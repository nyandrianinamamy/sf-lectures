(* Global import *)
Require Coq.MSets.MSetList.
Require Import BinInt.
Require Import Coq.Strings.String.
Require Import Coq.FSets.FMapFacts.
Require Import Coq.FSets.FSetFacts.


(* Local import *)
Require Import SEM.State.
Require Import SEM.Syntax.
Require Import SEM.Notation.
Require Import SEM.Util.

Import AExp.
Import BExp.
Import Com.


Fixpoint aeval (st: state) (a: aexp): option value :=
    match a with
    | ANum n => Some (VInt n)
    | AId x => match (MemMap.find x st) with
                | Some v => Some v
                | None => None
                end
    | <{ a1 + a2 }> => match (aeval st a1, aeval st a2) with
                    | (Some (VInt n1), Some (VInt n2)) => Some (VInt (n1 + n2))
                    | _ => None
                    end 
    end.

Reserved Notation
         "st '={' a '}=>' value"
         (at level 40, a constr,
          st constr, value constr at next level).

Inductive aevalR: state -> aexp -> option value -> Prop :=
    | E_ANum (n: Z): 
        forall st, st ={ n }=> (Some (VInt n))
    | E_AId_Def (l: loc) (v: value):
        forall st, MemMap.find l st = Some v -> st ={ AId l }=> (Some v)
    | E_AId_Undef (l: loc):
        forall st, MemMap.find l st = None -> st ={ AId l }=> None
    | E_APlus_Num (a1 a2: aexp) (n1 n2: Z):
        forall st, 
        st ={ a1 }=> (Some (VInt n1)) -> 
        st ={ a2 }=> (Some (VInt n2)) -> 
        st ={ <{ a1 + a2 }> }=> Some (VInt (n1 + n2))
    | E_APlus_Undef (a1 a2: aexp):
        forall st, 
        st ={ a1 }=> None -> 
        st ={ a2 }=> None -> 
        st ={ <{ a1 + a2 }> }=> None
where "state '={' aexp '}=>' value" := (aevalR state aexp value) : type_scope.

Fixpoint beval (st: state) (b: bexp): bool :=
    match b with
    | <{true}> => true
    | <{false}> => false
    | <{a1 = a2}> => match (aeval st a1, aeval st a2) with
                    | (Some (VInt n1), Some (VInt n2)) => Z.leb n1 n2
                    | _ => false
                end
    | <{a1 <= a2}> => match (aeval st a1, aeval st a2) with
                    | (Some (VInt n1), Some (VInt n2)) => Z.eqb n1 n2
                    | _ => false
                end
    | <{~b1}> => negb (beval st b1)
    end. 

(* We chose None to differentiate normal termination and out of gas (when adding loops later) *)
Fixpoint ceval (st: state) (c: com): option state :=
    match c with 
    | CSkip => Some st
    | CSeq c1 c2 => match ceval st c1 with
                        | Some st' => ceval st' c2
                        | None => None
                    end
    | CAsgn x a => match aeval st a with
                        | Some v => Some ((find_instance st x) !-> v; st)
                        | None => None
                    end
    (* TODO: 0 as default value ? *)
    | CAlloc x mu =>let l := fresh st mu in
                        match l with
                            | Some mu_ptr => 
                                Some (find_instance st x !-> (VPtr mu_ptr); mu_ptr !-> def_init; st)
                            | None => None
                        end
    end.

Reserved Notation
         "st '=[' c ']=>' st'"
         (at level 40, c custom com at level 99,
          st constr, st' constr at next level).

Inductive cevalR: com -> state -> option state -> Prop :=
    | E_Skip: 
        forall st, st =[ CSkip ]=> Some st
    | E_Seq:
        forall st st' st'' c1 c2,
        st =[ c1 ]=> Some st' ->
        st' =[ c2 ]=> st'' ->
        st =[ CSeq c1 c2 ]=> st''
    | E_Asgn: 
        forall (st:state) x aexp v,
        st ={ aexp }=> Some v ->
        st =[ CAsgn x aexp ]=> Some (find_instance st x !-> v; st)
    (* | E_Asgn_Ptr: 
        forall st x aexp loc,
        st ={ aexp }=> Some (VPtr loc) ->
        st =[ CAsgn x aexp ]=> Some (find_instance st x !-> (VPtr loc); st) *)
    | E_Asgn_Undef: 
        forall st x aexp,
        st ={ aexp }=> None ->
        st =[ CAsgn x aexp ]=> None
        (* TODO: 0 as default value ? *)
    | E_Alloc_Success: 
        forall st x mu mu_ptr,
        fresh_spec st mu (Some mu_ptr) ->
        st =[ CAlloc x mu ]=> Some (find_instance st x !-> (VPtr mu_ptr); mu_ptr !-> def_init; st)
    | E_Alloc_Fail:
        forall st x mu,
        fresh_spec st mu None ->
        st =[ CAlloc x mu ]=> None
where "st '=[' c ']=>' st'" := (cevalR c st st') : type_scope.   


(* Read and Written memory locations *)
Fixpoint upsilon (st: state) (a: aexp): locset :=
    match a with
    | ANum n => LocSet.empty
    | AId l => LocSet.singleton (l)
    | <{ a1 + a2 }> => LocSet.union (upsilon st a1) (upsilon st a2)
    end.

Inductive upsilonR: state -> aexp -> locset -> Prop :=
    | E_Ups_Num: 
        forall st n, upsilonR st (ANum n) LocSet.empty
    | E_Ups_Id: 
        forall st l, upsilonR st (AId l) (LocSet.singleton l)
    | E_Ups_Plus: 
        forall st a1 a2 l1 l2,
        upsilonR st a1 l1 -> upsilonR st a2 l2 -> upsilonR st <{ a1 + a2 }> (LocSet.union l1 l2).

(* TODO: Fail if CAlloc because unsound ? *)
Fixpoint write (st: state) (c: com) : locset :=
    match c with
    | <{ skip }> => LocSet.empty
    | <{ c1 ; c2 }> => 
        match ceval st c1 with
        | Some st' => LocSet.union (write st c1) (write st' c2)
        | None => LocSet.empty
        end
    | <{ x := a }> => LocSet.singleton (find_instance st x) 
    | <{ x := alloc mu }> => LocSet.singleton (find_instance st x) 
    end.
         
(* Inductive writeR: state -> com -> locset -> Prop :=
    | E_Write_CSkip: 
        forall st,
        writeR st <{ skip }> LocSet.empty
    | E_Write_CSeq:
        forall st st' c1 c2 l1 l2,
        writeR st c1 l1 ->
        st =[ c1 ]=> Some st' ->
        writeR st' c2 (LocSet.union l1 l2) -> 
        writeR st <{ c1 ; c2 }> (LocSet.union l1 l2)
    | E_Write_CAsn:
        forall st x a,
        writeR st <{ x := a }> (LocSet.singleton (find_instance st x))
    | E_Write_CAlloc:
        forall st x mu,
        writeR st <{ x := alloc mu }> (LocSet.singleton (find_instance st x)). *)

Fixpoint read (st: state) (c: com) : locset :=
    match c with
    | CSkip => LocSet.empty
    | CSeq c1 c2 =>
        match ceval st c1 with
        | Some st' => LocSet.union (read st c1) (read st' c2)
        | None => LocSet.empty
        end
    | CAsgn (x) (a) => upsilon st a 
    | CAlloc (x) (mu) => LocSet.empty
    end.

Inductive readR: state -> com -> state ->locset -> Prop :=
    | E_Read_CSkip:
        forall st st',
        st =[ skip ]=> (Some st') ->
        readR st CSkip st' (LocSet.empty)
    | E_Read_CAsgn:
        forall st st' x a l,
        st =[ x := a ]=> (Some st') ->
        upsilonR st a l ->
        readR st <{ x := a }> st' l
    | E_Read_CSeq I1 M1 O1 c1 c2 R1 R2:
        I1 =[ c1 ]=> (Some M1) ->
        readR I1 c1 M1 R1 ->
        M1 =[ c2 ]=> (Some O1) ->
        readR M1 c2 O1 R2 ->
        readR I1 <{ c1 ; c2 }> O1 (LocSet.union R1 R2).

Inductive writeR: state -> com -> state -> locset -> Prop :=
    | E_Write_CSkip st st':
        st =[ skip ]=> (Some st') -> 
        writeR st CSkip st' (LocSet.empty)
    | E_Write_CAsgn st st' l x a:
        st =[ x := a ]=> (Some st') -> 
        writeR st <{ x := a }> st' (LocSet.add (find_instance st x) l) 
    | E_Write_CSeq I1 M1 O1 c1 c2 W1 W2:
        I1 =[ c1 ]=> (Some M1)->
        writeR I1 c1 M1 W1 ->
        M1 =[ c2 ]=> (Some O1) ->
        writeR M1 c2 O1 W2 ->
        writeR I1 <{ c1 ; c2 }> O1 (LocSet.union W1 W2).


(* Inductive RW: state -> com -> locset -> locset -> Prop :=
    | E_RW_CSkip:
        forall st,
        RW st CSkip (LocSet.empty) (LocSet.empty)
    | E_RW_CAsgn:
        forall st x a l,
        upsilonR st a l ->
        RW st <{ x := a }> l (LocSet.singleton (find_instance st x))
    | E_RW_CSeq st st' st'' c1 c2 r r1 r2 diff_r2_w1 w1 w2:
        RW st c1 r1 w1 ->
        cevalR c1 st (Some st') ->
        RW st' c2 r2 w2 ->
        cevalR c2 st' (Some st'') ->
        LocSet.Equal (LocSet.diff r2 w1) diff_r2_w1 ->
        LocSet.Equal (LocSet.union r1 diff_r2_w1) r ->
        RW st <{ c1 ; c2 }> r w2. *)

        

(* Definition init_state := (W, 0) !-> VInt 10; _ !-> value.
Definition end_state := (W, 0) !-> VInt 10; (W, 0) !-> VInt 10; _ !-> value.
Definition empty_set := LocSet.empty.
Example test_readR_skip: 
    forall st, 
    RW st <{ skip }> empty_set empty_set.
Proof.
    intros *.
    apply E_RW_CSkip.
Admitted.


Example test_readR_seq_skip: 
    forall st,
    RW st <{ skip ; skip }> empty_set empty_set.
Proof.
    intros *.
    apply E_RW_CSeq with (st:=st) (st':=st) (st'':=st) (r1:=empty_set) (r2:=empty_set) 
    (diff_r2_w1:=empty_set) (w1:=empty_set) (w2:=empty_set); 
    try easy; 
    try apply E_RW_CSkip; 
    try apply E_Skip.
Admitted.

Definition ten: Z := 10.

Example test_readR_seq_asgn: 
    forall st st' x y,
    RW st <{ x := ANum ten }> empty_set (LocSet.singleton (X, 0)) ->
    RW st' <{ y := AId (X,0) }> (LocSet.singleton (X, 0)) (LocSet.singleton (Y, 0)) ->
    RW st <{ x := ANum ten ; y := AId (X,0) }> empty_set (LocSet.singleton(Y, 0)).
Proof.
    intros * Heval1 Heval2.
    eapply E_RW_CSeq.
Admitted. *)

Lemma LocSet_mem_1 : 
    forall l,
     LocSet.mem l (LocSet.singleton l) = true.
Proof.
    intros. apply LocSet.MF.mem_iff. rewrite LocSet.MF.singleton_iff. easy. 
Qed.

Lemma MemMap_mem_add: 
    forall (k: MemMap.key) (v: value) (m: MemMap.t value),
     MemMap.mem k (MemMap.add k v m) = true.
Proof.
    intros *.
    rewrite FMapFact.mem_find_b. 
    rewrite FMapFact.add_eq_o. easy. destruct k. easy.
Qed.

(* Relational RW *)

Lemma MemMap_find_1:
    forall (k: MemMap.key) (v: value) (m: MemMap.t value),
     MemMap.find (elt:=value) k (k !-> v; m) = Some v.
Proof.
    destruct k. intros. 
    apply FMapFact.add_eq_o. easy.
Qed.

Lemma LocSet_singleton_iff:
    forall l l',
    LocSet.In l (LocSet.singleton l') <-> l = l'.
Proof.
    intros *.
    destruct l; destruct l'; split; intros H;
    rewrite FSetFact.singleton_iff in *; 
    destruct H; simpl in *; 
    subst; easy.
Qed.

Lemma cevalR_det: forall c st1 st2 st,
    st =[ <{ c }> ]=> Some st1 ->
    st =[ <{ c }> ]=> Some st2 ->
    st1 = st2.
Proof.
Admitted.
    

Definition ten: Z := 10.

Example test_readR_writeR_seq_asgn: 
    forall x y R,
    let st := empty_state in
    let st'' := ((Y,0) !-> VInt 10; ((X,0) !-> VInt 10; empty_state)) in
    readR st <{ x := ANum ten ; y := AId (X,0) }> st'' R ->
    LocSet.Equal R (LocSet.singleton (X, 0)).
Proof.
    intros * Hread.
    inversion Hread. subst.
    inversion H2. inversion H9. subst.
    inversion H7. subst. inversion H11. subst. easy.
Qed.


Definition find (v:MemMap.key) (st:MemMap.t value) := MemMap.find v st.


Lemma no_change_outside_W:
    forall c (I O: state) (W: locset),
    writeR I c O W ->
    (forall w, ~LocSet.In w W -> find w O = find w I).
Proof.
Admitted.


Lemma LocSet_union_1:
    forall l1 l2 l3,
    LocSet.In l1 l2 -> LocSet.In l1 (LocSet.union l2 l3).
Proof.
    intros * H_in_l1.
    apply FSetFact.union_iff. left. easy.
Qed.

Lemma LocSet_neg_union_1:
    forall w W1 W2,
    ~LocSet.In w W1 /\ ~LocSet.In w W2 <-> ~ LocSet.In w (LocSet.union W1 W2).
Proof.
Admitted.


Lemma LocSet_union_non_disjoint:
    forall l1 l2 l3,
    LocSet.In l1 (LocSet.union l2 l3) <-> 
    ((LocSet.In l1 l2 /\ LocSet.In l1 l3) \/
    (LocSet.In l1 l2 /\ ~LocSet.In l1 l3) \/
    (~LocSet.In l1 l2 /\ LocSet.In l1 l3)).
Proof.
Admitted.


Lemma S_uses_only_R:
    forall c (I1 O1 I2 O2: state) (R W: locset),
    cevalR c I2 (Some O2) ->
    readR I1 c O1 R ->
    writeR I1 c O1 W ->
    (forall r, LocSet.In r R -> find r I1 = find r I2) ->
    (forall w, (LocSet.In w W -> find w O1 = find w O2) /\ (~LocSet.In w W -> find w O1 = find w I1 /\ find w O2 = find w I2)).
Proof.
    intros c.
    (* remember c as c' eqn: Hc. *)
    induction c.
    (* Skip *)
    -  intros * Hceval Hread Hwrite H_same_reads.
        inversion Hceval. inversion Hread. inversion Hwrite. subst.
        intros w.
        split.
        * intros H_in_w. easy.
        * intros H_not_in_w. split; try easy. apply no_change_outside_W with (c:=<{ skip }>) (W:= LocSet.empty); try easy.


    (* Seq *)
    - intros * Hceval Hread Hwrite.
        inversion Hceval as [|? M2|?|?|?|?]. inversion Hread. inversion Hwrite. subst.
        assert (HM1: M0 = M1). admit. subst. clear H19. clear H16.

        intros H_same_reads. intros w.

        (* Do not depend on r2 M2 *)
        assert (H_W_M1_M2: forall w, LocSet.In w W1 -> find w M1 = find w M2). {
            intros * H_in_W1.
            apply IHc1 with (I1:=I1) (O1:=M1) (I2:=I2) (O2:=M2) (R:=R1) (W:=W1); try easy.
            intros r. specialize (H_same_reads r). intros H_in_R1. apply H_same_reads. rewrite FSetFact.union_iff. left. easy.
        }

        (* Do not depend on r2 M2 *)
        assert (H_W1_not_W2_M1_M2: forall w, LocSet.In w W1 /\ ~ LocSet.In w W2 -> find w M1 = find w M2). {
            intros.
            apply H_W_M1_M2. easy.
        }
    

        (* I1 = M1 /\ I2 = M2 /\ I1 = I2  *)
(* 
        assert (H_not_W1: forall r, LocSet.In r R2 -> ~ LocSet.In r W1 -> find r M1 = find r I1 /\ find r M2 = find r I2). admit.
        assert (H_W1: forall r, LocSet.In r R2 -> LocSet.In r W1 -> find r M1 = find r M2). admit. *)

        assert (H_R2_not_W1: forall r, ~LocSet.In w W1 /\ LocSet.In r R2 -> find r M1 = find r M2). {
            admit.
        }

        assert (H_R2_W1: forall r, LocSet.In w W1 /\ LocSet.In r R2 -> find r M1 = find r M2). {
            admit.
        }

        assert (H_not_W1_W2: ~ LocSet.In w W1 /\ LocSet.In w W2 -> find w O1 = find w O2). {
            intros.
            destruct H1.
            apply IHc2 with (I1:=M1) (O1:=O1) (I2:=M2) (O2:=O2) (R:=R2) (W:=W2); try easy.
            intros r.
            intro H_in_R2. 
            apply H_R2_not_W1; try easy.
        }

        assert (H_W1_not_W2_O1_M1: LocSet.In w W1 /\ ~ LocSet.In w W2 -> find w O1 = find w M1 /\ find w O2 = find w M2). {
            intros H3.
            destruct H3.
            apply IHc2 with (I1:=M1) (O1:=O1) (I2:=M2) (O2:=O2) (R:=R2) (W:=W2); try easy.
            intros r.
            intro H_in_R2.
            apply H_R2_W1; try easy.
        }

        assert (H_W1_not_W2:
        ((find w M1 = find w M2) /\ (find w O1 = find w M1) /\ (find w O2 = find w M2))  ->
        find w O1 = find w O2). {
            intros H3.
            destruct H3.
            destruct H2.
            rewrite H1 in H2.
            apply transitivity with (x:=find w O1) (y:=find w M2) (z:=find w O2); try easy.
        }



        split.

(* In W1 U W2 *)
        *  
        intros H_in_W.
            rewrite LocSet_union_non_disjoint in H_in_W.
            destruct H_in_W.
            -- destruct H1. apply IHc2 with (I1:=M1) (O1:=O1) (I2:=M2) (O2:=O2) (R:=R2) (W:=W2); try easy.
                intros r.
                intro H_in_R2.
                apply H_R2_W1; try easy.
            -- destruct H1.
                ++ apply H_W1_not_W2.
                   split.
                    ** apply H_W1_not_W2_M1_M2. easy.
                    ** apply H_W1_not_W2_O1_M1. easy.
                ++ apply H_not_W1_W2. easy.
                (* ++ apply H_not_W1_W2; try easy. *)
(* 
        * intros H_not_in_W. rewrite <- LocSet_neg_union_1 in H_not_in_W.
            assert (H_not_W1: ~LocSet.In w W1 /\ ~LocSet.In w W2 -> find w O1 = find w I1). admit.
            assert (H_not_W2: ~LocSet.In w W1 /\ ~LocSet.In w W2 -> find w O2 = find w I2). admit.
            split.
            -- apply H_not_W1. easy.
            -- apply H_not_W2. easy. *)

(* 

        assert (H_W1: LocSet.In w W1 -> find w O1 = find w O2).
        {
            intros H_in_W1.
            admit.
        }
        assert (H_W2: LocSet.In w W2 -> find w O1 = find w O2). admit.



        (* w in W1 U W2  or w notin*)
        split.
        * intros H_in_W. rewrite FSetFact.union_iff in H_in_W. destruct H_in_W as [H_in_W1 | H_in_W2].
            -- apply H_W1. easy.
            -- apply H_W2. easy.
        *  *)

        


            

    



(* assert (H_EQ_O1_O2: forall w, 
LocSet.In w W1 -> 
    (LocSet.In w R1 -> (LocSet.In w W1 -> find w M1 = find w M2) \/ (~LocSet.In w W1 -> find w M1 = find w M2)) 
    \/ 
    (LocSet.In w R2 -> (LocSet.In w W2 -> find w O1 = find w O2) \/ (~LocSet.In w W2 -> find w O1 = find w O2))
). admit. *)
            
    (* apply H_EQ_O1_O2.  *)

           
        
            


        (* specialize IHc1 with (I1:=I1) (O1:=M1) (I2:=I2) (O2:=M2) (R:=R1) (W:=W1) as IHc1'. *)
(* 
        assert (H_R1_W1_M1_M2: forall w, (LocSet.In w W1 -> find w M1 = find w M2) /\ (~LocSet.In w W1 -> find w M1 = find w I1 /\ find w M2 = find w I2)). {
            apply IHc1 with (R:=R1); try easy.
            intros r. specialize (H_same_reads r). intros H_in_R1. apply H_same_reads. rewrite FSetFact.union_iff. left. easy.
        }

        assert (H_R2_W2_O1_O2: forall w, (LocSet.In w W2 -> find w O1 = find w O2) /\ (~LocSet.In w W2 -> find w O1 = find w M1 /\ find w O2 = find w M2)). {
            apply IHc2 with (R:=R2); try easy.
            intros r. specialize (H_same_reads r). intros H_in_R2. apply H_R1_W1_M1_M2.
            admit.
        }

        assert (HQ: forall r, (LocSet.In r R2 -> (LocSet.In r W1 -> find r M1 = find r M2) /\ (~LocSet.In r W1 -> find r M1 = find r I1 /\ find r I2 = find r M2 /\ find r I1 = find r I2))). {
            intros r H_in_R2.
            split.
            * admit.
            * intros H_not_in_W1. split.
            (* r notin W1 *)
              -- admit.
              -- split.
                 (* I2 = M2 on r *)
                ++ admit.
                (* I1 = I2 on r  *)
                ++ apply H_same_reads. rewrite FSetFact.union_iff. right. easy.
        }


        assert (HR: forall r, (LocSet.In r R2 -> (LocSet.In r W2 -> find r O1 = find r O2) /\ (~LocSet.In r W2 -> find r O1 = find r M1 /\ find r O2 = find r M2 /\ find r M1 = find r M2))). { 
            intros r H_in_R2.
            split; try easy.
            - apply H_R2_W2_O1_O2.
            - intros H_not_in_W2. split.
                + apply H_R2_W2_O1_O2; try easy.
                + split.
                   * apply H_R2_W2_O1_O2; try easy.
                   * apply 
        }

        split.
        * intros H_in_W. rewrite FSetFact.union_iff in H_in_W. destruct H_in_W as [H_in_W1 | H_in_W2].
            -- 
           *)



        (* intros H_same_r w. split.
        * intros H_in_w.
          apply FSetFact.union_iff in H_in_r.
          apply FSetFact.union_iff in H_in_w.
          

        * intros H_not_in_w.
          admit. *)

        (* inversion Hceval. inversion Hread. inversion Hwrite. subst.

        assert (Hst1: st'0 = st'1). admit. subst. clear H19.

        assert (H_r1_w1: forall r, LocSet.In r r1 -> MemMap.find r st1 = MemMap.find r st2 -> forall w, LocSet.In w w1-> MemMap.find w st1' = MemMap.find w st2'). {   
            admit.
        }
        
        assert (H_r2_w2: forall r, LocSet.In r r2 -> MemMap.find r st1 = MemMap.find r st2 -> forall w, LocSet.In w w2 -> MemMap.find w st1' = MemMap.find w st2'). {
            admit.
        }

        assert (H_r1_w2: forall r, LocSet.In r r1 -> MemMap.find r st1 = MemMap.find r st2 -> forall w, LocSet.In w w2 -> MemMap.find w st1' = MemMap.find w st2'). {
            admit.
        }

        assert (H_r2_w1: forall r, LocSet.In r r2 -> MemMap.find r st1 = MemMap.find r st2 -> forall w, LocSet.In w w1 -> MemMap.find w st1' = MemMap.find w st2'). {
            admit.
        }

        intros * H_in_r H_same_r w H_in_w.

        rewrite FSetFact.union_iff in *.
        
        destruct H_in_r as [H_in_R1 | H_in_R2];  destruct H_in_w as [H_in_W1 | H_in_W2].
        (* r in R1 *) (* w in W1 *)
        * apply H_r1_w1 with (r:=r); try easy.
            
        (* r in R1 *) (* w in W2 *)
        * apply H_r1_w2 with (r:=r); try easy.

        (* r in R2 *) (* w in W1 *) 
        * apply H_r2_w1 with (r:=r); try easy.

        (* r in R2 *) (* w in W2 *)
        * apply H_r2_w2 with (r:=r); try easy. *)
Admitted.
        
        (* * specialize IHc1 with (st1:=st1) (st2:=st2) (st1':=st'1) (st2':=st'2) (R:=l1) (W:=l4) as IHc1'.
          specialize IHc2 with (st1:=st'1) (st2:=st'2) (st1':= st1') (st2':=st2') (R:=l2) (W:=l7) as IHc2'. *)



      

       
      
    
    (* intros * Hread1 Hread2 Hwrite1 Hwrite2 H_eq_R H_eq_W H_eq_on_R.
      inversion Hread1. inversion Hread2. inversion Hwrite1. inversion Hwrite2. subst.


      assert (Hst1: st' = st'1). apply cevalR_det with (c:=c1) (st:=st1) (st1:=st') (st2:=st'1); easy. subst. clear H19. clear H22. 
      assert (Hst2: st'0 = st'2). apply cevalR_det with (c:=c1) (st:=st2) (st1:=st'0) (st2:=st'2); easy. subst. clear H28. clear H31.
         

      assert (Hw: forall w, LocSet.In w (LocSet.union l4 l6) -> MemMap.find w st'1 = MemMap.find w st'2). admit.
        
      specialize (IHc2 st'1 st'2 st1' st2' l2 l3 (LocSet.union l4 l5) l7) as IHc2'.
      apply IHc2'; try easy. *)
      


(* Theorem rw_eval:
forall c st1 st1' st2 st2' reads writes,
RW st1 c reads writes ->
cevalR c st1 (Some st1') ->
cevalR c st2 (Some st2') ->
(forall r, LocSet.In r reads -> MemMap.find r st1 = MemMap.find r st2) ->
(forall w, LocSet.In w writes -> MemMap.find w st1' = MemMap.find w st2').
Proof.
    intros c.
    induction c; intros * Hrw Hceval1 Hceval2 Hsamereads;  try easy.
    - inversion Hceval1. inversion Hceval2. inversion Hrw. subst.
      intros l. easy.
    - inversion Hceval1. inversion Hceval2. inversion Hrw. subst.

      assert (Hst1: st' = st'1). apply cevalR_det with (c:=c1) (st:=st1) (st1:=st') (st2:=st'1); easy. subst. clear H14.
      assert (Hst1: st1' = st''1). apply cevalR_det with (c:=c2) (st:=st'1) (st1:=st1') (st2:=st''1); easy. subst. clear H16.
         

      assert (Hst1': forall w , LocSet.In w writes -> MemMap.find w st'1 = MemMap.find w st'0). admit.



      specialize (IHc2 st'1 st''1 st'0 st2' r2 writes) as IHC2'.
      specialize (IHc1 st1 st'1 st2 st'0 r1 w1) as IHc1'.
       (* admit. *)

    - inversion Hceval1. inversion Hceval2. inversion Hrw. subst.
        unfold find_instance in *.
        induction a; try easy.
        (* a = n *)
        * inversion H14. subst. inversion H2. subst. inversion H7. subst.
            intros l. intro Hinl. rewrite LocSet_singleton_iff in Hinl. subst.
            rewrite MemMap_find_1. rewrite MemMap_find_1. easy.
        (* a = l *)
        * inversion H14. subst. inversion H2. subst. inversion H7. subst.
            specialize (Hsamereads l).
            intros l0. intro Hinl0. rewrite LocSet_singleton_iff in Hinl0. subst.
            rewrite MemMap_find_1. rewrite MemMap_find_1.
            rewrite LocSet_singleton_iff in Hsamereads.  *)

            
      (* specialize (IHc1 st1 st'1 st2 st'0 r1).
      specialize (IHc2 st'1 st''1 st'0 st2'). *)

      (* apply IHc2 with(reads:=r2); try easy.
      apply IHc1 with(writes:=r2); try easy.
      * admit.
      * assert (Hr1: LocSet.Subset r1 reads). admit. (* Follows from H21*)
        intros l Hl. apply Hsamereads. apply Hr1. easy. *)

      (* apply IHc2; try easy. *)

      (* apply IHc2; try easy. assert (Hr2: r2 = diff_r2_w1). {
         
       } 
    rewrite Hr2 in H15. apply H15. *)
      
    (* induction Hrw; try easy.
    - inversion Hceval1. inversion Hceval2. subst. unfold find_instance in *.
      intros Hsamereads. inversion H. subst; try easy.
        * inversion H8. subst. inversion H3. subst. *)
(* Admitted. *)


