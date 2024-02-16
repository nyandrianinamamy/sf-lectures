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


(* Fixpoint aeval (st: state) (a: aexp): option value :=
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
    end. *)

Reserved Notation
         "st '={' a '}=>' value"
         (at level 40, a constr,
          st constr, value constr at next level).

Inductive aevalR: state -> aexp -> option value -> Prop :=
    | E_ANum (n: Z): 
        forall st, st ={ n }=> (Some (VInt n))
    | E_AAddr_Def (x: string) (v: value):
        forall st l, 
        find_instance st x = l ->   
        st ={ AAddr x }=> Some (VPtr l)
    | E_AId_Def (x: string) (v: value):
        forall st l, 
        find_instance st x = l ->   
        MemMap.find l st = Some v -> 
        st ={ AId x }=> (Some v)
    | E_APlus_Num (a1 a2: aexp) (n1 n2: Z):
        forall st, 
        st ={ a1 }=> (Some (VInt n1)) -> 
        st ={ a2 }=> (Some (VInt n2)) -> 
        st ={ <{ a1 + a2 }> }=> Some (VInt (n1 + n2))
    | E_APlus_Undef_Left (a1 a2: aexp):
        forall st, 
        st ={ a1 }=> None ->
        st ={ <{ a1 + a2 }> }=> None
    | E_APlus_Undef_Right (a1 a2: aexp):
        forall st,
        st ={ a2 }=> None -> 
        st ={ <{ a1 + a2 }> }=> None
where "state '={' aexp '}=>' value" := (aevalR state aexp value) : type_scope.

(* Fixpoint beval (st: state) (b: bexp): bool :=
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
    end.  *)

(* We chose None to differentiate normal termination and out of gas (when adding loops later) *)
(* Fixpoint ceval (st: state) (c: com): option state :=
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
    | CAlloc x mu => let l := fresh st mu in
                        match l with
                            | Some mu_ptr => 
                                Some (find_instance st x !-> (VPtr mu_ptr); mu_ptr !-> def_init; st)
                            | None => None
                        end
    end. *)

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
        forall (st:state) x l aexp v,
        st ={ AAddr x }=> Some (VPtr l) ->
        st ={ aexp }=> Some v ->
        st =[ CAsgn x aexp ]=> Some (l !-> v; st)
    | E_Asgn_Undef: 
        forall st x aexp,
        st ={ aexp }=> None ->
        st =[ CAsgn x aexp ]=> None
        (* TODO: 0 as default value ? *)
    | E_Alloc_Success: 
        forall st x l mu mu_ptr,
        fresh_spec st mu (Some mu_ptr) ->
        st ={ AAddr x }=> Some (VPtr l) ->
        st =[ CAlloc x mu ]=> Some (l !-> (VPtr mu_ptr); mu_ptr !-> def_init; st)
    | E_Alloc_Fail:
        forall st x mu,
        fresh_spec st mu None ->
        st =[ CAlloc x mu ]=> None
where "st '=[' c ']=>' st'" := (cevalR c st st') : type_scope.   


(* Read and Written memory locations *)
(* Fixpoint upsilon (st: state) (a: aexp): locset :=
    match a with
    | ANum n => LocSet.empty
    | AId l => LocSet.singleton (l)
    | <{ a1 + a2 }> => LocSet.union (upsilon st a1) (upsilon st a2)
    end. *)

Inductive upsilonR: state -> aexp -> locset -> Prop :=
    | E_Ups_Num: 
        forall st n, upsilonR st (ANum n) LocSet.empty
    | E_Ups_Addr:
        forall st x,
        upsilonR st (AAddr x) LocSet.empty
    | E_Ups_Id: 
        forall st x l, 
        st ={ AAddr x }=> Some (VPtr l) ->
        upsilonR st (AId x) (LocSet.singleton l)
    | E_Ups_Plus: 
        forall st a1 a2 l1 l2,
        upsilonR st a1 l1 -> upsilonR st a2 l2 -> upsilonR st <{ a1 + a2 }> (LocSet.union l1 l2).

(* TODO: Fail if CAlloc because unsound ? *)
(* Fixpoint write (st: state) (c: com) : locset :=
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
          *)
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

(* Fixpoint read (st: state) (c: com) : locset :=
    match c with
    | CSkip => LocSet.empty
    | CSeq c1 c2 =>
        match ceval st c1 with
        | Some st' => LocSet.union (read st c1) (read st' c2)
        | None => LocSet.empty
        end
    | CAsgn (x) (a) => upsilon st a 
    | CAlloc (x) (mu) => LocSet.empty
    end. *)

Inductive readR: state -> com -> state -> locset -> Prop :=
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
    | E_Write_CAsgn st st' x a:
        st =[ x := a ]=> (Some st') -> 
        writeR st <{ x := a }> st' (LocSet.singleton (find_instance st x)) 
    | E_Write_CSeq I1 M1 O1 c1 c2 W1 W2:
        I1 =[ c1 ]=> (Some M1)->
        writeR I1 c1 M1 W1 ->
        M1 =[ c2 ]=> (Some O1) ->
        writeR M1 c2 O1 W2 ->
        writeR I1 <{ c1 ; c2 }> O1 (LocSet.union W1 W2).



Inductive RW: state -> com -> state -> locset -> locset -> Prop :=
    | E_RW_CSkip:
        forall st,
        RW st CSkip st (LocSet.empty) (LocSet.empty)
    | E_RW_CSeq I1 M1 O1 c1 c2 R1 R2 W1 W2:
        I1 =[ c1 ]=> (Some M1)->
        RW I1 c1 M1 R1 W1 ->
        M1 =[ c2 ]=> (Some O1) ->
        RW M1 c2 O1 R2 W2 ->
        RW I1 <{ c1 ; c2 }> O1 (LocSet.union R1 R2) (LocSet.union W1 W2).

        

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

Definition find (v:MemMap.key) (st:MemMap.t value) := MemMap.find v st.

Lemma LocSet_neg_union_1:
    forall w W1 W2,
    LocSet.mem w W1 = false /\ LocSet.mem w W2 = false <-> (LocSet.mem w (LocSet.union W1 W2) = false).
Proof.
    intros *.
    rewrite FSetFact.union_b.
    split; try auto.
    - intros [H1 H2].
        rewrite H1. rewrite H2. easy.
    - intros H.
        destruct (LocSet.mem w W1) eqn: H1; destruct (LocSet.mem w W2) eqn: H2; try easy.
Qed.


(* Proof by uniqueness of k ?  *)
Lemma MemMap_not_find:
    forall k l v (m: MemMap.t value),
    LocSet.mem k (LocSet.singleton l) = false -> MemMap.find k (l !-> v; m) = MemMap.find k m.
Proof.
Admitted.


Lemma LocSet_union_1:
    forall l1 l2 l3,
    LocSet.In l1 l2 -> LocSet.In l1 (LocSet.union l2 l3).
Proof.
    intros * H_in_l1.
    apply FSetFact.union_iff. left. easy.
Qed.


Lemma S_uses_only_R:
    forall c R W I1 I2 O1 O2,
    I2 =[ c ]=> (Some O2) ->
    readR I1 c O1 R ->
    writeR I1 c O1 W ->
    (forall r, LocSet.In r R -> find r I1 = find r I2) ->
    (forall w, (LocSet.In w W -> find w O1 = find w O2) /\ (LocSet.mem w W = false -> find w O1 = find w I1 /\ find w O2 = find w I2)).
Proof.
    intros c.
    induction c.
    (* Skip *)
    - intros * Hceval Hread Hwrite H_same_reads.
        inversion Hceval. subst.
        inversion Hread. subst.
        inversion Hwrite. subst.
        intros w. split.
        + easy.
        + intros H_not_in_W. inversion H. subst. easy.

    (* Seq *)
    - intros * Hceval Hread Hwrite H_same_reads.
        inversion Hceval as [|? M2|?|?|?|?]. subst.
        inversion Hread. inversion Hwrite. subst.
        assert (HM1: M0 = M1). admit. subst. clear H12. clear H15.


        assert (H_W1_not_W1: forall w, (LocSet.In w W1 -> find w M1 = find w M2) /\ (LocSet.mem w W1 = false -> find w M1 = find w I1 /\ find w M2 = find w I2)).
        {
            apply IHc1 with (I1:=I1) (O1:=M1) (I2:=I2) (O2:=M2) (R:=R1) (W:=W1); try easy.
            intros r. specialize (H_same_reads r). intros H_in_R1. apply H_same_reads. rewrite FSetFact.union_iff. left. easy.
        }

        assert (H_R2: forall r, LocSet.In r R2 -> find r I1 = find r I2). {
            intros r. intros H_in_R2.
            apply H_same_reads. rewrite FSetFact.union_iff. right. easy.
        }

        assert (H_same_middle: forall r, LocSet.In r R2 -> find r M1 = find r M2). {
            intros r. intros H_in_R2.
            destruct (LocSet.mem r W1) eqn: H_mem; specialize (H_W1_not_W1 r); destruct H_W1_not_W1 as [H_W1 H_not_W1].
            --  apply H_W1. apply FSetFact.mem_iff. easy.
            --  specialize (H_R2 r). apply H_not_W1 in H_mem. destruct H_mem. apply H_R2 in H_in_R2.
                rewrite H_in_R2 in H1.
                apply transitivity with (x:=find r M1) (y:=find r I2) (z:=find r M2); try easy.            
        }

        assert (H_W2_not_W2: forall w, (LocSet.In w W2 -> find w O1 = find w O2) /\ (LocSet.mem w W2 = false -> find w O1 = find w M1 /\ find w O2 = find w M2)).
        {
            apply IHc2 with (I1:=M1) (O1:=O1) (I2:=M2) (O2:=O2) (R:=R2) (W:=W2); try easy.
        }

        intros w.

        split.

        2: {
            intros H_not_in_W1_W2.
            rewrite <- LocSet_neg_union_1 in H_not_in_W1_W2.
            destruct H_not_in_W1_W2 as [H_not_in_W1 H_not_in_W2].
            destruct H_W1_not_W1 with (w:=w) as [H_W1 H_not_W1].
            apply H_not_W1 in H_not_in_W1.
            destruct H_W2_not_W2 with (w:=w) as [H_W2 H_not_W2].
            apply H_not_W2 in H_not_in_W2.
            destruct H_not_in_W1. destruct H_not_in_W2.
            rewrite H1 in H5. rewrite H2 in H7.
            split; try easy.
        }

        intros H_in_W1_W2.

        rewrite FSetFact.union_iff in H_in_W1_W2.

        destruct H_in_W1_W2 as [H_in_W1 | H_in_W2].

        -- destruct (LocSet.mem w W2) eqn: H_mem.
            ++ apply IHc2 with (I1:=M1) (O1:=O1) (I2:=M2) (O2:=O2) (R:=R2) (W:=W2); try easy. rewrite <- FSetFact.mem_iff in H_mem. easy.
            ++ destruct H_W1_not_W1 with (w:=w) as [H_W1 H_not_W1].
               destruct H_W2_not_W2 with (w:=w) as [H_W2 H_not_W2]. 
                apply H_W1 in H_in_W1. apply H_not_W2 in H_mem.
                destruct H_mem. rewrite H1. rewrite H2. easy.
        
        -- destruct (LocSet.mem w W1) eqn: H_mem ; 
            destruct H_W2_not_W2 with (w:=w) as [H_W2 H_not_W2];
            apply H_W2 in H_in_W2; easy.


    (* Asgn *)
    - intros * Hceval Hread Hwrite H_same_reads.
        induction a as [n | y | ? | y mu].
        + inversion Hceval. inversion Hread. inversion Hwrite. subst.  clear H17.
          inversion H11. subst. unfold find_instance in *.
          inversion H8. subst. inversion H3. subst. unfold find_instance in *.
          inversion H5. subst. unfold find_instance in *.
          inversion H6. subst. inversion H4. subst.

          intros w. split.
          * intros H_in_W. apply LocSet_singleton_iff in H_in_W. subst.
            rewrite MemMap_find_1. rewrite MemMap_find_1. easy.
          * intros H_not_in_W. unfold find. split.
            -- apply MemMap_not_find with (k:=w) (l:=(x,0)) (v:=VInt n) (m:=I1). easy.
            -- apply MemMap_not_find with (k:=w) (l:=(x,0)) (v:=VInt n) (m:=I2). easy. 
        + inversion Hceval. inversion Hread. inversion Hwrite. subst.  clear H17.
          inversion H11. subst. unfold find_instance in *.
          inversion H8. subst. inversion H3. subst. unfold find_instance in *.
          inversion H4. subst. inversion H7. subst. unfold find_instance in *.
          inversion H6. subst. unfold find_instance in *.
          inversion H1. subst. unfold find_instance in *.

          specialize (H_same_reads (y,0)).
          intros w. split.
            * intros H_in_W.

Admitted.
