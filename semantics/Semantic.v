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

(* Inductive readR: state -> com -> locset -> Prop :=
    | E_Read_CSkip:
        forall st,
        readR st CSkip (LocSet.empty)
    | E_Read_CAsgn:
        forall st st' x a l,
        upsilonR st a l ->
        readR st <{ x := a }> l
    | E_Read_CSeq st st' st'' c1 c2 l l' l'':
        readR st c1 l1 ->
        ceval st c1 = Some st' ->
        readR st' c2 l2 ->
        let lu := LocSet.union(l1 l2) in
        readR st <{ c1 ; c2 }> .

Inductive writeR: state -> locset -> com -> state -> locset -> Prop :=
    | E_Write_CSkip st l:
        writeR st l CSkip st l
    | E_Write_CAsgn st st' l x a:
        st =[ x := a ]=> (Some st') -> 
        writeR st l <{ x := a }> st' (LocSet.add (find_instance st x) l) 
    | E_Write_CSeq st st' st'' c1 c2 l l' l'':
        writeR st l c1 st' l' ->
        writeR st' l' c2 st'' l'' ->
        writeR st l <{ c1 ; c2 }> st'' l''. *)


Inductive RW: state -> com -> locset -> locset -> Prop :=
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
        RW st <{ c1 ; c2 }> r w2.
        

Definition init_state := (W, 0) !-> VInt 10; _ !-> value.
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
Admitted.

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

Theorem rw_eval:
forall c st1 st1' st2 st2' reads writes,
RW st1 c reads writes ->
cevalR c st1 (Some st1') ->
cevalR c st2 (Some st2') ->
(forall l, LocSet.In l reads -> MemMap.find l st1 = MemMap.find l st2) ->
(forall l, LocSet.In l writes -> MemMap.find l st1' = MemMap.find l st2').
Proof.
    intros c.
    induction c; intros * Hrw Hceval1 Hceval2;  try easy.
    - inversion Hceval1. inversion Hceval2. inversion Hrw. subst.
      intros Hsamereads. intros l. easy.
    - inversion Hceval1. inversion Hceval2. inversion Hrw. subst.
      intros Hsamereads.

      assert (Hst1: st' = st'1). apply cevalR_det with (c:=c1) (st:=st1) (st1:=st') (st2:=st'1); easy. subst. clear H14.
      assert (Hst1: st1' = st''1). apply cevalR_det with (c:=c2) (st:=st'1) (st1:=st1') (st2:=st''1); easy. subst. clear H16.


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
Admitted.


