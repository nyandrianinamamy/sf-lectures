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
    | <{ c1 ; c2 }> => LocSet.union (write st c1) (write st c2)
    | <{ x := a }> => LocSet.singleton (find_instance st x) 
    | <{ x := alloc mu }> => LocSet.singleton (find_instance st x) 
    end.
         
Inductive writeR: state -> com -> locset -> Prop :=
    | E_Write_CSkip: 
        forall st,
        writeR st <{ skip }> LocSet.empty
    | E_Write_CSeq:
        forall st c1 c2 l1 l2,
        writeR st c1 l1 -> 
        writeR st c2 l2 -> 
        writeR st <{ c1 ; c2 }> (LocSet.union l1 l2)
    | E_Write_CAsn:
        forall st x a,
        writeR st <{ x := a }> (LocSet.singleton (find_instance st x))
    | E_Write_CAlloc:
        forall st x mu,
        writeR st <{ x := alloc mu }> (LocSet.singleton (find_instance st x)).

Fixpoint read (st: state) (c: com) : locset :=
    match c with
    | CSkip => LocSet.empty
    | CSeq c1 c2 => LocSet.union (read st c1) (read st c2)
    | CAsgn (x) (a) => upsilon st a 
    | CAlloc (x) (mu) => LocSet.empty
    end.

Inductive readR: state -> com -> locset -> Prop :=
    | E_Read_CSkip: 
        forall st,
        readR st CSkip LocSet.empty
    | E_Read_CSeq:
        forall st c1 c2 l1 l2,
        readR st c1 l1 -> 
        readR st c2 l2 -> 
        readR st <{ c1 ; c2 }> (LocSet.union l1 l2)
    | E_Read_CAsn:
        forall st x a l,
        upsilonR st a l ->
        readR st <{ x := a }> l
    | E_Read_CAlloc:
        forall st x mu,
        readR st <{ x := alloc mu }> LocSet.empty.


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

(* Computational rw *)
(* For reuse *)
Definition rw_template (c: com) (st1 st1' st2 st2': state) : Prop :=
    ceval st1 c = Some st1' ->
    ceval st2 c = Some st2' ->
    LocSet.For_all (fun l => MemMap.mem l st1 = MemMap.mem l st2) (read st1 c) ->
    LocSet.For_all (fun l => MemMap.mem l st1' = MemMap.mem l st2') (write st1 c).

(* skip *)
Lemma rw_skip:
    forall st1 st1' st2 st2',
    rw_template CSkip st1 st1' st2 st2'.
Proof.
    intros * Hc Hceval1 Hceval2 Hreads. subst.
    unfold LocSet.For_all. intros. easy.
Qed.

(* x := n *)
Lemma rw_asgn_int:
    forall c n x  a st1 st1' st2 st2',
    c = (CAsgn x a) ->
    a = ANum n ->
    rw_template c st1 st1' st2 st2'.

Proof.
    intros * Hc Ha Hceval1 Hceval2 Hreads. 
    subst. unfold ceval in *. unfold aeval in *. unfold read in *. unfold upsilon in *. unfold write in *. unfold find_instance in *.
    injection Hceval1 as Hceval1. injection Hceval2 as Hceval2.
    subst.  
    unfold LocSet.For_all in *. intros.
    unfold find_instance in *. apply FSetFact.singleton_iff in H. destruct x0. simpl in *. destruct H. subst.
    rewrite ?MemMap_mem_add. easy.
Qed.

(* x := l *)
Lemma rw_asgn_loc:
    forall c x a l v st1 st1' st2 st2',
    c = (CAsgn x a) ->
    a = AId l ->
    MemMap.find l st1 = Some v ->
    MemMap.find l st2 = Some v ->
    rw_template c st1 st1' st2 st2'.
Proof.
    intros * Hc Ha Hst1 Hst2 Hceval1 Hceval2 Hreads. 
    subst. unfold ceval in *. unfold aeval in *. unfold read in *. unfold upsilon in *. unfold write in *. unfold find_instance in *.
    rewrite Hst1 in *. rewrite Hst2 in *.
    injection Hceval1 as Hceval1. injection Hceval2 as Hceval2.
    subst.
    unfold LocSet.For_all in *. intros. 
    apply FSetFact.singleton_iff in H. destruct x0. simpl in *. destruct H. subst.
    rewrite ?MemMap_mem_add. easy.
Qed. 

(* c1; c2 *)
Lemma rw_seq_skip_skip:
    forall c1 c2 st1 st1' st2 st2',
    c1 = CSkip ->
    c2 = CSkip ->
    rw_template (CSeq c1 c2) st1 st1' st2 st2'.
Proof.
    intros * Hc1 Hc2 Hceval1 Hceval2 Hreads. subst. easy.
Qed.

Lemma rw_seq_skip_c2:
    forall c1 c2 st1 st1' st2 st2',
    c1 = CSkip ->
    rw_template (CSeq c1 c2) st1 st1' st2 st2'.
Proof.
    intros * Hc1 Hceval1 Hceval2 Hreads. subst. simpl in *.
Abort.
(* End computational rw *)

(* Relational RW *)

Print FSetFact. 


Lemma rw_skipR:
    forall st1 st1' st2 st2' reads writes,
    st1 =[ CSkip ]=> Some st1' ->
    st2 =[ CSkip ]=> Some st2' ->
    readR st1 CSkip reads ->
    writeR st1 CSkip writes ->
    (forall l, LocSet.In l reads -> MemMap.find l st1 = MemMap.find l st2) ->
    (forall l, LocSet.In l writes -> MemMap.find l st1' = MemMap.find l st2').
Proof.
    intros * Hceval1 Hceval2 Hreads Hwrites Hsamereads.
    inversion Hceval1. inversion Hceval2. subst.
    inversion Hreads. inversion Hwrites. subst.
    intros.
    specialize (Hsamereads l H). 
    apply Hsamereads.
Qed.


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

(* x := n *)
Lemma rw_asgnR:
    forall st1 st1' st2 st2' reads writes x a,
    st1 =[ <{ x:=a }> ]=> Some st1' ->
    st2 =[ <{ x:=a }> ]=> Some st2' ->
    readR st1 (<{ x:=a }>) reads ->
    writeR st1 (<{ x:=a }>) writes ->
    (forall l, LocSet.In l reads -> MemMap.find l st1 = MemMap.find l st2) ->
    (forall l, LocSet.In l writes -> MemMap.find l st1' = MemMap.find l st2').
Proof.
    intros * Hceval1 Hceval2 Hreads Hwrites Hsamereads.
    inversion Hceval1. inversion Hceval2. subst.
    destruct a.
    (* x := n *)
    - inversion Hreads. inversion H4. subst.
        inversion Hwrites. unfold find_instance in *. subst.
        clear H4. inversion H2. subst. inversion H7. subst.
        intros. destruct l. apply LocSet_singleton_iff in H. rewrite H.
        rewrite ?MemMap_find_1. 
        easy.
    (* x := l *)

    (* x := a + b*)
Admitted.

Lemma rw_allocR:
    forall st1 st1' st2 st2' reads writes x mu,
    st1 =[ <{ x:= alloc mu }> ]=> Some st1' ->
    st2 =[ <{ x:= alloc mu }> ]=> Some st2' ->
    readR st1 (<{ x:= alloc mu }>) reads ->
    writeR st1 (<{ x:= alloc mu }>) writes ->
    (forall l, LocSet.In l reads -> MemMap.find l st1 = MemMap.find l st2) ->
    (forall l, LocSet.In l writes -> MemMap.find l st1' = MemMap.find l st2').
Proof.
Admitted.


(* c1; c2 *)
Lemma rw_seqR:
    forall st1 st1' st2 st2' reads writes c1 c2,
    st1 =[ <{ c1; c2 }> ]=> Some st1' ->
    st2 =[ <{ c1; c2 }> ]=> Some st2' ->
    readR st1 <{ c1; c2 }> reads ->
    writeR st1 <{ c1; c2 }> writes ->
    (forall l, LocSet.In l reads -> MemMap.find l st1 = MemMap.find l st2) ->
    (forall l, LocSet.In l writes -> MemMap.find l st1' = MemMap.find l st2').
Proof.
    intros * Hceval1 Hceval2 Hreads Hwrites Hsamereads.
    induction Hceval1; simpl in *.
    - inversion Hwrites. subst. inversion Hreads. subst. intros. easy.
    - inversion Hwrites. subst. inversion Hreads. subst. intros.   
Admitted.


Lemma rw_total:
    forall c (st2 st2' st1 st1': state) reads writes,
    st1 =[ <{ c }> ]=> Some st1' ->
    st2 =[ <{ c }> ]=> Some st2' ->
    readR st1 <{ c }> reads ->
    writeR st1 <{ c }> writes ->
    (forall l, LocSet.In l reads -> MemMap.find l st1 = MemMap.find l st2) ->
    (forall l, LocSet.In l writes -> MemMap.find l st1' = MemMap.find l st2').
Proof.
    intros c.
    induction c; intros * Hceval1 Hceval2 Hreads Hwrites Hsamereads.

    (* Skip *)
    - apply rw_skipR with (st1:=st1') (st1':=st1') (st2:=st2') (st2':=st2') (reads:=reads).
        * apply E_Skip.
        * apply E_Skip.
        * inversion Hreads. apply E_Read_CSkip.
        * inversion Hwrites. apply E_Write_CSkip.
        * inversion Hreads. subst. easy.

    (* Sequence *)
    - inversion Hceval1. inversion Hceval2. subst. inversion Hreads. inversion Hwrites. subst.

        assert (Hmid_write_l0: forall l, LocSet.In l l0 -> MemMap.find l st' = MemMap.find l st'0).
        {intros. apply IHc1 with (st1:=st1) (st1':=st') (st2:=st2) (st2':=st'0) (reads:=l1) (writes:=l0).
            - apply H1.
            - apply H7.
            - apply H3.
            - apply H12.
            - intros. specialize (Hsamereads l4). apply Hsamereads. apply LocSet.union_2. easy.
            - apply H.
        }

        assert (Hmid_read_l2: forall l, LocSet.In l l2 -> MemMap.find l st' = MemMap.find l st'0).
        admit.

        assert (Hmid_read_l1: forall l, LocSet.In l l1 -> MemMap.find l st1 = MemMap.find l st2).
        admit.
        
        assert (Hmid_write_l3: forall l, LocSet.In l l3 -> MemMap.find l st1' = MemMap.find l st2').
        {intros. apply IHc2 with (st1:=st') (st1':=st1') (st2:=st'0) (st2':=st2') (reads:=l2) (writes:=l3).
        - apply H4.
        - apply H10.
        - assert (readR st' c2 l2 = readR st1 c2 l2). admit. rewrite H0. apply H6.
        - assert (writeR st' c2 l3 = writeR st1 c2 l3). admit. rewrite H0. apply H14.
        - intros. specialize (Hmid_read_l2 l4). apply Hmid_read_l2. apply H0.
        - apply H.
        }

        assert (Hmid_not_touch: forall l, ~(LocSet.In l l3) -> MemMap.find l st1' = MemMap.find l st2').
        admit.

        intros. 
        apply LocSet.union_1 in H. destruct H.
          * specialize (Hmid_write_l0 l). 
          assert (Excl: ~(LocSet.In l l3)). { admit. }
            apply Hmid_not_touch. apply Excl.
        * specialize (Hmid_write_l3 l). apply Hmid_write_l3. easy.
 

       
        



    (* intros c.
    induction c; intros * Hceval1 Hceval2 Hreads Hwrites Hsamereads; inversion Hceval1; inversion Hceval2; subst; auto.
    (* Skip *)
    - apply rw_skipR with (st1:=st1') (st1':=st1') (st2:=st2') (st2':=st2') (reads:=reads); auto.
    (* Assignment *)
    -  *)
    
    
    (* Allocation *)
    (* Seq *)



(* intros * Hceval1 Hceval2 Hreads Hwrites Hsamereads.
(* x := l *)
- inversion Hreads. inversion H5. subst.
    inversion Hwrites. unfold find_instance in *. subst.
    clear H5. inversion H2. subst. inversion H3. subst.
    specialize (Hsamereads l). clear H2 H3 Hceval1 Hceval2 Hwrites.
    assert (HP: LocSet.In l (LocSet.singleton l)). { apply FSetFact.singleton_iff. easy. }
    apply Hsamereads in HP.
    assert (HV: v = v0). { 
    apply
    
}
    subst.
    intros. apply FSetFact.singleton_iff in H. destruct l0. simpl in *. destruct H. subst.
    rewrite ?MemMap_mem_add. easy.
    *)
    

        
    
      

    
    
    