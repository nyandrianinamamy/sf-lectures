(* Global import *)
Require Coq.MSets.MSetList.
Require Import BinInt.
Require Import Coq.Strings.String.


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

Definition ceval (st: state) (c: com): option state :=
    match c with 
    | CSkip => Some st
    | CAsgn x a => match aeval st a with
                    | Some v => Some (find_instance st x !-> v; st)
                    | None => None
                end
    (* TODO: 0 as default value ? *)
    | CAlloc x mu => let l := fresh st mu in
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
    | E_Asgn_Int: 
        forall st x aexp n,
        st ={ aexp }=> Some (VInt n) ->
        st =[ CAsgn x aexp ]=> Some (find_instance st x !-> (VInt n); st)
    | E_Asgn_Ptr: 
        forall st x aexp loc,
        st ={ aexp }=> Some (VPtr loc) ->
        st =[ CAsgn x aexp ]=> Some (find_instance st x !-> (VPtr loc); st)
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
Definition write (st: state) (c: com) : locset :=
    match c with
    | <{ skip }> => LocSet.empty
    | <{ x := a }> => LocSet.singleton (find_instance st x) 
    | <{ x := alloc mu }> => LocSet.singleton (find_instance st x) 
    end.
         
Inductive writeR: state -> com -> locset -> Prop :=
    | E_Write_CSkip: 
        forall st,
        writeR st <{ skip }> LocSet.empty
    | E_Write_CAsn:
        forall st x a,
        writeR st <{ x := a }> (LocSet.singleton (find_instance st x))
    | E_Write_CAlloc:
        forall st x mu,
        writeR st <{ x := alloc mu }> (LocSet.singleton (find_instance st x)).

Definition read (st: state) (c: com) : locset :=
    match c with
    | CSkip => LocSet.empty
    | CAsgn (x) (a) => upsilon st a 
    | CAlloc (x) (mu) => LocSet.empty
    end.

Inductive readR: state -> com -> locset -> Prop :=
    | E_Read_CSkip: 
        forall st,
        readR st CSkip LocSet.empty
    | E_Read_CAsn:
        forall st x a l,
        upsilonR st a l ->
        readR st <{ x := a }> l
    | E_Read_CAlloc:
        forall st x mu,
        readR st <{ x := alloc mu }> LocSet.empty.

(* Projection on locsets *)
Definition proj (st: state) (locs: locset): state :=
    MemMap.fold (
        fun k v acc => 
        if (LocSet.mem k locs) 
        then MemMap.add k v acc 
        else acc
    ) st empty_state.
        
Inductive projR: state -> locset -> state -> Prop :=
    | E_Proj_Empty: 
        forall st, projR st LocSet.empty empty_state
    | E_Proj_Add: 
        forall st locs k v acc,
        (LocSet.mem k locs) = true ->
        (MemMap.mem k st) = true ->
        projR st locs (MemMap.add k v acc)
    | E_Proj_NoAdd: 
        forall st locs k acc,
        LocSet.mem k locs = false ->
        projR st locs acc.

Require Coq.FSets.FSetFacts.

Lemma LocSet_mem_1 : 
    forall l,
     LocSet.mem l (LocSet.singleton l) = true.
Proof.
    intros. apply LocSet.MF.mem_iff. rewrite LocSet.MF.singleton_iff. easy. 
Qed.

Lemma MemMap_mem_1_old : 
    forall (k: MemMap.key) (v: value) m,
     MemMap.mem k (MemMap.add k v m) = true.
Proof.
    intros. rewrite MemMap.mem_1; try easy.
Admitted.

Require Import Coq.FSets.FMapFacts.

Module Import P := WProperties_fun Loc_as_OT MemMap.
Module Import F := P.F.

Print Module F.


Lemma MemMap_mem_add: 
    forall (k: MemMap.key) (v: value) (m: MemMap.t value),
     MemMap.mem k (MemMap.add k v m) = true.
Proof.
    intros *.
    rewrite F.mem_find_b. 
    rewrite F.add_eq_o. easy. destruct k. easy.
Qed.


Lemma proj_empty: 
    forall st, 
        projR st LocSet.empty empty_state.
Proof.
    intros. apply E_Proj_Empty.
Qed.


Lemma proj_singleton: forall st l v,
    projR (l !-> v; st) (LocSet.singleton l) (l !-> v; empty_state).
Proof.
    intros *. apply E_Proj_Add. apply LocSet_mem_1. apply MemMap_mem_add.
Qed.

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
    intros * Hc Ha Hceval1 Hceval2 Hreads. subst. unfold ceval in *. unfold aeval in *. 
    injection Hceval1 as Hceval1. injection Hceval2 as Hceval2. unfold find_instance in *. 
    subst. unfold read in *. unfold upsilon in *. unfold write in *. unfold LocSet.For_all. intros.
    unfold find_instance in *. rewrite LocSet.MF.singleton_iff in H. destruct H as [HL HR]. destruct x0. simpl in *. subst.
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
    intros * Hc Ha Hst1 Hst2 Hceval1 Hceval2 Hreads. subst. unfold read in *. unfold upsilon in *. unfold write in *. unfold find_instance in *.
    unfold ceval in *. unfold aeval in *. unfold find_instance in *. rewrite Hst1 in Hceval1. rewrite Hst2 in Hceval2. injection Hceval1 as Hceval1. injection Hceval2 as Hceval2.
    subst.
    unfold LocSet.For_all in *. intros. rewrite LocSet.MF.singleton_iff in H. destruct H as [HL HR]. destruct x0. simpl in *. subst.
    rewrite ?MemMap_mem_add. easy.
Qed. 

            
