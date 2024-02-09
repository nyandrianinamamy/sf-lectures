(* Global import *)
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
         "st '={' aexp '}=>' value"
         (at level 40, aexp custom com at level 99,
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
    (* What about alloc failed ? *)
    | CAlloc x mu => let mu_ptr := fresh st mu in
                Some (find_instance st x !-> (VPtr mu_ptr); mu_ptr !-> def_init; st)
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
        (* What about alloc failed ? *)
    | E_Alloc: 
        forall st x mu,
        let mu_ptr := fresh st mu in
        st =[ CAlloc x mu ]=> Some (find_instance st x !-> (VPtr mu_ptr); mu_ptr !-> def_init; st)
where "st '=[' c ']=>' st'" := (cevalR c st st') : type_scope.   


(* Definition proj (st: state) (locs: locset): state :=
    MemMap.fold (
        fun k v acc => 
        if (LocSet.mem k locs) 
        then MemMap.add k v acc 
        else acc
    ) st empty_state. *)

(* Example proj_1 : proj ((x_loc X) !-> VInt 1; (x_loc Y) !-> VInt 0; empty_state) (LocSet.singleton (x_loc X)) = ((x_loc X) !-> VInt 1; empty_state).
Proof.
    unfold proj. simpl. reflexivity.
Qed. *)


(* Require Coq.FSets.FSetFacts.
Require Coq.FSets.FMapFacts. *)

(* Search (MSet.mem _ MSet.empty). *)

(* Search "fold". *)
(* 
Lemma fold_empty: forall f (m: MemMap.t value),
    MemMap.fold f m (MemMap.empty value) = MemMap.empty value.
Proof.
Admitted.


Lemma proj_empty: forall st, (proj st LocSet.empty) = empty_state.
Proof.
    intros. unfold proj. unfold LocSet.empty. unfold LocSet.mem. unfold empty_state. simpl. rewrite fold_empty. reflexivity.
Qed.

(* Lemma proj_singleton : forall l v st, proj (l !-> v; st) (singleton l) = (l !-> v; empty_state).
Proof.
Admitted. *)


Definition write_locs (c: com) (st: state): locset :=
    match c with
    | CSkip => LocSet.empty
    | CAsgn (x) _ => LocSet.singleton (x_loc x) 
    | CAlloc (x) (mu) => LocSet.singleton (x_loc x) 
    end.

Definition upsilon (a: aexp) (st: state): locset :=
    match a with
    | ANum n => LocSet.empty
    | AId l => LocSet.singleton (l)
    | APlus _ _ => LocSet.empty
    end.

Definition read_locs (c: com) (st: state): locset :=
    match c with
    | CSkip => LocSet.empty
    | CAsgn (x) (a) => upsilon a st 
    | CAlloc (x) (mu) => LocSet.empty
    end.


Lemma proj_CSkip: forall st1 st1' st2 st2',
    st1' = ceval st1 CSkip ->
    st2' = ceval st2 CSkip ->
    proj st1 (read_locs CSkip st1) = proj st2 (read_locs CSkip st2) ->
    proj st1' (write_locs CSkip st1) = proj st2' (write_locs CSkip st2).
Proof.
    intros * Hst1 Hst2 Hproj; simpl in *; subst. try easy.
Qed.

Lemma proj_CAsn: forall st1 st1' st2 st2' x a v,
    aeval st1 a = v ->
    aeval st2 a = v ->
    st1' = ceval st1 (CAsgn x a) ->
    st2' = ceval st2 (CAsgn x a) ->
    proj st1 (read_locs (CAsgn x a) st1) = proj st2 (read_locs (CAsgn x a) st2) ->
    proj st1' (write_locs (CAsgn x a) st1) = proj st2' (write_locs (CAsgn x a) st2).
Proof.
    intros * Haeval1 Haeval2 Hst1' Hst2' Hproj; simpl in *.
    rewrite Haeval1 in Hst1'. rewrite Haeval2 in Hst2'. unfold find_instance in *. unfold x_loc in *. rewrite Hst1'. rewrite Hst2'. rewrite proj_singleton. rewrite proj_singleton. reflexivity.
Qed.


Lemma proj_CAsn_1: forall st1 st1' st2 st2' x a,
    st1' = ceval st1 (CAsgn x a) ->
    st2' = ceval st2 (CAsgn x a) ->
    proj st1 (read_locs (CAsgn x a) st1) = proj st2 (read_locs (CAsgn x a) st2) ->
    proj st1' (write_locs (CAsgn x a) st1) = proj st2' (write_locs (CAsgn x a) st2).
Proof.
    intros * Hst1' Hst2' Hproj; simpl in *. unfold upsilon in *. destruct a; try easy.
    - simpl in *. unfold find_instance in *. unfold x_loc in *. subst. rewrite proj_singleton. rewrite proj_singleton. reflexivity.
    - simpl in *. unfold find_instance in *. unfold x_loc in *. subst. rewrite proj_singleton. rewrite proj_singleton. destruct (find l st1) eqn:Hfind1.
      * destruct (find l st2) eqn:Hfind2.
        -- assert (Hv: v = v0). admit. subst. reflexivity.
        -- 
Abort. *)


(* Theorem proj_all: forall c st1 st1' st2 st2' a v,
    aeval st1 a = v ->
    aeval st2 a = v ->
    st1' = ceval st1 c ->
    st2' = ceval st2 c ->
    proj st1 (read_locs c st1) = proj st2 (read_locs c st2) ->
    proj st1' (write_locs c st1) = proj st2' (write_locs c st2).
Proof.
    intros * Haeval1 Haeval2 Hst1' Hst2' Hproj; simpl in *.
    destruct c as [| x a' | x mu].
    - apply proj_CSkip; easy.
    -  *)





(* Theorem same_read_write_states: forall c st1 st1' st2 st2',
    st1' = ceval st1 c ->
    st2' = ceval st2 c ->
    proj st1 (read_locs c st1) = proj st2 (read_locs c st2) ->
    proj st1' (write_locs c st1) = proj st2' (write_locs c st2). *)


(* Theorem same_read_write_states: forall c st1 st1' st2 st2',
    st1' = ceval st1 c ->
    st2' = ceval st2 c ->
    proj st1 (read_locs c st1) = proj st2 (read_locs c st2) ->
    proj st1' (write_locs c st1) = proj st2' (write_locs c st2).
Proof.
    intros [] * Hst1 Hst2 Hproj; simpl in *; try easy.
    - unfold proj. simpl. unfold empty_state. rewrite fold_empty. rewrite fold_empty. reflexivity.
    - unfold find_instance in *. unfold x_loc. subst. rewrite proj_singleton. rewrite proj_singleton.
      destruct a; simpl. try easy.
       * unfold upsilon in Hproj. *)
     (* x := a *) 
    (* -  x := a 
    unfold find_instance.
        * destruct a.
            -- unfold aeval. unfold x_loc. rewrite proj_singleton. rewrite proj_singleton. reflexivity.
            -- unfold upsilon in Hproj. assert (Hl0: l0 = l). admit. subst. rewrite proj_singleton in Hproj. rewrite proj_singleton in Hproj. rewrite proj_singleton. rewrite proj_singleton. unfold x_loc.  *)
            (* rewrite Hst1 in Hproj. rewrite Hst2 in Hproj. rewrite proj_singleton. rewrite proj_singleton in Hproj. *)
                
               
                
(* 
Theorem same_read_write_states: forall c st1 st1' st2 st2' l reads1 writes1 reads2 writes2,
    st1' = ceval st1 c ->
    st2' = ceval st2 c ->
    reads1 = read_locs c st1 ->
    reads2 = read_locs c st2 ->
    writes1 = write_locs c st1 ->
    writes2 = write_locs c st2 ->
    reads1 = reads2 ->
    proj_rel l st1 st1' reads1 = proj_rel l st2 st2' reads2 ->
    proj_rel l st1 st1' writes1 = proj_rel l st2 st2' writes2.
Proof.
    intros * Hceval1 Hceval2 Hreads1 Hreads2 Hwrites1 Hwrites2 Hreads Hproj. subst.
    destruct c; simpl in *; try easy.
    - (* x := a *) unfold find_instance in *. destruct a.
        * simpl in *. unfold x_loc. unfold proj_rel in *. try auto 5. *)

            

