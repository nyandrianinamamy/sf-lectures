Require Coq.FSets.FMapList.
Require Coq.FSets.FSetList.
Require Import Coq.FSets.FSetFacts.
Require Import Coq.Structures.OrderedType.
Require Import Coq.Structures.OrderedTypeEx.
Require Import String.
Require Import BinInt.

Module Import Loc_as_OT := PairOrderedType(String_as_OT)(Nat_as_OT).

Module Import MemMap := FMapList.Make(Loc_as_OT).

Module Import LocSet := FSetList.Make(Loc_as_OT).

Definition loc := Loc_as_OT.t.
Definition locset := LocSet.t.
Definition var := string.


Definition x_loc (x:string) : loc := (x, 0).

Inductive value : Type :=
    | VInt (n: Z)
    | VPtr (l: loc).

Definition mem := MemMap.t value.

Definition cmp_value (v1 v2: value) : Prop :=
    match (v1, v2) with
    | (VInt n1, VInt n2) => Z.eq n1 n2
    | (VPtr l1, VPtr l2) => Loc_as_OT.eq l1 l2
    | _ => False
    end.

Module AExp.

Inductive aexp : Type :=
    | ANum (n: Z)
    | AId (l: loc)
    | APlus (a1 a2: aexp).

Inductive bexp : Type :=
    | BTrue
    | BFalse
    | BLe (a1 a2: aexp)
    | BEq (a1 a2: aexp)
    | BNot (b: bexp).

End AExp.

(* Module AEval_no_state.
Import AExp.



Fixpoint aeval (a: aexp): value :=
    match a with
    | ANum n => VInt n
    | AId l => VPtr l
    | APlus n1 n2 => match (aeval n1, aeval n2) with
                    | (VInt n1, VInt n2) => VInt (n1 + n2)
                    | _ => undef_val
                    end
    end.

Fixpoint beval (b: bexp): bool :=
    match b with
    | BTrue => true
    | BFalse => false
    | BLe a1 a2 => match (aeval a1, aeval a2) with
                    | (VInt n1, VInt n2) => Z.leb n1 n2
                    | _ => false
                    end
    | BEq a1 a2 => match (aeval a1, aeval a2) with
                    | (VInt n1, VInt n2) => Z.eqb n1 n2
                    | _ => false
                    end
    | BNot b1 => negb (beval b1)
end.

End AEval_no_state.



Module AEvalR.
Import AExp.
Import AEval_no_state.


Notation "e 'eval_to' n" := (aevalR e n) (at level 90, left associativity): type_scope.

(* Theorem aeval_iff_aevalR: forall a v,
    aevalR a v <-> aeval a = v.
Proof.
    intros a v. split; intros H.
    - induction H; reflexivity.
    - destruct a; simpl in H; rewrite <- H; constructor.
Abort. *)

End AEvalR. *)

Import AExp.

(* Notations *)

Definition W : string := "W".
Definition X : string := "X".
Definition Y : string := "Y".


Coercion AId : loc >-> aexp.
Coercion ANum : Z >-> aexp.

Declare Custom Entry com.
Declare Scope com_scope.

Notation "<{ e }>" := e (at level 0, e custom com at level 99) : com_scope.
Notation "( x )" := x (in custom com, x at level 99) : com_scope.
Notation "x" := x (in custom com at level 0, x constr at level 0) : com_scope.
Notation "f x .. y" := (.. (f x) .. y)
                  (in custom com at level 0, only parsing,
                  f constr at level 0, x constr at level 9,
                  y constr at level 9) : com_scope.
Notation "x + y"   := (APlus x y) (in custom com at level 50, left associativity).
Notation "'true'"  := true (at level 1).
Notation "'true'" := BTrue (in custom com at level 0).
Notation "'false'" := false (at level 1).
Notation "'false'" := BFalse (in custom com at level 0).
Notation "x <= y"  := (BLe x y) (in custom com at level 70, no associativity).
Notation "x = y"   := (BEq x y) (in custom com at level 70, no associativity).
Notation "'~' b"   := (BNot b) (in custom com at level 75, right associativity).

Notation "'_' '!->' v" := (MemMap.empty v)
  (at level 100, right associativity).

Notation "x '!->' v ';' m" := (MemMap.add x v m)
                              (at level 100, v at next level, right associativity).

Open Scope com_scope.

Definition state := MemMap.t value.

Definition undef_val := VInt (-1).

Definition add_value (v1 v2: value) : value :=
    match (v1, v2) with
    | (VInt n1, VInt n2) => VInt (n1 + n2)
    | _ => undef_val
    end.

Inductive com : Type :=
    | CSkip
    | CAsgn (x:string) (a: aexp)
    | CAlloc (x:string) (mu: string).

Fixpoint aeval (st: state) (a: aexp): value :=
    match a with
    | ANum n => VInt n
    | AId x => match (MemMap.find x st) with
                | Some v => v
                | None => undef_val
                end
    | <{ a1 + a2 }> => add_value (aeval st a1) (aeval st a2)
    end.

Inductive aevalR: aexp -> value -> Prop :=
    | E_ANum (n: Z): aevalR (ANum n) (VInt n)
    | E_AId (l: loc): aevalR (AId l) (VPtr l)
    | E_APlus_Num (a1 a2: aexp) (n1 n2: Z):
        aevalR a1 (VInt n1) ->
        aevalR a2 (VInt n2) ->
        aevalR (APlus a1 a2) (VInt (n1 + n2)).

Fixpoint beval (st: state) (b: bexp): bool :=
    match b with
    | <{true}> => true
    | <{false}> => false
    | <{a1 = a2}> => match (aeval st a1, aeval st a2) with
                    | (VInt n1, VInt n2) => Z.leb n1 n2
                    | _ => false
                end
    | <{a1 <= a2}> => match (aeval st a1, aeval st a2) with
                    | (VInt n1, VInt n2) => Z.eqb n1 n2
                    | _ => false
                end
    | <{~b1}> => negb (beval st b1)
    end. 

Definition find_instance (st: state) (x: var): loc :=
    (x, 0).

Definition fresh (st: state) (mu: string): loc :=
    (mu, 0).

Definition ceval (st: state) (c: com): state :=
    match c with 
    | CSkip => st
    | CAsgn x a => let a' := aeval st a in
                   let l := find_instance st x in
                   MemMap.add l a' st
    | CAlloc x mu => let l := find_instance st x in
                        let mu_ptr := fresh st mu in
                        let mem' := MemMap.add l (VPtr (mu_ptr)) st in
                        MemMap.add mu_ptr undef_val mem' 
    end.

Inductive cevalR: com -> state -> state -> Prop :=
| E_Skip: forall st, cevalR CSkip st st
| E_Asgn: forall st a n x,
            aeval st a = n ->
            cevalR (CAsgn x a) st ((x_loc x) !-> n; st)
| E_Alloc: forall st x mu,
            let l := find_instance st x in
            let mu_ptr := fresh st mu in
            let mem' := MemMap.add l (VPtr (mu_ptr)) st in
            let st' := MemMap.add mu_ptr undef_val mem' in
            cevalR (CAlloc x mu) st st'.                


Definition empty_state: state := MemMap.empty value.

Definition proj (st: state) (locs: locset): state :=
    MemMap.fold (
        fun k v acc => 
        if (LocSet.mem k locs) 
        then MemMap.add k v acc 
        else acc
    ) st empty_state.

Example proj_1 : proj ((x_loc X) !-> VInt 1; (x_loc Y) !-> VInt 0; empty_state) (LocSet.singleton (x_loc X)) = ((x_loc X) !-> VInt 1; empty_state).
Proof.
    unfold proj. simpl. reflexivity.
Qed.


Require Coq.FSets.FSetFacts.
Require Coq.FSets.FMapFacts.

(* Search (MSet.mem _ MSet.empty). *)

(* Search "fold". *)

Lemma fold_empty: forall f (m: MemMap.t value),
    MemMap.fold f m (MemMap.empty value) = MemMap.empty value.
Proof.
Admitted.


Lemma proj_empty: forall st, (proj st LocSet.empty) = empty_state.
Proof.
    intros. unfold proj. unfold LocSet.empty. unfold LocSet.mem. unfold empty_state. simpl. rewrite fold_empty. reflexivity.
Qed.

Lemma proj_singleton : forall l v st, proj (l !-> v; st) (singleton l) = (l !-> v; empty_state).
Proof.
Admitted.


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
Abort.


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

            

