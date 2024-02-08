Require Import Coq.FSets.FMapList.
Require Import Coq.FSets.FSetList.
Require Import Coq.Structures.OrderedType.
Require Import Coq.Structures.OrderedTypeEx.
Require Import String.
Require Import ZArith_base.

Module Import Loc_as_OT := PairOrderedType(String_as_OT)(Nat_as_OT).

Module Import MemMap := FMapList.Make(Loc_as_OT).

Module Import LocSet := FSetList.Make(Loc_as_OT).

Inductive value : Type :=
    | VInt (n: Z)
    | VPtr (l: Loc_as_OT.t).

Definition mem := MemMap.t value.

Module AExp.

Inductive aexp : Type :=
    | ANum (n: Z)
    | AId (l: Loc_as_OT.t)
    | APlus_Num (n1 n2: Z).

Definition undef_val := VInt (-1).

Definition aeval (a: aexp): value :=
    match a with
    | ANum n => VInt n
    | AId l => VPtr l
    | APlus_Num n1 n2 => VInt (n1 + n2)
    end.

Definition beval (a: aexp): bool :=
    match a with
    | ANum n => match n with
                | Z0 => false
                | _ => true
                end
    | AId l => false
    | APlus_Num n1 n2 => match n1, n2 with
                        | Z0, Z0 => false
                        | _, _ => true
                        end
    end.

End AExp.

Module AEvalR.
Import AExp.

Inductive aevalR: aexp -> value -> Prop :=
    | E_ANum (n: Z): aevalR (ANum n) (VInt n)
    | E_AId (l: Loc_as_OT.t): aevalR (AId l) (VPtr l)
    | E_APlus_Num (n1 n2: Z):
        aevalR (APlus_Num n1 n2) (VInt (n1 + n2)).


Notation "e 'eval_to' n" := (aevalR e n) (at level 90, left associativity): type_scope.

End AEvalR.

Theorem aeval_iff_aevalR: forall a v,
    AEvalR.aevalR a v <-> AExp.aeval a = v.
Proof.
    intros a v. split; intros H.
    - induction H; reflexivity.
    - destruct a; simpl in H; rewrite <- H; constructor.
Qed.