From Coq Require Export String.

Module Loc.
Definition t: Type := string.
Definition eqb (l1 l2: string): bool :=
    String.eqb l1 l2.

Theorem eqb_eq: forall (l1 l2: string), eqb l1 l2 = true <-> l1 = l2.
Proof.
    intros l1 l2. split.
    - intros H. apply String.eqb_eq. apply H.
    - intros H. rewrite H. apply String.eqb_refl.
Qed.

Theorem eqb_refl : forall (l: string), eqb l l = true.
Proof.
    intros l. apply String.eqb_refl.
Qed.
End Loc.

Definition loc := Loc.t.

Definition var : Type := string.

Inductive value : Type :=
| VLoc (l: loc)
| VNat (n: nat).

Inductive expr : Type :=
    | Const (c: nat)
    | Addr (x: var)
    | Lval (l: lval)
with lval : Type :=
| Deref (e: expr).

Inductive stmt : Type :=
    | Skip
    | Assign (x: var) (e: expr)
    | Alloc (x: var) (mu: nat).

Inductive partial_map : Type :=
 | Empty
 | Binding (k: loc) (v: value) (m: partial_map).

Fixpoint lookup_var (x: var) (m: partial_map): option value :=
match m with
| Empty => None
| Binding k' v m' => if Loc.eqb x k' then Some v else lookup_var x m'
end.

Fixpoint lookup (k: loc) (m: partial_map): option value :=
match m with
| Empty => None
| Binding k' v m' => if Loc.eqb k k' then Some v else lookup k m'
end.

Fixpoint update (m: partial_map) (k: loc) (v: value): partial_map :=
match m with
| Empty => Binding k v Empty
| Binding k' v' m' => if Loc.eqb k k' then Binding k v m' else Binding k' v' (update m' k v)
end.

Fixpoint eval_expr (E: expr) (I: partial_map): option value :=
match E with
| Const n => Some (VNat n)
| Addr x => match lookup_var x I with
            | Some l => Some l
            | None => None
            end
| Lval (Deref e) => match eval_expr e I with
                    | Some (VLoc l) => match lookup l I with
                                | Some v => Some v
                                | None => None
                                end
                    | _ => None
                    end
end.

Definition eval_stmt (S: stmt) (I: partial_map): partial_map :=
match S with 
| Skip => I
| Assign x e => match eval_expr e I with
                | Some v => match lookup_var x I with
                            | Some l' => match l' with 
                                        | VLoc l'' => update I l'' v
                                        | _ => I
                                        end
                            | None => update I x v
                            end
                | _ => I
                end
| _ => I
end.

Theorem update_eq : forall (m: partial_map) (k: loc) (v: value),
    update m k v = Binding k v m.
Proof.
Admitted.

Theorem lookup_empty: forall (k: loc),
    lookup k Empty = None.
Proof. reflexivity. Qed.

Theorem lookup_k: forall (m: partial_map) (k: loc) (v: value),
    lookup k (Binding k v m) = Some v.
Proof.
    intros. simpl. rewrite Loc.eqb_refl. reflexivity.
Qed.

Theorem lookup_update_eq: forall (m: partial_map) (k: loc) (v: value),
    lookup k (update m k v) = Some v.
Proof.
    intros. rewrite update_eq. rewrite lookup_k. reflexivity.
Qed.

Definition empty_map: partial_map := Empty.

Definition x: string := "x".

Example test_eval_expr_1:
    eval_expr (Const 42) empty_map = Some (VNat 42).
Proof. reflexivity. Qed.

Example test_eval_stmt_1:
    eval_stmt (Assign x (Const 42)) empty_map = Binding x (VNat 42) Empty.
Proof. reflexivity. Qed.

Theorem eval_stmt_eq : forall (S: stmt) (I1 I2: partial_map),
    I1 = I2 -> eval_stmt S I1 = eval_stmt S I2.
Proof.
    intros. rewrite H. reflexivity.
Qed.

Require Import Ensembles.

Definition set_var := Ensemble var.

Definition write_var (S: stmt) (I: partial_map) : set_var :=
match S with
| Skip => Empty_set var
| Assign x e => Singleton var x
| Alloc x mu => Empty_set var
end.

Theorem write_var_eq : forall (S: stmt) (I1 I2: partial_map),
    I1 = I2 -> write_var S I1 = write_var S I2.
Proof.
    intros. rewrite H. reflexivity.
Qed.

Definition upsilon (E: expr) (I: partial_map) : set_var :=
match E with
| Const n => Empty_set var
| Addr x => Empty_set var
| Lval (Deref e) => match eval_expr e I with
                    | Some (VLoc l) => Singleton var l
                    | _ => Empty_set var
                    end
end.

Definition read_var (S: stmt) (I: partial_map) : set_var :=
match S with
| Skip => Empty_set var
| Assign x e => upsilon e I
| Alloc x mu => Empty_set var
end.

Theorem read_var_eq : forall (S: stmt) (I1 I2: partial_map),
    I1 = I2 -> read_var S I1 = read_var S I2.
Proof.
    intros. rewrite H. reflexivity.
Qed.

Theorem read_write_var_eq : forall (S: stmt) (I1 I2: partial_map),
    read_var S I1 = read_var S I2 -> write_var S I1 = write_var S I2.
Proof.
    intros. destruct S.
    - reflexivity.
    - try reflexivity.
    - try reflexivity.
Qed.





