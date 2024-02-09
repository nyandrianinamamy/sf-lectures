From Coq Require Import Arith.Arith.
From Coq Require Import Bool.Bool.
Require Export Coq.Strings.String.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Lists.List.
Import ListNotations.
Set Default Goal Selector "!".

Definition total_map (A:Type) := string -> A.

Definition t_empty {A : Type} (v: A) : total_map A :=
    (fun _ => v).

Definition t_update {A: Type} (m: total_map A) (x: string) (v : A) :=
    fun x' => if String.eqb x x' then v else m x'.

Definition examplemap :=
    t_update (t_update (t_empty false) "foo" true) "bar" true.

Notation "'_' '!->' v" := (t_empty v)
    (at level 100, right associativity).

Example example_empty := (_ !-> false).

Notation "x  '!->' v ';' m" := (t_update m x v)
    (at level 100, v at next level, right associativity).

Definition examplemap' := 
    ( "bar" !-> true;
      "foo" !-> true;
       _ !-> false).

Lemma t_apply_empty : forall (A: Type) (x : string) (v : A),
    (_ !-> v) x = v.
Proof.
    intros. unfold t_empty. reflexivity.
Qed.

Lemma t_update_eq : forall (A : Type) (m: total_map A) x v,
    (x !-> v; m) x = v.
Proof.
    intros. unfold t_update. rewrite eqb_refl. reflexivity.
Qed.

Lemma t_update_neq : forall (A : Type) (m: total_map A) x1 x2 v,
    x1 <> x2 ->
    (x1 !-> v; m) x2 = m x2.
Proof.
    intros. unfold t_update. rewrite <- eqb_neq in H. rewrite H. reflexivity.
Qed.

Lemma t_update_shadow : forall (A : Type) (m: total_map A) v1 v2 x,
    (x !-> v2; x !-> v1; m) = (x !-> v2; m).
Proof.
    intros. unfold t_update. apply functional_extensionality. intros. destruct (eqb x x0) eqn:E.
    - reflexivity.
    - reflexivity.
Qed.

Lemma t_update_same : forall (A : Type) (m: total_map A) x,
    (x !-> m x; m) = m.
Proof.
    intros. unfold t_update. apply functional_extensionality. intros. destruct (eqb_spec x x0).
    - subst. reflexivity.
    - reflexivity.
Qed.


Definition partial_map (A: Type) := total_map (option A).

Definition empty {A: Type} : partial_map A := 
    t_empty None.

Definition update {A: Type} (m: partial_map A) (x: string) (v: A) :=
    (x !-> (Some v); m).

Notation "x '|->' v ';' m" := (update m x v)
    (at level 100, v at next level, right associativity).

Notation "x '|->' v" := (update empty x v)
    (at level 100).

Example example_partial_map :=
    ("Church" |-> true; "Turing" |-> false).

Lemma apply_empty : forall (A: Type) (x: string),
    @empty A x = None.
Proof.
    intros. unfold empty. unfold t_empty. reflexivity. Qed.

Lemma update_eq : forall (A: Type) (m: partial_map A) x v,
    (x |-> v; m) x = Some v.
Proof.
    intros. unfold update. unfold t_update. rewrite eqb_refl. reflexivity.
Qed.

Definition includein {A: Type} (m m': partial_map A) :=
    forall x v, m x = Some v -> m' x = Some v.
