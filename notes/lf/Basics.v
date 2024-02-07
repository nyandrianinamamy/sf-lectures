Inductive day: Type :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.

Definition next_day (d: day): day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => saturday
  | saturday => sunday
  | sunday => monday
  end.

Definition next_weekday (d: day): day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | _ => monday
  end.

Compute (next_weekday monday).

Example test_next_day:
  (next_day monday) = tuesday.
Proof. simpl. reflexivity. Qed.


Inductive bool: Type :=
  | true
  | false.

Definition negb (b: bool): bool := 
  match b with
  | true => false
  | false => true
  end.

Definition andb (b1 b2: bool) :=
  match b1 with
  | true => b2
  | false => false
  end.

Definition orb (b1 b2: bool) :=
  match b1 with
  | true => true
  | false => b2
  end.

Example text_andb1:
  (andb true false) = false.
Proof. simpl. reflexivity. Qed.

Example test_orb1:
  (orb false true) = true.
Proof. simpl. reflexivity. Qed.

Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).


Example test_orb2:
  false || false = false.
Proof. simpl. reflexivity. Qed.

Definition nandb (b1 b2: bool) := 
  negb (andb b1 b2).

Example test_nandb1:
  (nandb true true) = false.
Proof. reflexivity. Qed.

Check negb.

Inductive rgb: Type :=
  | red
  | green
  | blue.

Inductive color: Type :=
  | black
  | white
  | primary (p: rgb).

Definition monochrome (c: color): bool :=
  match c with
  | black => true
  | white => true
  | primary p => false
  end.

Module NatPlayground.

Inductive N: Type :=
| O
| S (n: N).

Definition pred (n: N) : N :=
match n with
  | O => O
  | S n' => n'
end.
End NatPlayground.

Check (S (S (S (S O)))).

Definition minustwo (n: nat) : nat :=
match n with
  | O | S O => O
  | S (S n') => n'
end.

Compute minustwo (S (S O)).

Compute minustwo 4.

Fixpoint even (n: nat) : bool :=
match n with
  | O => true
  | S O => false
  | S (S n') => even n'
end.

Compute even (S O).

Definition odd (n: nat) : bool :=
  negb (even n).

Module NatPlayground2.

Fixpoint plus (n m: nat) : nat :=
  match n with
  | O => m
  | S n' => plus n' (S m)
  end.

Example test_plus1 : plus O (S O) = 1.
Proof. simpl. reflexivity. Qed.

Example test_plus2 : plus 3 2 = 5.
Proof. simpl. reflexivity. Qed.

Fixpoint mult (n m: nat) : nat :=
  match n,m with 
  | O, _ | _, O => O
  | S n', S m' => plus (mult n' m) m
  end.

Compute mult 4 0.

Fixpoint minus (n m: nat) : nat :=
  match n, m with
  | O , _ => O
  | S _, O => n
  | S n', S m' => minus n' m'
  end.

Compute minus 5 4.
Compute minus 0 10.
Compute minus 6 2.

End NatPlayground2.

Notation "x + y" := (plus x y)
                        (at level 50, left associativity)
                        : nat_scope.
Notation "x - y" := (minus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x * y" := (mult x y)
                       (at level 40, left associativity)
                       : nat_scope.

Check ((0 + 1) + 1) : nat.

Fixpoint eqb (n m: nat) : bool :=
  match n, m with
  | O, O => true
  | O, S _ | S _, O => false
  | S n', S m' => eqb n' m'
  end.

Compute eqb 1 1.
Compute eqb 2 3.


Fixpoint leb (n m: nat) : bool :=
  match n, m with
  | O, _ => true
  | _, O => false
  | S n', S m' => leb n' m'
  end.

Compute leb 0 3.
Compute leb 9 0.

Definition gb (n m: nat) : bool :=
  negb (leb n m).

Definition geb (n m: nat) : bool :=
  match negb (leb n m) with
  | false => eqb n m
  | true => true
  end.

Compute geb 5 4.
Compute geb 5 5.
Compute gb 6 3.
Compute gb 5 9.

Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.

Example test_leb3: (4 <=? 2) = false.
Proof. simpl. reflexivity. Qed.

Theorem plus_0_n : forall n : nat, 0 + n = n.
Proof.
  intros n.
  simpl.
  reflexivity.
Qed.


Theorem plus_id_example : forall n m: nat, n = m -> n + n = m + m.
Proof.
  intros n m.
  intros H.
  rewrite H.
  reflexivity.
Qed.

Check mult_n_O.
  

Theorem mult_n_0_m_0 : forall p q : nat, (p * 0) + (q * 0) = 0.
Proof.
  intros p q.
  rewrite <- mult_n_O.
  rewrite <- mult_n_O.
  reflexivity.
Qed.


Theorem plus_1_neq_0_firsttry : forall n : nat, ((n + 1) =? 0) = false.
Proof.
  intros n.
  destruct n as [| n'] eqn:E.
  - reflexivity.
  - reflexivity.
Qed.

Theorem negb_involutive : forall b: bool, negb (negb b) = b.
Proof.
  intros [].
  - reflexivity.
  - reflexivity.
Qed.



Theorem andb_commutative : forall b c, andb b c = andb c b.
Proof.
  intros [] [].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Definition idt (n: nat) : nat :=
match n with 
| O => plus O O
| S n' => plus n O
end.

Theorem idt_idt : forall (n: nat), idt n = n.
Proof.
  intros [| n'].
  - reflexivity.
  - simpl. rewrite <- plus_n_O. reflexivity.
Qed.

(* Fixpoint nonterm (n: nat) : nat :=
match n with
| O => O
| S n' => nonterm (idt n')
end. *)

Theorem identity_fn_applied_twice : 
forall (f: bool -> bool), 
(forall (x: bool), f x = x) -> forall (b: bool), f (f b) = b.
Proof.
  intros f.
  intros x.
  intros b.
  rewrite x. rewrite x. reflexivity.
Qed.


Theorem negation_fn_applied_twice : 
forall (f: bool -> bool), 
(forall (x: bool), f x = negb x) -> forall (b: bool), f (f b) = b.
Proof.
  intros f. intros x.
  intros b.
  destruct b as [|].
  - rewrite x. rewrite x. reflexivity.
  - rewrite x. rewrite x. reflexivity.
Qed.

Require Import Setoid.

Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
  intros b c.
  destruct b.
  destruct c.
  - intros H. reflexivity.
  - simpl. intros H. rewrite H. reflexivity.
  - simpl. destruct c.
    + intros H. reflexivity.
    + intros H. rewrite H. reflexivity.
Qed.

  
Theorem andb_eq_orb: 
forall (b c: bool), (andb b c = orb b c) -> b = c.
Proof.
  intros b.
  intros c.
  destruct b.
  destruct c.
  - simpl. intros H. reflexivity.
  - simpl. intros H. rewrite H. reflexivity.
  - simpl. destruct c.
    + intros H. rewrite H. reflexivity.
    + intros H. reflexivity.
Qed.

Theorem foo' : forall n, 0 <=? n = true.
Proof.
  reflexivity.
Qed.

Theorem silly : forall (P: Prop), P -> P.
Proof.
  intros P HP.
  try reflexivity.
  apply HP.
Qed.

  (* intros.
  destruct n;
  simpl;
  reflexivity.
Qed. *)

