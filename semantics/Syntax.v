Require Import BinInt.
Require Import Coq.Strings.String.
Require Import SEM.State.

Module AExp.

Inductive aexp : Type :=
    | ANum (n: Z)
    | AId (x: string)
    | AAddr (x: string)
    | APlus (a1 a2: aexp).


End AExp.

Module BExp.
Import AExp.

Inductive bexp : Type :=
    | BTrue
    | BFalse
    | BLe (a1 a2: aexp)
    | BEq (a1 a2: aexp)
    | BNot (b: bexp).
End BExp.

Module Com.
Import AExp.

Inductive com : Type :=
    | CSkip
    | CSeq (c1 c2: com)
    | CAsgn (x:string) (a: aexp)
    | CAlloc (x:string) (mu: string).
End Com.
