Require Coq.FSets.FMapList.
Require Coq.FSets.FSetList.
Require Import Coq.FSets.FSetFacts.
Require Import Coq.Structures.OrderedType.
Require Import Coq.Structures.OrderedTypeEx.
Require Import String.
Require Import BinInt.

Module Loc_as_OT := PairOrderedType(String_as_OT)(Nat_as_OT).

Module MemMap := FMapList.Make(Loc_as_OT).

Module LocSet := FSetList.Make(Loc_as_OT).

Definition loc := Loc_as_OT.t.
Definition locset := LocSet.t.
Definition var := string.

(* Value : Z U loc *)
Inductive value : Type :=
    | VInt (n: Z)
    | VPtr (l: loc).

(* State : loc -> value *)
Definition state := MemMap.t value.