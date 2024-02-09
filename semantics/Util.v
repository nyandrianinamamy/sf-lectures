Require Import BinInt.
Require Import Coq.Strings.String.
Require Import SEM.State.



(* Useful variables *)
Definition W : string := "W".
Definition X : string := "X".
Definition Y : string := "Y".


(* Operation on values *)
Definition add_value (v1 v2: option value) : option value :=
    match (v1, v2) with
    | (Some (VInt n1), Some (VInt n2)) => Some (VInt (n1 + n2))
    | _ => None
    end.

(* Compare two values *)
Definition cmp_value (v1 v2: value) : Prop :=
    match (v1, v2) with
    | (VInt n1, VInt n2) => Z.eq n1 n2
    | (VPtr l1, VPtr l2) => Loc_as_OT.eq l1 l2
    | _ => False
    end.

(* Locations *)
(* Creates a location as a global variable *)
Definition gvar_loc (x:string) : loc := (x, 0).

(* Find the instance of a variable in the state *)
Definition find_instance (st: state) (x: var): loc :=
    (x, 0).

(* Creates a fresh location in the state *)
Definition fresh (st: state) (mu: string): loc :=
    (mu, 0).

(* Default value for a newly allocated memory *)
Definition def_init : value := VInt 0.