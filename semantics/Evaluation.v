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


Module Eval.
Fixpoint aeval (st: state) (a: aexp): option value :=
    match a with
    | ANum n => Some (VInt n)
    | AId x => match (MemMap.find x st) with
                | Some v => Some v
                | None => None
                end
    | <{ a1 + a2 }> => add_value (aeval st a1) (aeval st a2) 
    end.

Inductive aevalR: aexp -> option value -> Prop :=
    | E_ANum (n: Z): aevalR (ANum n) (Some (VInt n))
    | E_AId_Def (l: loc): aevalR (AId l) (Some (VPtr l))
    | E_AId_Undef (l: loc): aevalR (AId l) None
    | E_APlus_Num (a1 a2: aexp) (n1 n2: Z):
        aevalR a1 (Some (VInt n1)) ->
        aevalR a2 (Some (VInt n2)) ->
        aevalR (<{ a1 + a2 }>) (Some (VInt (n1 + n2)))
    | E_APlus_Undef (a1 a2: aexp):
        aevalR a1 None ->
        aevalR a2 None ->
        aevalR (<{ a1 + a2 }>) None.

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

End Eval.