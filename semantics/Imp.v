Require Import Strings.String.
Require Import stdpp.stringmap.



Inductive value: Type :=
| VInt (n: nat)
| VLoc (l: string).

Definition loc := string.

(* addr -> value *)
Definition mem := stringmap value.

(* var -> addr *)
Definition env := stringmap loc.

Inductive expr: Type :=
| Const (n: nat)
| Addr (x: string)
| LVal (e: expr)
with lval: Type :=
| Deref (e: expr).

Inductive stmt: Type :=
| Skip
| Assign (x: string) (e: expr)
| Alloc (x: string) (mu: string).

Fixpoint eval_expr (mem: mem) (env: env) (expr: expr): option value :=
  match expr with
  | Const n => Some (VInt n)
  | Addr x =>
    match env !! x with
    | Some l => mem !! l
    | None => None
    end
  | LVal e => match eval_expr mem env e with
              | Some (VLoc l) => mem !! l
              | _ => None
              end
  end.

Definition eval_lval (mem: mem) (env: env) (lval: lval): option value :=
  match lval with
  | Deref e => eval_expr mem env e
  end.

Definition def_heap := VInt 0.

Definition eval_stmt (m: mem) (e: env) (s: stmt): option (mem * env) :=
  match s with
  | Skip => Some (m, e)
  | Assign x expr =>
    match eval_expr m e expr with
    | Some v => let m' := map_insert x v m in
                let e' := map_insert x x e in
                  Some (m', e')
    | None => None
    end
  | Alloc x mu => 
                let m' := map_insert x def_heap m in
                let e' := map_insert x mu e in
                Some (m', e')
  end.

Theorem eval_stmt_eq: forall (m m': mem) (e e': env) (s: stmt),
  m = m' /\ e = e' -> eval_stmt m e s = eval_stmt m' e' s.
Proof.
  intros. destruct H as [Hm He]. rewrite Hm. rewrite He. reflexivity.
Qed.
