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
| Deref (e: expr).

Inductive stmt: Type :=
| Skip
| Assign (x: string) (e: expr).
(* | Alloc (x: string) (mu: string). *)

Definition eval_expr (mem: mem) (env: env) (expr: expr): value :=
  match expr with
  | Const n => VInt n
  | Addr x =>
    match env !! x with
    | Some l => match mem !! l with 
                | Some v => v
                | None => VInt 0
                end
    | None => VInt 0
    end
  | Deref e => match e with
    | Addr x => match env !! x with
                | Some l => match mem !! l with 
                            | Some v => v
                            | None => VInt 0
                            end
                | None => VInt 0
                end
    | _ => VInt 0
    end
end.

Definition eval_lval (mem: mem) (env: env) (lval: expr): value :=
  match lval with
  | Deref e => eval_expr mem env e
  | _ => VInt 0
  end.

Definition def_heap := VInt 0.

Definition eval_stmt (m: mem) (e: env) (s: stmt): mem * env :=
  match s with
  | Skip => (m, e)
  | Assign x expr =>
        let v := eval_expr m e expr in
        let m' := map_insert x v m in
        let e' := map_insert x x e in
        (m', e')
      end.

(* Theorem eval_stmt_eq: forall (m m': mem) (e e': env) (s: stmt),
  m = m' /\ e = e' -> eval_stmt m e s = eval_stmt m' e' s.
Proof.
  intros. destruct H as [Hm He]. rewrite Hm. rewrite He. reflexivity.
Qed. *)

Definition state := (mem * env)%type.

(* Read and Written sets *)
Definition locs := stringset.
Definition vars := stringset.

Definition proj_mem (m: mem) (l: locs): mem :=
  (filter (fun k => k ∈ l) m).

Definition proj_env (e: env) (v: vars): env :=
  (filter (fun k => k ∈ v) e).

Definition proj (s: state) (v: vars) (l: locs)  :=
  let (m, e) := s in
  (proj_env e l, proj_mem m v).


Definition upsilon (expr: expr) (state: state) : vars*locs :=
let (mem, env) := state in
match expr with
| Const _ => (∅, ∅)
| Addr x => match env !! x with
           | Some l => ({[x]}, {[l]})
           | None => (∅, ∅)
           end
| Deref e => match e with
  | Addr x => match env !! x with
              | Some l => ({[x]}, {[l]})
              | None => (∅, ∅)
              end
  | _ => (∅, ∅)
  end
end.

Definition upsilon_vars (expr: expr) (env: env): vars :=
match expr with
| Const _ => ∅
| Addr x => match env !! x with
           | Some l => {[x]}
           | None => ∅
           end
| Deref e => match e with
  | Addr x => match env !! x with
              | Some l => {[x]}
              | None => ∅
              end
  | _ => ∅
  end
end.

Definition read (stmt: stmt) (state: state) : vars*locs :=
  let (m, e) := state in
  match stmt with
  | Skip => (∅, ∅)
  | Assign x expr => upsilon expr state
  end.

Definition read_vars (stmt: stmt) (env: env) : vars :=
  match stmt with
  | Skip => ∅
  | Assign x expr => upsilon_vars expr env
  end.

Definition write (stmt: stmt) (state: state) : vars*locs :=
  let (m, e) := state in
  match stmt with
  | Skip => (∅, ∅)
  | Assign x expr => match e !! x with
                    | Some l => ({[x]}, {[l]})
                    | None => (∅, ∅)
                    end
  end.

Definition write_vars (stmt: stmt) (env: env) : vars :=
  match stmt with
  | Skip => ∅
  | Assign x expr => match env !! x with
                    | Some l => {[x]}
                    | None => ∅
                    end
  end.

Theorem proj_env_eq: forall (e1 e2: env) (v: vars),
  proj_env e1 v = proj_env e2 v -> forall (x: string), x ∈ v -> e1 !! x = e2 !! x.
Proof.
Admitted.

Theorem proj_env_empty: forall (e: env),
  proj_env e ∅ = ∅.
Proof.
  intros. unfold proj_env. 
Admitted.

Theorem proj_env_same: forall (m: mem) (e1 e2: env) (stmt: stmt) (r1 r2: vars),
  r2 = read_vars stmt e2 /\
  r1 = read_vars stmt e1 /\
  r1 = r2 /\
  proj_env e1 r1 = proj_env e2 r2  
    -> proj_env (snd(eval_stmt m e1 stmt)) (write_vars stmt e1) = proj_env (snd(eval_stmt m e2 stmt)) (write_vars stmt e2).
Proof.
  intros. destruct H. destruct H0. destruct H1. destruct stmt0.
  - simpl. simpl in H. simpl in H0. rewrite -> H0 in H2. rewrite -> H in H2. assumption.
  - simpl in H. simpl in H0. destruct e.
    + simpl. destruct (e2 !! x) eqn:He2x.
      * destruct (e1 !! x) eqn:He1x.
        -- simpl in H2.
Abort.
