(* Calculation of the simple arithmetic language. *)
Require Import List.
Require Import Tactics.


Inductive Expr : Set :=  Val (n : nat) | Add (x y : Expr).

Fixpoint eval (x: Expr) : nat :=
  match x with
    | Val n => n
    | Add x1 x2 => eval x1 + eval x2
  end.

Inductive Instr : Set := .

Definition Code := list Instr.

Import ListNotations.


Fixpoint comp (e : Expr) (c : Code) : Code :=
  match e with
    | Val n => Admit
    | Add x y => Admit
  end.

Definition Stack : Set := list nat.

Definition Conf : Set := prod Code  Stack.


Hint Constructors VM.

(* Boilerplate to import calculation tactics *)
Module VM <: Machine.
Definition Conf := Conf.
Definition Rel := VM.
End VM.
Module VMCalc := Calculation VM.
Import VMCalc.

Ltac by_eval := eval_inv (eval).

Theorem spec e P c :  { s, (comp e c, s) | P s} =|>
                        { s n, (c , n :: s) | (e ⇓ n) /\ P s}.
Proof.
  intros.
  generalize dependent c.
  generalize dependent P.
  induction e; intros.

  begin
    ({ s n', (c, n' :: s) | (Val n ⇓ n') /\ P s}).
  = {by_eval}
    ({ s, (c, n :: s) | P s}) .
  <== {apply vm_push}
    ({ s, (PUSH n :: c, s) | P s }) .
  [].

  begin
  ({s n, (c, n :: s) | Add e1 e2 ⇓ n /\ P s }) .
  = { by_eval }
  ({s n m, (c, (n + m) :: s) | e1 ⇓ n /\ e2 ⇓ m /\ P s}) .
  <== { apply vm_add }
  ({ s n m, (ADD :: c, m :: n :: s) | e1 ⇓ n /\ e2 ⇓ m /\ P s}).
  = { eauto }
  ({s' m, (ADD :: c, m :: s') | e2 ⇓ m /\ (exists s n, e1 ⇓ n /\ s' = n :: s /\ P s)} ).
  <|= { apply IHe2 }
  ({s, (comp e2 (ADD :: c), s) | exists s' n, e1 ⇓ n /\ s = n :: s' /\ P s'}).
  = { eauto }
  ({s n, (comp e2 (ADD :: c),  n :: s) | e1 ⇓ n /\ P s }).
  <|= { apply IHe1 }
  ({s, (comp e1 (comp e2 (ADD :: c)),  s) | P s }).
  [].
Qed.