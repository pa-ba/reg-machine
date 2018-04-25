(** Calculation of the simple arithmetic language. *)

Require Import List.
Require Import Tactics.
Require Import Coq.Program.Equality.
Module Arith (mem : Memory).
Import mem.

  
(** * Syntax *)

Inductive Expr : Set := 
| Val : nat -> Expr 
| Add : Expr -> Expr -> Expr.

(** * Semantics *)

Fixpoint eval (x: Expr) : nat :=
  match x with
    | Val n => n
    | Add x1 x2 => eval x1 + eval x2
  end.

(** * Compiler *)

Inductive Code : Set :=
| LOAD : nat -> Code -> Code
| ADD : adr -> Code -> Code
| STORE : adr -> Code -> Code
| HALT : Code.

Fixpoint comp' (x : Expr) (r : adr) (c : Code) : Code :=
  match x with
    Val n => LOAD n c
  | Add e1 e2 => comp' e1 r (STORE r (comp' e2 (next r) (ADD r c)))
  end.

Definition comp (x : Expr) : Code := comp' x adr0 HALT.

(** * Virtual Machine *)

Inductive Conf : Type := conf : Code -> Conf.

Notation "⟨ x , y , z ⟩" := (conf x, y, z).

Definition acc := named "acc".

Reserved Notation "x ==> y" (at level 80, no associativity).
Inductive VM : Conf * Mem nat * Mem nat -> Conf * Mem nat * Mem nat -> Prop :=
| vm_load n a c s : ⟨LOAD n c, a , s⟩ ==> ⟨c , a[acc:=n],  s⟩
| vm_add c s a m r n : s[r] = n -> m[acc] = a
                     -> ⟨ADD r c, m , s⟩ ==> ⟨c , m[acc:= n + a],  s⟩
| vm_store c s a m r : m[acc] = a -> ⟨STORE r c, m , s⟩ ==> ⟨c , m, s[r:=a]⟩
where "x ==> y" := (VM x y).


(** * Calculation *)

(** Boilerplate to import calculation tactics *)
Module Mon := Monotonicity mem.
Import Mon.

Module VM <: (Machine mem).
Definition Conf := Conf.
Definition Rel := VM.
Definition MemElem := nat.
Lemma monotone : monotonicity VM.
  do 8 intro; intros Hle Hle' Step;
  dependent destruction Step;
  do 2eexists; (split; [econstructor| idtac]) ; eauto using memle_get, set_monotone.
Qed.
End VM.
Module VMCalc := Calculation mem VM.
Import VMCalc.



(** Specification of the compiler *)

Theorem spec e r c m s : freeFrom r s -> ⟨comp' e r c, m, s⟩  =|> ⟨c , m[acc:=eval e], s⟩ .


(** Setup the induction proof *)

Proof.
  intros.
  generalize dependent c.
  generalize dependent s.
  generalize dependent r.
  generalize dependent m.
  induction e;intros.

(** Calculation of the compiler *)

(** - [x = Val n]: *)

  begin
    ⟨c , m[acc:=eval (Val n)], s⟩.
  = {auto}
      ⟨ c, m[acc:=n], s⟩.
  <== {apply vm_load }
      ⟨ LOAD n c, m, s ⟩.
  [].

(** - [x = Add x1 x2]: *)
  
  begin
    ⟨ c, m[acc:= eval (Add e1 e2)], s ⟩.
  = {auto}
    ⟨ c, m[acc:= eval e1 + eval e2], s ⟩.
  ≤ {auto}
    ⟨c, m[acc:= eval e1 + eval e2], s[r:=eval e1]⟩.
  <== {apply vm_add}
      ⟨ADD r c, m[acc:= eval e2], s[r:=eval e1]⟩.
  <|= {apply IHe2}
      ⟨comp' e2 (next r) (ADD r c), m[acc:=eval e1], s[r:=eval e1]⟩.
  <== { apply vm_store}
    ⟨STORE r (comp' e2 (next r) (ADD r c)), m[acc:=eval e1], s⟩.
  <|= { apply IHe1 }
    ⟨comp' e1 r (STORE r (comp' e2 (next r) (ADD r c))), m, s⟩.
  [].
Qed.


(** * Soundness *)
  
(** Since the VM is defined as a small step operational semantics, we *)
(* have to prove that the VM is deterministic and does not get stuck in *)
(* order to derive soundness from the above theorem. *)


Lemma determ_vm : determ VM.
  intros C C1 C2 V. induction V; intro V'; inversion V'; subst;eauto.
  rewrite H in *. inversion H5;subst. auto.
Qed.


Theorem sound x a s C : freeFrom adr0 s -> ⟨comp x, a, s⟩ =>>! C -> exists s', C = ⟨HALT, eval x, s'⟩.
Proof.
  intros F M.
  pose (spec x adr0 HALT a s F). unfold Reach in *. repeat autodestruct.
  pose (determ_trc determ_vm) as D.
  unfold determ in D. inversion H0. subst. eexists. eapply D. apply M. split. 
  apply H. intro Contra. destruct Contra.
  inversion H1.
Qed.

End Arith.
