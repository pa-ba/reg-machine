(** Calculation of the simple arithmetic language. *)

Require Import List.
Require Import Tactics.
Require Import Coq.Program.Equality.
Module Arith (Import mem : Memory).
  

  
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

Inductive Conf : Type := conf : Code -> nat -> Mem nat -> Conf.

Notation "⟨ x , y , z ⟩" := (conf x y z).

Reserved Notation "x ==> y" (at level 80, no associativity).
Inductive VM : Conf -> Conf -> Prop :=
| vm_load n a c s : ⟨LOAD n c, a , s⟩ ==> ⟨c , n,  s⟩
| vm_add c s a r n : s[r] = n -> ⟨ADD r c, a , s⟩ ==> ⟨c , n + a,  s⟩
| vm_store c s a r : ⟨STORE r c, a , s⟩ ==> ⟨c , a, s[r:=a]⟩
where "x ==> y" := (VM x y).


Inductive cle : Conf -> Conf -> Prop :=
  cle_mem x y z z' : z ≤ z' -> cle ⟨ x , y , z ⟩ ⟨ x , y , z' ⟩.

Hint Constructors cle.


(** * Calculation *)

(** Boilerplate to import calculation tactics *)
Module VM <: Machine.
Definition Conf := Conf.
Definition Pre := cle.
Definition Rel := VM.
Definition MemElem := nat.
Lemma monotone : monotonicity cle VM.
prove_monotonicity. Qed.
Lemma preorder : is_preorder cle.
prove_preorder. Qed.
End VM.
Module VMCalc := Calculation mem VM.
Import VMCalc.


(** Specification of the compiler *)

Theorem spec e r c a s : freeFrom r s -> ⟨comp' e r c, a, s⟩  =|> ⟨c , eval e, s⟩ .


(** Setup the induction proof *)

Proof.
  intros.
  generalize dependent c.
  generalize dependent s.
  generalize dependent r.
  generalize dependent a.
  induction e;intros.

(** Calculation of the compiler *)

(** - [x = Val n]: *)

  begin
    ⟨c , eval (Val n), s⟩.
  = {auto}
      ⟨ c, n, s⟩.
  <== { apply vm_load }
      ⟨ LOAD n c, a, s ⟩.
  [].

(** - [x = Add x1 x2]: *)
  
  begin
    ⟨ c, eval (Add e1 e2), s ⟩.
  = {auto}
    ⟨ c, eval e1 + eval e2, s ⟩.
  ≤ {auto}
    ⟨c, eval e1 + eval e2, s[r:=eval e1]⟩.
  <== {apply vm_add}
      ⟨ADD r c, eval e2, s[r:=eval e1]⟩.
  <|= {apply IHe2}
      ⟨comp' e2 (next r) (ADD r c), eval e1, s[r:=eval e1]⟩.
  <== { apply vm_store}
    ⟨STORE r (comp' e2 (next r) (ADD r c)), eval e1, s⟩.
  <|= { apply IHe1 }
    ⟨comp' e1 r (STORE r (comp' e2 (next r) (ADD r c))), a, s⟩.
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
