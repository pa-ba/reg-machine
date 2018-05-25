(** Calculation for the lambda calculus + arithmetic. *)

Require Import List.
Require Import ListIndex.
Require Import Tactics.
Require Import Coq.Program.Equality.
Module Lambda (mem : Memory).
Module Mem := MemoryTheory mem.
Import Mem.


(** * Syntax *)

Inductive Expr : Set := 
| Val : nat -> Expr 
| Add : Expr -> Expr -> Expr
| Var : nat -> Expr
| Abs : Expr -> Expr
| App : Expr -> Expr -> Expr.

(** * Semantics *)

(** The evaluator for this language is given as follows (as in the
paper):
<<
type Env = [Value]
data Value =  Num Int | Fun (Value -> Value)


eval ::  Expr -> Env -> Value
eval (Val n) e   = Num n
eval (Add x y) e = case eval x e of
                     Num n -> case eval y e of
                                Num m -> Num (n+m)
eval (Var i) e   = e !! i
eval (Abs x) e   = Fun (\v -> eval x (v:e))
eval (App x y) e = case eval x e of
                     Fun f -> f (eval y e)
>>
After defunctionalisation and translation into relational form we
obtain the semantics below. *)

Inductive Value : Set :=
| Num : nat -> Value
| Clo : Expr -> list Value -> Value.

Definition Env := list Value.

Reserved Notation "x ⇓[ e ] y" (at level 80, no associativity).

Inductive eval : Expr -> Env -> Value -> Prop :=
| eval_val e n : Val n ⇓[e] Num n
| eval_add e x y m n : x ⇓[e] Num m -> y ⇓[e] Num n -> Add x y ⇓[e] Num (m + n)
| eval_var e i v : nth e i = Some v -> Var i ⇓[e] v
| eval_abs e x : Abs x ⇓[e] Clo x e
| eval_app e e' x x' x'' y y' : x ⇓[e] Clo x' e' -> y ⇓[e] y' -> x' ⇓[y' :: e'] x'' -> App x y ⇓[e] x''
where "x ⇓[ e ] y" := (eval x e y).

(** * Compiler *)

Inductive Code : Set :=
| LOAD : nat -> Code -> Code
| ADD : adr -> Code -> Code
| STORE : adr -> Code -> Code
| LOOKUP : nat -> Code -> Code
| RET : Code
| APP : adr -> Code -> Code
| ABS : Code -> Code -> Code
| POP : Code -> Code
| HALT : Code.

Fixpoint comp' (e : Expr) (r : adr) (c : Code) : Code :=
  match e with
    | Val n => LOAD n c
    | Add x y => comp' x r (STORE r (comp' y (next r) (ADD r c)))
    | Var i => LOOKUP i c
    | App x y => comp' x r (STORE r (comp' y (next r) (APP r (POP c))))
    | Abs x => ABS (comp' x (next adr0) RET) c
  end.

Definition comp (e : Expr) : Code := comp' e adr0 HALT.

(** * Virtual Machine *)

Inductive Value' : Set :=
| Num' : nat -> Value'
| Clo' : Code -> list Value' -> Value'.

Definition Env' := list Value'.

Inductive Elem : Set :=
| VAL : Value' -> Elem 
| CLO : Code -> Env' -> Elem
.

Notation empty := (empty_mem Elem).

Definition Stack : Type := list (Mem Elem).

Inductive Conf : Type := 
| conf : Code -> Value' -> Env' -> Stack -> Mem Elem -> Conf.

Notation "⟨ c , a , e , k , s ⟩" := (conf c a e k s).

Reserved Notation "x ==> y" (at level 80, no associativity).
Inductive VM : Conf -> Conf -> Prop :=
 | vm_push n c s a e k :  ⟨LOAD n c, a, e, k, s⟩ ==> ⟨c, Num' n, e, k, s⟩
 | vm_pop c s s' a e k :  ⟨POP c, a, e, s' :: k, s⟩ ==> ⟨c, a, e, k, s'⟩
 | vm_add c m n r s e k : s[r] = VAL (Num' m) -> ⟨ADD r c, Num' n, e, k, s⟩
                                                 ==> ⟨c, Num'(m + n), e, k, s⟩
 | vm_store c v r s e k : ⟨STORE r c, v, e, k, s⟩
                        ==> ⟨c, v, e, k, s[r:=VAL v]⟩
 | vm_lookup e i c v a s k : nth e i = Some v -> ⟨LOOKUP i c, a, e, k, s⟩ ==> ⟨c, v, e, k, s⟩
 | vm_env a c e e' s k : s[adr0] = CLO c e -> ⟨RET, a, e', k, s⟩ ==> ⟨c, a, e, k, s⟩
 | vm_app c c' e e' v r s k :
     s[r]=VAL (Clo' c' e') ->
     ⟨APP r c, v, e, k,s⟩ ==> ⟨c', Num' 0, v :: e', s :: k, empty[adr0:=CLO c e]⟩
 | vm_abs a c c' s e k : ⟨ABS c' c, a, e, k, s⟩ ==> ⟨c, Clo' c' e, e, k, s⟩
where "x ==> y" := (VM x y).

(** Conversion functions from semantics to VM *)

Fixpoint conv (v : Value) : Value' :=
  match v with
    | Num n => Num' n
    | Clo x e => Clo' (comp' x (next adr0) RET) (map conv e)
  end.

Definition convE : Env -> Env' := map conv.

Inductive stackle : Stack -> Stack -> Prop :=
| stackle_empty : stackle nil nil
| stackle_cons s s' k k' : s ≤ s' -> stackle k k' -> stackle (s :: k) (s' :: k').

Hint Constructors stackle : memory.

Lemma stackle_refl k : stackle k k.
Proof.
  induction k; constructor; auto with memory.
Qed.

Lemma stackle_trans k1 k2 k3 : stackle k1 k2 -> stackle k2 k3 -> stackle k1 k3.
Proof.
  intros L1. generalize k3. induction L1; intros k3' L2. assumption. inversion L2. subst. constructor;
  eauto with memory.
Qed.

Hint Resolve stackle_refl stackle_trans.

Inductive cle : Conf -> Conf -> Prop :=
 | cle_mem  c a e k k' s s' : stackle k k' -> s ≤ s' -> cle ⟨ c , a , e , k, s ⟩ ⟨ c , a , e , k', s' ⟩.

Hint Constructors cle.

Lemma rel_eq {T} {R : T -> T -> Prop} x y y' : R x y' -> y = y' -> R x y.
Proof. intros. subst. auto.
Qed .
Lemma rel_eq' {T} {R : T -> T -> Prop} x x' y : R x' y -> x = x' -> R x y.
Proof. intros. subst. auto.
Qed .

Ltac apply_eq t := eapply rel_eq; [apply t | repeat rewrite set_set; auto].


(** * Calculation *)

(** Boilerplate to import calculation tactics *)

Module VM <: Machine.
Definition Conf := Conf.
Definition Pre := cle.
Definition Rel := VM.
Definition MemElem := nat.
Lemma monotone : monotonicity cle VM.
  prove_monotonicity1;
    try (match goal with [H : stackle (_ :: _) _ |- _] => inversion H end)
    ; prove_monotonicity2.
Qed.
Lemma preorder : is_preorder cle.
prove_preorder. Qed.
End VM.



(* Lemma rel_eq {T} {R : T -> T -> Prop} x y y' : R x y' -> y = y' -> R x y. *)
(* Proof. intros. subst. auto. *)
(* Qed . *)
(* Ltac apply_eq t := eapply rel_eq; [apply t | repeat rewrite set_set; auto]. *)

(* Module VM <: (Machine mem). *)
(* Definition Conf := Conf. *)
(* Definition Rel := VM. *)
(* Definition MemElem := Elem. *)
(* Lemma monotone : monotonicity VM. *)
(*   do 5 intro; intros Hle Step; *)
(*   dependent destruction Step; *)
(*   try (eexists; (split; [econstructor| idtac]); eauto using memle_get, set_monotone). *)
(*   eexists (empty [adr0 := CLO c e]). split. apply_eq vm_app. eauto using memle_get, set_monotone.  *)

(*   apply Hle in H. *)

  
(*   Admitted. *)


Module VMCalc := Calculation mem VM.
Import VMCalc.



(** Specification of the compiler *)

Theorem spec p v e r c a s k :
  freeFrom r s ->  p ⇓[e] v ->
  ⟨comp' p r c, a, convE e, k, s⟩ =|> ⟨c , conv v, convE e, k, s⟩.

(** Setup the induction proof *)

Proof.
  intros F E.
  generalize dependent c.
  generalize dependent a.
  generalize dependent s.
  generalize dependent r.
  generalize dependent k.
  induction E;intros.

(** Calculation of the compiler *)

(** - [Val n ⇓[e] Num n]: *)

  begin
  ⟨c, Num' n , convE e, k, s⟩.
  <== { apply vm_push }
  ⟨LOAD n c, a, convE e, k, s⟩.
  [].

(** - [Add x y ⇓[e] Num (m + n)]: *)

  begin
    ⟨c, Num' (m + n), convE e, k, s⟩.
  ≤ {auto}
    ⟨c, Num' (m + n), convE e, k, s[r:=VAL (Num' m)]⟩ .
  <== { apply vm_add }
    ⟨ADD r c, Num' n, convE e, k, s[r:=VAL (Num' m)]⟩ .
  <|= { apply IHE2 }
      ⟨comp' y (next r) (ADD r c), Num' m, convE e, k, s[r:=VAL (Num' m)]⟩ .
  <== { apply vm_store }
      ⟨STORE r (comp' y (next r) (ADD r c)), Num' m, convE e, k, s⟩.
  <|= { apply IHE1 }
      ⟨comp' x r (STORE r (comp' y (next r) (ADD r c))), a, convE e, k, s⟩.
  [].

(** - [Var i ⇓[e] v] *)

  begin
    ⟨c, conv v, convE e , k, s⟩.
  <== {apply vm_lookup; unfold convE; rewrite nth_map; rewr_assumption}
      ⟨LOOKUP i c, a , convE e, k, s ⟩.
   [].

(** - [Abs x ⇓[e] Clo x e] *)

  begin
    ⟨c, Clo' (comp' x (next adr0) RET) (convE e), convE e, k, s ⟩.
  <== { apply vm_abs }
    ⟨ABS (comp' x (next adr0) RET) c, a, convE e, k, s ⟩.
  [].

(** - [App x y ⇓[e] x''] *)

  begin
    ⟨c, conv x'', convE e, k, s ⟩.
  <== { apply vm_pop }
    ⟨POP c, conv x'', convE e, s :: k, empty[adr0:=CLO (POP c) (convE e)] ⟩.
  <== { apply vm_env }
    ⟨RET, conv x'', convE (y' :: e'), s :: k, empty[adr0:=CLO (POP c) (convE e)]⟩.
  <|= {apply  IHE3}
      ⟨comp' x' (next adr0) RET, Num' 0, convE (y' :: e'), s :: k, empty[adr0:=CLO (POP c) (convE e)]⟩.
  = {auto}
      ⟨comp' x' (next adr0) RET, Num' 0, conv y' :: convE e', s::k, empty[adr0:=CLO (POP c) (convE e)]⟩.
  ≤ {auto with memory}
      ⟨comp' x' (next adr0) RET, Num' 0, conv y' :: convE e', s[r:=VAL (Clo' (comp' x' (next adr0) RET) (convE e'))]::k, empty[adr0:=CLO (POP c) (convE e)]⟩.
  <== {apply_eq vm_app}
      ⟨APP r (POP c), conv y', convE e, k, s[r:=VAL (Clo' (comp' x' (next adr0) RET) (convE e'))]⟩.
  <|= {apply IHE2}
      ⟨comp' y (next r) (APP r (POP c)), (Clo' (comp' x' (next adr0) RET) (convE e')), convE e, k, s[r:=VAL (Clo' (comp' x' (next adr0) RET) (convE e'))]⟩.
  <== { apply vm_store }
    ⟨STORE r (comp' y (next r) (APP r (POP c))), (Clo' (comp' x' (next adr0) RET) (convE e')), convE e, k, s⟩.
  = {auto}
    ⟨STORE r (comp' y (next r) (APP r (POP c))), conv (Clo x' e'), convE e, k, s ⟩.
  <|= { apply IHE1 }
    ⟨comp' x r (STORE r (comp' y (next r) (APP r (POP c)))), a, convE e,k, s ⟩.
  [].
Qed.
  
(** * Soundness *)

Lemma determ_vm : determ VM.
  intros C C1 C2 V. induction V; intro V'; inversion V'; subst; congruence.
Qed.
  

Definition terminates (p : Expr) : Prop := exists r, p ⇓[nil] r.

Theorem sound p a s C : freeFrom adr0 s -> terminates p -> ⟨comp p, a, nil, nil, s⟩ =>>! C -> 
                          exists v s', C = ⟨HALT , conv v, nil, nil, s'⟩ /\ p ⇓[nil] v.
Proof.
  unfold terminates. intros F T M. destruct T as [v T].
  pose (spec p v nil adr0 HALT a s nil F T) as H'.
  unfold Reach in *. repeat autodestruct.
  pose (determ_trc determ_vm) as D.
  unfold determ in D. inversion H0.  inversion H7.  subst. exists v. eexists. split. eapply D. apply M. split.
  unfold comp.
  simpl in *. apply H. intro Contra. destruct Contra.
  inversion H1. assumption.
Qed.

End Lambda.