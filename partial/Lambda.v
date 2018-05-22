(** Calculation for the lambda calculus + arithmetic. *)

Require Import List.
Require Import ListIndex.
Require Import Tactics.
Require Import Coq.Program.Equality.
Module Lambda (mem : Memory).
Import mem.

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
| RET : adr -> Code
| APP : adr -> Code -> Code
| ABS : (adr -> Code) -> Code -> Code
| HALT : Code.

Fixpoint comp' (e : Expr) (r : adr) (c : Code) : Code :=
  match e with
    | Val n => LOAD n c
    | Add x y => comp' x r (STORE r (comp' y (next r) (ADD r c)))
    | Var i => LOOKUP i c
    | App x y => comp' x r (STORE r (comp' y (next r) (APP r c)))
    | Abs x => ABS (fun r' => comp' x (next r') (RET r')) c
  end.

Definition comp (e : Expr) : Code := comp' e adr0 HALT.

(** * Virtual Machine *)

Inductive Value' : Set :=
| Num' : nat -> Value'
| Clo' : (adr -> Code) -> list Value' -> Value'.

Definition Env' := list Value'.

Inductive Elem : Set :=
| VAL : Value' -> Elem 
| CLO : Code -> Env' -> Elem
.

Inductive Conf : Set := 
| conf : Code -> Value' -> Env' -> Conf.

Notation "⟨ c , a , e , s ⟩" := (conf c a e, s).

Reserved Notation "x ==> y" (at level 80, no associativity).
Inductive VM : Conf * Mem Elem -> Conf * Mem Elem -> Prop :=
 | vm_push n c s a e :  ⟨LOAD n c, a, e, s⟩ ==> ⟨c, Num' n, e, s⟩ 
 | vm_add c m n r s e : s[r] = VAL (Num' m) -> ⟨ADD r c, Num' n, e, s⟩ 
                                                 ==> ⟨c, Num'(m + n), e, s⟩
 | vm_store c v r s e : ⟨STORE r c, v, e, s⟩ 
                        ==> ⟨c, v, e, s[r:=VAL v]⟩                                                 
 | vm_lookup e i c v a s : nth e i = Some v -> ⟨LOOKUP i c, a, e, s⟩ ==> ⟨c, v, e, s⟩ 
 | vm_env a r c e e' s  : s[r] = CLO c e -> ⟨RET r, a, e', s⟩ ==> ⟨c, a, e, s⟩
 | vm_app c c' e e' v r s :
     s[r]=VAL (Clo' c' e') ->
     ⟨APP r c, v, e,s⟩ ==> ⟨c' r, Num' 0, v :: e', s[r:=CLO c e]⟩
 | vm_abs a c c' s e : ⟨ABS c' c, a, e, s⟩ ==> ⟨c, Clo' c' e, e, s⟩
where "x ==> y" := (VM x y).

(** Conversion functions from semantics to VM *)

Fixpoint conv (v : Value) : Value' :=
  match v with
    | Num n => Num' n
    | Clo x e => Clo' (fun r => comp' x (next r) (RET r)) (map conv e)
  end.

Definition convE : Env -> Env' := map conv.

(** * Calculation *)

(** Boilerplate to import calculation tactics *)

Module Mon := Monotonicity mem.
Import Mon.

Module VM <: (Machine mem).
Definition Conf := Conf.
Definition Rel := VM.
Definition MemElem := Elem.
Lemma monotone : monotonicity VM.
prove_monotonicity. Qed.
End VM.
Module VMCalc := Calculation mem VM.
Import VMCalc.



(** Specification of the compiler *)

Theorem spec p v e r c a s :
  freeFrom r s ->  p ⇓[e] v ->
  ⟨comp' p r c, a, convE e, s⟩ =|> ⟨c , conv v, convE e, s⟩.

(** Setup the induction proof *)

Proof.
  intros F E.
  generalize dependent c.
  generalize dependent a.
  generalize dependent s.
  generalize dependent r.
  induction E;intros.

(** Calculation of the compiler *)

(** - [Val n ⇓[e] Num n]: *)

  begin
  ⟨c, Num' n , convE e, s⟩.
  <== { apply vm_push }
  ⟨LOAD n c, a, convE e, s⟩.
  [].

(** - [Add x y ⇓[e] Num (m + n)]: *)

  begin
    ⟨c, Num' (m + n), convE e, s⟩.
  ≤ { auto }
    ⟨c, Num' (m + n), convE e, s[r:=VAL (Num' m)]⟩ .
  <== { apply vm_add }
    ⟨ADD r c, Num' n, convE e, s[r:=VAL (Num' m)]⟩ .
  <|= { apply IHE2 }
      ⟨comp' y (next r) (ADD r c), Num' m, convE e, s[r:=VAL (Num' m)]⟩ .
  <== { apply vm_store }
      ⟨STORE r (comp' y (next r) (ADD r c)), Num' m, convE e, s⟩.
  <|= { apply IHE1 }
      ⟨comp' x r (STORE r (comp' y (next r) (ADD r c))), a, convE e, s⟩.
  [].

(** - [Var i ⇓[e] v] *)

  begin
    ⟨c, conv v, convE e , s⟩.
  <== {apply vm_lookup; unfold convE; rewrite nth_map; rewr_assumption}
      ⟨LOOKUP i c, a , convE e, s ⟩.
   [].

(** - [Abs x ⇓[e] Clo x e] *)

  begin
    ⟨c, Clo' (fun r' => comp' x (next r') (RET r')) (convE e), convE e, s ⟩.
  <== { apply vm_abs }
    ⟨ABS (fun r' => comp' x (next r') (RET r')) c, a, convE e, s ⟩.
  [].

(** - [App x y ⇓[e] x''] *)

  begin
    ⟨c, conv x'', convE e, s ⟩.
  ≤ { auto }
    ⟨c, conv x'', convE e, s[r:=CLO c (convE e)] ⟩.
  <== { apply vm_env }
    ⟨RET r, conv x'', convE (y' :: e'), s[r:=CLO c (convE e)]⟩.
  <|= { apply IHE3 }
    ⟨comp' x' (next r) (RET r), Num' 0, convE (y' :: e'), s[r:=CLO c (convE e)]⟩.
  = {auto}
      ⟨comp' x' (next r) (RET r), Num' 0, conv y' :: convE e', s[r:=CLO c (convE e)]⟩.
  <== {apply_eq vm_app}
      ⟨APP r c, conv y', convE e, s[r:=VAL (Clo' (fun r' => comp' x' (next r') (RET r')) (convE e'))]⟩.
  <|= { apply IHE2 }
    ⟨comp' y (next r) (APP r c), (Clo' (fun r' => comp' x' (next r') (RET r')) (convE e')), convE e, s[r:=VAL (Clo' (fun r' => comp' x' (next r') (RET r')) (convE e'))]⟩.
  <== { apply vm_store }
    ⟨STORE r (comp' y (next r) (APP r c)), (Clo' (fun r' => comp' x' (next r') (RET r')) (convE e')), convE e, s⟩.
  = {auto}
    ⟨STORE r (comp' y (next r) (APP r c)), conv (Clo x' e'), convE e,s ⟩.
  <|= { apply IHE1 }
    ⟨comp' x r (STORE r (comp' y (next r) (APP r c))), a, convE e, s ⟩.
  [].
Qed.
  
(** * Soundness *)

Lemma determ_vm : determ VM.
  intros C C1 C2 V. induction V; intro V'; inversion V'; subst; congruence.
Qed.
  

Definition terminates (p : Expr) : Prop := exists r, p ⇓[nil] r.

Theorem sound p a s C : freeFrom adr0 s -> terminates p -> ⟨comp p, a, nil, s⟩ =>>! C -> 
                          exists v s', C = ⟨HALT , conv v, nil, s'⟩ /\ p ⇓[nil] v.
Proof.
  unfold terminates. intros F T M. destruct T as [v T].
  pose (spec p v nil adr0 HALT a s F T) as H'.
  unfold Reach in *. repeat autodestruct.
  pose (determ_trc determ_vm) as D.
  unfold determ in D. inversion H0. subst. exists v. eexists. split. eapply D. apply M. split.
  unfold comp.
  simpl in *. apply H. intro Contra. destruct Contra.
  inversion H1. assumption.
Qed.

End Lambda.