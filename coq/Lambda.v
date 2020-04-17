(** Calculation for the lambda calculus + arithmetic using a call
    stack for saving registers before a call. *)

Require Import List.
Require Import ListIndex.
Require Import Tactics.
Require Import Coq.Program.Equality.
Module Lambda (Import mem : Memory).


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
| eval_add e x y n n' : x ⇓[e] Num n -> y ⇓[e] Num n' -> Add x y ⇓[e] Num (n + n')
| eval_var e i v : nth e i = Some v -> Var i ⇓[e] v
| eval_abs e x : Abs x ⇓[e] Clo x e
| eval_app e e' x x' x'' y y' : x ⇓[e] Clo x' e' -> y ⇓[e] y' -> x' ⇓[y' :: e'] x'' -> App x y ⇓[e] x''
where "x ⇓[ e ] y" := (eval x e y).

(** * Compiler *)

Inductive Code : Set :=
| HALT : Code
| LOAD : nat -> Code -> Code
| LOOKUP : nat -> Code -> Code
| STORE : Reg -> Code -> Code
| ADD : Reg -> Code -> Code
| STC : Reg -> Code -> Code                         
| APP : Reg -> Code -> Code
| ABS : Code -> Code -> Code
| RET : Code.

Fixpoint comp (e : Expr) (r : Reg) (c : Code) : Code :=
  match e with
    | Val n   => LOAD n c
    | Var i   => LOOKUP i c
    | Add x y => comp x r (STORE r (comp y (next r) (ADD r c)))
    | App x y => comp x r (STC r (comp y (next r) (APP r c)))
    | Abs x   => ABS (comp x (next first) RET) c
  end.

Definition compile (e : Expr) : Code := comp e first HALT.

(** * Virtual Machine *)

Inductive Value' : Set :=
| Num' : nat -> Value'
| Clo' : Code -> list Value' -> Value'.

Definition Env' := list Value'.

Inductive val : Set :=
| NUM : nat -> val
| CLO : Code -> Env' -> val.

Definition empty := (@empty val).


Definition Lam : Type := list (Mem val).

Inductive Conf : Type := 
| conf : Code -> Value' -> Env' -> Lam -> Mem val -> Conf.

Notation "⟨ c , a , e , s , m ⟩" := (conf c a e s m).

Reserved Notation "x ==> y" (at level 80, no associativity).
Inductive VM : Conf -> Conf -> Prop :=
| vm_load n c m a e s :
    ⟨LOAD n c, a, e, s, m⟩         ==> ⟨c, Num' n, e, s, m⟩
| vm_add c a n r m e s : m[r] = NUM n ->
    ⟨ADD r c, Num' a, e, s, m⟩     ==> ⟨c, Num'(n + a), e, s, m⟩
| vm_store c n r m e s :
    ⟨STORE r c, Num' n, e, s, m⟩   ==> ⟨c, Num' n, e, s, m[r:=NUM n]⟩
| vm_stc c c' e' r m e s :
    ⟨STC r c, Clo' c' e', e, s, m⟩ ==> ⟨c, Clo' c' e', e, s, m[r:=CLO c' e']⟩
| vm_lookup e i c v a m s : nth e i = Some v ->
    ⟨LOOKUP i c, a, e, s, m⟩       ==> ⟨c, v, e, s, m⟩
| vm_ret a c e e' m m' s : m[first] = CLO c e ->
    ⟨RET, a, e', m' :: s, m⟩       ==> ⟨c, a, e, s, m'⟩
| vm_call c c' e e' v r m s : m[r]=CLO c' e' ->
    ⟨APP r c, v, e, s, m⟩          ==> ⟨c', v, v :: e', m :: s, empty[first:=CLO c e]⟩
| vm_fun a c c' m e s :
    ⟨ABS c' c, a, e, s, m⟩         ==> ⟨c, Clo' c' e, e, s, m⟩
where "x ==> y" := (VM x y).

(** Conversion functions from semantics to VM *)

Fixpoint conv (v : Value) : Value' :=
  match v with
    | Num n   => Num' n
    | Clo x e => Clo' (comp x (next first) RET) (map conv e)
  end.

Definition convE : Env -> Env' := map conv.

Inductive stackle : Lam -> Lam -> Prop :=
| stackle_empty : stackle nil nil
| stackle_cons m m' s s' : m ⊑ m' -> stackle s s' -> stackle (m :: s) (m' :: s').

Hint Constructors stackle : memory.

Lemma stackle_refl s : stackle s s.
Proof.
  induction s; constructor; auto with memory.
Qed.

Lemma stackle_trans s1 s2 s3 : stackle s1 s2 -> stackle s2 s3 -> stackle s1 s3.
Proof.
  intros L1. generalize s3. induction L1; intros s3' L2. assumption. inversion L2. subst. constructor;
  eauto with memory.
Qed.

Hint Resolve stackle_refl stackle_trans.

Inductive cle : Conf -> Conf -> Prop :=
 | cle_mem  c a e s s' m m' : stackle s s' -> m ⊑ m' -> cle ⟨ c , a , e , s, m ⟩ ⟨ c , a , e , s', m' ⟩.

Hint Constructors cle.

Lemma rel_eq {T} {R : T -> T -> Prop} x y y' : R x y' -> y = y' -> R x y.
Proof. intros. subst. auto.
Qed .
Lemma rel_eq' {T} {R : T -> T -> Prop} x x' y : R x' y -> x = x' -> R x y.
Proof. intros. subst. auto.
Qed .


(** * Calculation *)

(** Boilerplate to import calculation tactics *)

Module VM <: Machine.
Definition Conf := Conf.
Definition Pre := cle.
Definition Rel := VM.
Lemma monotone : monotonicity cle VM.
  prove_monotonicity1;
    try (match goal with [H : stackle (_ :: _) _ |- _] => inversion H end)
    ; prove_monotonicity2.
Qed.
Lemma preorder : is_preorder cle.
prove_preorder. Qed.
End VM.


Module VMCalc := Calculation mem VM.
Import VMCalc.



(** Specification of the compiler *)

Theorem spec p v e r c a m s :
  freeFrom r m ->  p ⇓[e] v ->
  ⟨comp p r c, a, convE e, s, m⟩ =|> ⟨c , conv v, convE e, s, m⟩.

(** Setup the induction proof *)

Proof.
  intros F E.
  generalize dependent c.
  generalize dependent a.
  generalize dependent m.
  generalize dependent r.
  generalize dependent s.
  induction E;intros.

(** Calculation of the compiler *)

(** - [Val n ⇓[e] Num n]: *)

  begin
  ⟨c, Num' n , convE e, s, m⟩.
  <== { apply vm_load }
  ⟨LOAD n c, a, convE e, s, m⟩.
  [].

(** - [Add x y ⇓[e] Num (n + n')]: *)

  begin
    ⟨c, Num' (n + n'), convE e, s, m⟩.
  ⊑ {auto}
    ⟨c, Num' (n + n'), convE e, s, m[r:=NUM n]⟩ .
  <== { apply vm_add }
    ⟨ADD r c, Num' n', convE e, s, m[r:=NUM n]⟩ .
  <|= { apply IHE2 }
      ⟨comp y (next r) (ADD r c), Num' n, convE e, s, m[r:=NUM n]⟩ .
  <== { apply vm_store }
      ⟨STORE r (comp y (next r) (ADD r c)), Num' n, convE e, s, m⟩.
  <|= { apply IHE1 }
      ⟨comp x r (STORE r (comp y (next r) (ADD r c))), a, convE e, s, m⟩.
  [].

(** - [Var i ⇓[e] v] *)

  begin
    ⟨c, conv v, convE e , s, m⟩.
  <== {apply vm_lookup; unfold convE; rewrite nth_map; rewr_assumption}
      ⟨LOOKUP i c, a , convE e, s, m ⟩.
   [].

(** - [Abs x ⇓[e] Clo x e] *)

  begin
    ⟨c, Clo' (comp x (next first) RET) (convE e), convE e, s, m ⟩.
  <== { apply vm_fun }
    ⟨ABS (comp x (next first) RET) c, a, convE e, s, m ⟩.
  [].

(** - [App x y ⇓[e] x''] *)

  begin
    ⟨c, conv x'', convE e, s, m ⟩.
  <== { apply vm_ret }
      ⟨RET, conv x'', convE (y' :: e'), m :: s, empty[first:=CLO c (convE e)]⟩.
  <|= {apply  IHE3}
      ⟨comp x' (next first) RET, conv y', convE (y' :: e'), m :: s, empty[first:=CLO c (convE e)]⟩.
  = {auto}
      ⟨comp x' (next first) RET, conv y', conv y' :: convE e', m::s, empty[first:=CLO c (convE e)]⟩.
  ⊑ {auto with memory}
      ⟨comp x' (next first) RET, conv y', conv y' :: convE e', m[r:=CLO (comp x' (next first) RET) (convE e')]::s, empty[first:=CLO c (convE e)]⟩.
  <== {apply vm_call}
      ⟨APP r c, conv y', convE e, s, m[r:=CLO (comp x' (next first) RET) (convE e')]⟩.
  <|= {apply IHE2}
      ⟨comp y (next r) (APP r c), (Clo' (comp x' (next first) RET) (convE e')), convE e, s, m[r:=CLO (comp x' (next first) RET) (convE e')]⟩.
  <== { apply vm_stc }
    ⟨STC r (comp y (next r) (APP r c)), (Clo' (comp x' (next first) RET) (convE e')), convE e, s, m⟩.
  = {auto}
    ⟨STC r (comp y (next r) (APP r c)), conv (Clo x' e'), convE e, s, m ⟩.
  <|= { apply IHE1 }
    ⟨comp x r (STC r (comp y (next r) (APP r c))), a, convE e, s, m ⟩.
  [].
Qed.


(** Specification of the whole compiler *)

Theorem spec' x a (e : Env) s v : x ⇓[e] v ->
                                ⟨compile x, a, convE e, s, empty⟩  =|> ⟨HALT , conv v , convE e, s, empty⟩.
Proof.
  intros E.
  begin
    ⟨HALT , conv v , convE e, s, empty⟩.
  <|= {apply spec; auto using empty_mem_free}
      ⟨comp x first HALT, a, convE e, s, empty⟩.
  [].
Qed.


(** * Soundness *)

Lemma determ_vm : determ VM.
  intros C C1 C2 V. induction V; intro V'; inversion V'; subst; congruence.
Qed.
  

Definition terminates (p : Expr) : Prop := exists r, p ⇓[nil] r.

Theorem sound p a C : terminates p -> ⟨compile p, a, nil, nil, empty⟩ =>>! C -> 
                          exists v m, C = ⟨HALT , conv v, nil, nil, m⟩ /\ p ⇓[nil] v.
Proof.
  unfold terminates. intros T M. destruct T as [v T].
  pose (spec' p a nil nil v T) as H'.
  unfold Reach in *. repeat autodestruct.
  pose (determ_trc determ_vm) as D.
  unfold determ in D. inversion H0.  inversion H7.  subst. exists v. eexists. split. eapply D. apply M. split.
  unfold comp.
  simpl in *. apply H. intro Contra. destruct Contra.
  inversion H1. assumption.
Qed.

End Lambda.
