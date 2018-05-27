(** Calculation for the lambda calculus + arithmetic + exceptions. *)

Require Import List.
Require Import ListIndex.
Require Import Tactics.
Require Import Coq.Program.Equality.
Module Lambda (mem : TruncMem).
Module Mem := TruncMemTheory mem.
Import Mem.


(** * Syntax *)

Inductive Expr : Set := 
| Val : nat -> Expr 
| Add : Expr -> Expr -> Expr
| Var : nat -> Expr
| Abs : Expr -> Expr
| App : Expr -> Expr -> Expr
| Throw : Expr
| Catch : Expr -> Expr -> Expr.

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

Inductive eval : Expr -> Env -> option Value -> Prop :=
| eval_val e n : Val n ⇓[e] Some (Num n)
| eval_add e x y m n : x ⇓[e] Some (Num m) -> y ⇓[e] Some (Num n) -> Add x y ⇓[e] Some (Num (m + n))
| eval_var e i v : nth e i = Some v -> Var i ⇓[e] Some v
| eval_abs e x : Abs x ⇓[e] Some (Clo x e)
| eval_app e e' x x' x'' y y' : x ⇓[e] Some (Clo x' e') -> y ⇓[e] Some y' -> x' ⇓[y' :: e'] Some x'' -> App x y ⇓[e] Some x''
| eval_throw e : Throw ⇓[e] None
| eval_catch_fail e x h v v' : x ⇓[e] v -> h ⇓[e] v' ->
                               Catch x h ⇓[e]
                                     match v with
                                      | None => v'
                                      | Some v'' => Some v''
                                      end
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
| THROW : Code
| UNMARK : Code -> Code
| MARK : adr -> Code -> Code -> Code
| HALT : Code.

Fixpoint comp' (e : Expr) (r : adr) (c : Code) : Code :=
  match e with
    | Val n => LOAD n c
    | Add x y => comp' x r (STORE r (comp' y (next r) (ADD r c)))
    | Var i => LOOKUP i c
    | App x y => comp' x r (STORE r (comp' y (next r) (APP r (POP c))))
    | Abs x => ABS (comp' x (next adr0) RET) c
    | Throw => THROW
    | Catch e1 e2 => MARK r (comp' e2 r c) (comp' e1 (next r) (UNMARK c))
  end.

Definition comp (e : Expr) : Code := comp' e adr0 HALT.

(** * Virtual Machine *)

Inductive Value' : Set :=
| Num' : nat -> Value'
| Clo' : Code -> list Value' -> Value'
| Exc' : Value'.

Definition Env' := list Value'.

Definition Han := option adr.


Inductive Elem : Set :=
| VAL : Value' -> Elem 
| CLO : Code -> Env' -> Elem
| HAN : Code -> Env' -> Han -> Elem
.

Notation empty := (empty_mem Elem).

Definition Stack : Type := list (Mem Elem).

Inductive Conf' : Type := 
| conf : Code -> Value' -> Env' -> Han -> Conf'
| fail : Han -> Conf'.

Definition Conf : Type := Conf' * Stack * Mem Elem.

Notation "⟨ x , y , z , w , k , s ⟩" := (conf x y z w, k, s).
Notation "⟪ x , k , s ⟫" := (fail x, k, s).


Reserved Notation "x ==> y" (at level 80, no associativity).
Inductive VM : Conf -> Conf -> Prop :=
 | vm_push n c s a e k h :  ⟨LOAD n c, a, e, h, k, s⟩ ==> ⟨c, Num' n, e, h, k, s⟩
 | vm_pop c s s' a e k h :  ⟨POP c, a, e, h, s' :: k, s⟩ ==> ⟨c, a, e, h, k, s'⟩
 | vm_add c m n r s e k h : s[r] = VAL (Num' m) -> ⟨ADD r c, Num' n, e, h, k, s⟩
                                                 ==> ⟨c, Num'(m + n), e, h, k, s⟩
 | vm_store c v r s e k h : ⟨STORE r c, v, e, h, k, s⟩
                        ==> ⟨c, v, e, h, k, s[r:=VAL v]⟩
 | vm_lookup e i c v a s k h : nth e i = Some v -> ⟨LOOKUP i c, a, e, h, k, s⟩ ==> ⟨c, v, e, h, k, s⟩
 | vm_env a c e e' s k h : s[adr0] = CLO c e -> ⟨RET, a, e', h, k, s⟩ ==> ⟨c, a, e, h, k, s⟩
 | vm_app c c' e e' v r s k h :
     s[r]=VAL (Clo' c' e') ->
     ⟨APP r c, v, e, h, k,s⟩ ==> ⟨c', Num' 0, v :: e', h, truncate r s :: k, empty[adr0:=CLO c e]⟩
 | vm_abs a c c' s e k h : ⟨ABS c' c, a, e, h, k, s⟩ ==> ⟨c, Clo' c' e, e, h, k, s⟩
 | vm_throw a e h k s : ⟨THROW, a, e, h, k, s⟩ ==> ⟪h, k, s⟫
 | vm_fail p p' s c k e : s[p] = HAN c e p' -> ⟪ Some p, k, s⟫ ==> ⟨c, Num' 0, e, p',k, s⟩
 | vm_unmark p p' s a c c' e e' k : s[p] = HAN c' e' p' -> ⟨UNMARK c, a, e, Some p, k, s⟩ ==> ⟨c, a, e, p', k, s⟩
 | vm_mark p r s a c c' e k : ⟨MARK r c' c, a, e, p, k, s⟩ ==> ⟨c, a, e, Some r, k, s[r:= HAN c' e p]⟩
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
 | cle_mem  c a e k k' s s' h : stackle k k' -> s ≤ s' -> cle ⟨ c , a , e , h, k, s ⟩ ⟨ c , a , e, h , k', s' ⟩.

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
Admitted.
Lemma preorder : is_preorder cle.
prove_preorder. Admitted.
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

Theorem spec p v e r c a s k h :
  freeFrom r s ->  p ⇓[e] v ->
  ⟨comp' p r c, a, convE e, h, k, s⟩ =|> match v with
                                         | None => ⟪ h , k , s ⟫
                                         | Some v' => ⟨c , conv v', convE e, h, k, s⟩
                                         end.

(** Setup the induction proof *)

Proof.
  intros F E.
  generalize dependent c.
  generalize dependent a.
  generalize dependent s.
  generalize dependent r.
  generalize dependent k.
  generalize dependent h.
  induction E;intros.

(** Calculation of the compiler *)

(** - [Val n ⇓[e] Num n]: *)

  begin
  ⟨c, Num' n , convE e, h, k, s⟩.
  <== { apply vm_push }
  ⟨LOAD n c, a, convE e, h, k, s⟩.
  [].

(** - [Add x y ⇓[e] Num (m + n)]: *)

  begin
    ⟨c, Num' (m + n), convE e, h, k, s⟩.
  ≤ {auto}
    ⟨c, Num' (m + n), convE e, h, k, s[r:=VAL (Num' m)]⟩ .
  <== { apply vm_add }
    ⟨ADD r c, Num' n, convE e, h, k, s[r:=VAL (Num' m)]⟩ .
  <|= { apply IHE2 }
      ⟨comp' y (next r) (ADD r c), Num' m, convE e, h, k, s[r:=VAL (Num' m)]⟩ .
  <== { apply vm_store }
      ⟨STORE r (comp' y (next r) (ADD r c)), Num' m, convE e, h, k, s⟩.
  <|= { apply IHE1 }
      ⟨comp' x r (STORE r (comp' y (next r) (ADD r c))), a, convE e, h, k, s⟩.
  [].

(** - [Var i ⇓[e] v] *)

  begin
    ⟨c, conv v, convE e, h, k, s⟩.
  <== {apply vm_lookup; unfold convE; rewrite nth_map; rewr_assumption}
      ⟨LOOKUP i c, a , convE e, h, k, s ⟩.
   [].

(** - [Abs x ⇓[e] Clo x e] *)

  begin
    ⟨c, Clo' (comp' x (next adr0) RET) (convE e), convE e, h, k, s ⟩.
  <== { apply vm_abs }
    ⟨ABS (comp' x (next adr0) RET) c, a, convE e, h, k, s ⟩.
  [].

(** - [App x y ⇓[e] x''] *)

  begin
    ⟨c, conv x'', convE e, h, k, s ⟩.
  <== { apply vm_pop }
    ⟨POP c, conv x'', convE e, h, s :: k, empty[adr0:=CLO (POP c) (convE e)] ⟩.
  <== { apply vm_env }
    ⟨RET, conv x'', convE (y' :: e'), h, s :: k, empty[adr0:=CLO (POP c) (convE e)]⟩.
  <|= {apply  IHE3}
      ⟨comp' x' (next adr0) RET, Num' 0, convE (y' :: e'), h, s :: k, empty[adr0:=CLO (POP c) (convE e)]⟩.
  = {auto}
      ⟨comp' x' (next adr0) RET, Num' 0, conv y' :: convE e', h, s::k, empty[adr0:=CLO (POP c) (convE e)]⟩.
  <== {apply_eq vm_app;try rewrite truncate_set}
      ⟨APP r (POP c), conv y', convE e, h, k, s[r:=VAL (Clo' (comp' x' (next adr0) RET) (convE e'))]⟩.
  <|= {apply IHE2}
      ⟨comp' y (next r) (APP r (POP c)), (Clo' (comp' x' (next adr0) RET) (convE e')), convE e, h, k, s[r:=VAL (Clo' (comp' x' (next adr0) RET) (convE e'))]⟩.
  <== { apply vm_store }
    ⟨STORE r (comp' y (next r) (APP r (POP c))), (Clo' (comp' x' (next adr0) RET) (convE e')), convE e, h, k, s⟩.
  = {auto}
    ⟨STORE r (comp' y (next r) (APP r (POP c))), conv (Clo x' e'), convE e, h, k, s ⟩.
  <|= { apply IHE1 }
    ⟨comp' x r (STORE r (comp' y (next r) (APP r (POP c)))), a, convE e, h, k, s ⟩.
  [].

    begin
      ⟪h, k, s⟫.
    <== {apply vm_throw}
        ⟨ THROW, a, convE e, h, k, s⟩.
    [].

    begin
      match match v with
            | Some v'' => Some v''
            | None => v'
            end with
      | Some v'0 => ⟨ c, conv v'0, convE e, h0, k, s ⟩
      | None => ⟪ h0, k, s ⟫
      end.
    = {eauto}
      match v with
            | Some v'' => ⟨ c, conv v'', convE e, h0, k, s ⟩
            | None => match v' with
                      | Some v'' => ⟨ c, conv v'', convE e, h0, k, s ⟩
                      | None => ⟪ h0, k, s ⟫
                      end 
      end.
    <|= {apply IHE2}
      match v with
            | Some v'' => ⟨ c, conv v'', convE e, h0, k, s ⟩
            | None => ⟨ comp' h r c, Num' 0, convE e, h0, k, s ⟩
      end.
    ≤ {eauto}
      match v with
            | Some v'' => ⟨ c, conv v'', convE e, h0, k, s ⟩
            | None => ⟨ comp' h r c, Num' 0, convE e, h0, k, s[r:= HAN (comp' h  r c) (convE e) h0] ⟩
      end.
    <== {apply vm_fail}
      match v with
            | Some v'' => ⟨ c, conv v'', convE e, h0, k, s ⟩
            | None => ⟪ Some r, k, s[r:= HAN (comp' h  r c) (convE e) h0] ⟫
      end.
    ≤ {eauto}
      match v with
            | Some v'' => ⟨ c, conv v'', convE e, h0, k, s[r:= HAN (comp' h  r c) (convE e) h0] ⟩
            | None => ⟪ Some r, k, s[r:= HAN (comp' h  r c) (convE e) h0] ⟫
      end.
    <== {eapply vm_unmark}
      match v with
            | Some v'' => ⟨ UNMARK c, conv v'', convE e, Some r, k, s[r:= HAN (comp' h r c) (convE e) h0] ⟩
            | None => ⟪ Some r, k, s[r:= HAN (comp' h  r c) (convE e) h0] ⟫
      end.
    <|= {apply IHE1}
        ⟨ comp' x (next r) (UNMARK c), a, convE e, Some r, k, s[r:= HAN (comp' h  r c) (convE e) h0] ⟩.
    <== {apply vm_mark}
        ⟨ MARK r (comp' h  r c) (comp' x (next r) (UNMARK c)), a, convE e, h0, k, s ⟩.
    [].
    
Qed.
  
(** * Soundness *)

Lemma determ_vm : determ VM.
  intros C C1 C2 V. induction V; intro V'; inversion V'; subst; congruence.
Qed.
  

Definition terminates (p : Expr) : Prop := exists r, p ⇓[nil] r.

Theorem sound p a s h C : freeFrom adr0 s -> terminates p -> ⟨comp p, a, nil, h, nil, s⟩ =>>! C -> 
                          exists v s', C = ⟨HALT , conv v, nil, h, nil, s'⟩ /\ p ⇓[nil] Some v.
Proof.
  unfold terminates. intros F T M. destruct T as [v T].
  pose (spec p v nil adr0 HALT a s nil h F T) as H'.
  unfold Reach in *. repeat autodestruct.
  pose (determ_trc determ_vm) as D.
  unfold determ in D. inversion H0. destruct v; try inversion H1. subst.  inversion H2. subst.
  exists v. eexists. split. eapply D. apply M. split.
  unfold comp.
  simpl in *. apply H. intro Contra. destruct Contra.
  inversion H4. assumption.
Qed.

End Lambda.
