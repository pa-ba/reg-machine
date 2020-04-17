(** Calculation for the lambda calculus + arithmetic + exceptions. *)

Require Import List.
Require Import ListIndex.
Require Import Tactics.
Require Import Coq.Program.Equality.
Module Lambda (Import mem : TruncMem).


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
data Value =  Num Int | Fun (Value -> Maybe Value)


eval ::  Expr -> Env -> Maybe Value
eval (Val n) e   = Some (Num n)
eval (Add x y) e = case eval x e of
                     Just (Num n) -> case eval y e of
                                       Just (Num m) -> Num (n+m)
                                       _ -> Nothing
                     _ -> Nothing
eval (Var i) e   = if i < length  e then Just (e !! i) else Nothing
eval (Abs x) e   = Just (Fun (\v -> eval x (v:e)))
eval (App x y) e = case eval x e of
                     Just (Fun f) -> eval y e >>= f
                     _ -> Nothing
                     
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
| eval_add e x y m n : x ⇓[e] m -> y ⇓[e] n 
                       -> Add x y ⇓[e] (match m, n with
                                          | Some (Num m'), Some (Num n') => Some (Num (m' + n'))
                                          | _,_ => None
                                        end  )
| eval_throw e : Throw ⇓[e] None
| eval_catch e x y m n : x ⇓[e] m -> y ⇓[e] n 
                       -> Catch x y ⇓[e] (match m with
                                            | None => n
                                            | _ => m
                                        end  )
| eval_var e i : Var i ⇓[e] nth e i
| eval_abs e x : Abs x ⇓[e] Some (Clo x e)
| eval_app e  x x'' y  x' e' y' : x ⇓[e] Some (Clo x' e') -> y ⇓[e] Some y' -> x' ⇓[y' :: e'] x''
                                -> App x y ⇓[e] x''
| eval_app_fail x x' y y' e : x ⇓[e] x' -> y ⇓[e] y' -> 
                              (x' = None \/ exists n, x' = Some (Num n) \/ y' = None) -> 
                              App x y ⇓[e] None
where "x ⇓[ e ] y" := (eval x e y).

(** * Compiler *)

Inductive Code : Set :=
| LOAD : nat -> Code -> Code
| ADD : Reg -> Code -> Code
| STORE : Reg -> Code -> Code
| STC : Reg -> Code -> Code
| LOOKUP : nat -> Code -> Code
| RET : Code
| APP : Reg -> Code -> Code
| ABS : Code -> Code -> Code
| THROW : Code
| UNMARK : Code -> Code
| MARK : Reg -> Code -> Code -> Code
| HALT : Code.

Fixpoint comp (e : Expr) (r : Reg) (c : Code) : Code :=
  match e with
    | Val n => LOAD n c
    | Add x y => comp x r (STORE r (comp y (next r) (ADD r c)))
    | Var i => LOOKUP i c
    | App x y => comp x r (STC r (comp y (next r) (APP r c)))
    | Abs x => ABS (comp x (next first) RET) c
    | Throw => THROW
    | Catch e1 e2 => MARK r (comp e2 r c) (comp e1 (next r) (UNMARK c))
  end.

Definition compile (e : Expr) : Code := comp e first HALT.

(** * Virtual Machine *)

Inductive Value' : Set :=
| Num' : nat -> Value'
| Clo' : Code -> list Value' -> Value'
| Exc' : Value'.

Definition Env' := list Value'.

Definition Han := option Reg.


Inductive RVal : Set :=
| VAL : nat -> RVal 
| CLO : Code -> Env' -> RVal
| HAN : Code -> Env' -> Han -> RVal
.

Inductive SElem :=
| MEM : Mem RVal -> SElem
| MARKED : SElem.

Definition Lam : Type := list SElem.

Inductive Conf' : Type := 
| conf : Code -> Value' -> Env' -> Han -> Conf'
| fail : Han -> Conf'.

Definition Conf : Type := Conf' * Lam * Mem RVal.

Notation "⟨ x , y , z , w , k , s ⟩" := (conf x y z w, k, s).
Notation "⟪ x , k , s ⟫" := (fail x, k, s).

Definition empty := (@empty RVal).

Reserved Notation "x ==> y" (at level 80, no associativity).
Inductive VM : Conf -> Conf -> Prop :=
 | vm_load n c s a e k h :  ⟨LOAD n c, a, e, h, k, s⟩ ==> ⟨c, Num' n, e, h, k, s⟩
 | vm_add c m n r s e k h : s[r] = VAL m -> ⟨ADD r c, Num' n, e, h, k, s⟩
                                                     ==> ⟨c, Num'(m + n), e, h, k, s⟩
 | vm_add_fail s c c' e e' h r k : ⟨ADD r c, Clo' c' e', e, h, k, s⟩ ==> ⟪h, k, s⟫
 | vm_store c n r s e k h : ⟨STORE r c, Num' n, e, h, k, s⟩
                              ==> ⟨c, Num' n, e, h, k, s[r:=VAL n]⟩
 | vm_store_fail c r s e k h c' e' : ⟨STORE r c, Clo' c' e', e, h, k, s⟩
                                       ==>  ⟪h, k, s⟫
 | vm_stc c c' e' r s e k h : ⟨STC r c, Clo' c' e', e, h, k, s⟩
                                   ==> ⟨c, Clo' c' e', e, h, k, s[r:=CLO c' e']⟩
 | vm_stc_fail c n r s e k h : ⟨STC r c, Num' n, e, h, k, s⟩
                              ==> ⟪h, k, s⟫
 | vm_lookup e i c v a s k h : nth e i = Some v -> ⟨LOOKUP i c, a, e, h, k, s⟩ ==> ⟨c, v, e, h, k, s⟩
 | vm_lookup_fail e i c a s k h : nth e i = None -> ⟨LOOKUP i c, a, e, h, k, s⟩ ==> ⟪h, k, s⟫
 | vm_ret a c e e' s s' k h : s[first] = CLO c e -> ⟨RET, a, e', h, MEM s' :: k, s⟩ ==> ⟨c, a, e, h, k, s'⟩
 | vm_app c c' e e' v r s k h :
     s[r]=CLO c' e' ->
     ⟨APP r c, v, e, h, k,s⟩ ==> ⟨c', Num' 0, v :: e', h, MEM (truncate r s) :: k, empty[first:=CLO c e]⟩
 | vm_abs a c c' s e k h : ⟨ABS c' c, a, e, h, k, s⟩ ==> ⟨c, Clo' c' e, e, h, k, s⟩
 | vm_throw a e h k s : ⟨THROW, a, e, h, k, s⟩ ==> ⟪h, k, s⟫
 | vm_fail p p' s c k e : s[p] = HAN c e p' -> ⟪ Some p, MARKED :: k, s⟫ ==> ⟨c, Num' 0, e, p', k, s⟩
 | vm_fail_pop p s s' k : ⟪ p, MEM s' :: k, s⟫ ==> ⟪ p, k, s'⟫
 | vm_unmark p p' s a c c' e e' k : s[p] = HAN c' e' p' -> ⟨UNMARK c, a, e, Some p, MARKED :: k, s⟩ ==> ⟨c, a, e, p', k, s⟩
 | vm_mark p r s a c c' e k : ⟨MARK r c' c, a, e, p, k, s⟩ ==> ⟨c, a, e, Some r, MARKED :: k, s[r:= HAN c' e p]⟩
where "x ==> y" := (VM x y).

(** Conversion functions from semantics to VM *)

Fixpoint conv (v : Value) : Value' :=
  match v with
    | Num n => Num' n
    | Clo x e => Clo' (comp x (next first) RET) (map conv e)
  end.

Definition convE : Env -> Env' := map conv.

Inductive stackle : Lam -> Lam -> Prop :=
| stackle_empty : stackle nil nil
| stackle_cons_mem s s' k k' : s ⊑ s' -> stackle k k' -> stackle (MEM s :: k) (MEM s' :: k')
| stackle_cons_han k k' : stackle k k' -> stackle (MARKED :: k) (MARKED :: k').

Hint Constructors stackle : memory.

Lemma stackle_refl k : stackle k k.
Proof.
  induction k; try destruct a; constructor; auto with memory.
Qed.

Lemma stackle_trans k1 k2 k3 : stackle k1 k2 -> stackle k2 k3 -> stackle k1 k3.
Proof.
  intros L1. generalize k3. induction L1; intros k3' L2; solve[assumption| inversion L2; subst; constructor; eauto with memory].
Qed.

Hint Resolve stackle_refl stackle_trans : core.

Inductive cle : Conf -> Conf -> Prop :=
 | cle_mem  f k k' s s' : stackle k k' -> s ⊑ s' -> cle (f, k, s)  (f , k', s' ).

Hint Constructors cle : core.

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

Theorem spec p v e r c a s k h :
  freeFrom r s ->  p ⇓[e] v ->
  ⟨comp p r c, a, convE e, h, k, s⟩ =|> match v with
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
  <== { apply vm_load }
  ⟨LOAD n c, a, convE e, h, k, s⟩.
  [].

(** - [Add x y ⇓[e] Num (m + n)]: *)

  begin
      match  m with
        | Some (Num m') => match n with
                           | Some (Num n') => ⟨ c, Num' (m' + n'), convE e, h, k, s ⟩
                           | _ => ⟪ h, k, s ⟫
                           end
        | _ => ⟪ h, k, s ⟫
      end.
  ⊑ {auto}
      match  m with
        | Some (Num m') => match n with
                           | Some (Num n') => ⟨ c, Num' (m' + n'), convE e, h, k, s[r:=VAL m'] ⟩
                           | _ => ⟪ h, k, s[r:=VAL m'] ⟫
                           end
        | _ => ⟪ h, k, s ⟫
      end.
  <== { apply vm_add }
      match  m with
      | Some (Num m') => match n with
                         | Some (Num n') => ⟨ADD r c, Num' n', convE e, h, k, s[r:=VAL m'] ⟩
                         | _ => ⟪ h, k, s[r:=VAL m'] ⟫
                         end
        | _ => ⟪ h, k, s ⟫
      end.
  <== { apply vm_add_fail }
      match  m with
      | Some (Num m') => match n with
                         | Some v => ⟨ADD r c, conv v, convE e, h, k, s[r:=VAL m'] ⟩
                         | None => ⟪ h, k, s[r:=VAL m'] ⟫
                         end
      | _ => ⟪ h, k, s ⟫
      end.
  <|= { apply IHE2 }
      match  m with
      | Some (Num m') => ⟨comp y (next r) (ADD r c), Num' m', convE e, h, k, s[r:=VAL m'] ⟩
      | _ => ⟪ h, k, s ⟫
      end.
  <== { apply vm_store }
      match  m with
      | Some (Num m') => ⟨STORE r (comp y (next r) (ADD r c)), Num' m', convE e, h, k, s ⟩
      | _ => ⟪ h, k, s ⟫
      end.
  <== { apply vm_store_fail }
      match  m with
      | Some v => ⟨STORE r (comp y (next r) (ADD r c)), conv v, convE e, h, k, s ⟩
      | _ => ⟪ h, k, s ⟫
      end.
  <|= { apply IHE1 }
      ⟨comp x r (STORE r (comp y (next r) (ADD r c))), a, convE e, h, k, s⟩.
  [].

  (** - [Throw ⇓[e] None] *)
  
    begin
      ⟪h, k, s⟫.
    <== {apply vm_throw}
        ⟨ THROW, a, convE e, h, k, s⟩.
    [].


    begin
      match m with
            | Some v'' => ⟨ c, conv v'', convE e, h, k, s ⟩
            | None => match n with
                      | Some v'' => ⟨ c, conv v'', convE e, h, k, s ⟩
                      | None => ⟪ h, k, s ⟫
                      end 
      end.
    <|= {apply IHE2}
      match m with
            | Some v'' => ⟨ c, conv v'', convE e, h, k, s ⟩
            | None => ⟨ comp y r c, Num' 0, convE e, h, k, s ⟩
      end.
    ⊑ {eauto}
      match m with
            | Some v'' => ⟨ c, conv v'', convE e, h, k, s ⟩
            | None => ⟨ comp y r c, Num' 0, convE e, h, k, s[r:= HAN (comp y r c) (convE e) h] ⟩
      end.
    <== {apply vm_fail}
      match m with
            | Some v'' => ⟨ c, conv v'', convE e, h, k, s ⟩
            | None => ⟪ Some r, MARKED :: k, s[r:= HAN (comp y r c) (convE e) h] ⟫
      end.
    ⊑ {eauto}
      match m with
            | Some v'' => ⟨ c, conv v'', convE e, h, k, s[r:= HAN (comp y r c) (convE e) h] ⟩
            | None => ⟪ Some r, MARKED :: k, s[r:= HAN (comp y r c) (convE e) h] ⟫
      end.
    <== {eapply vm_unmark}
      match m with
            | Some v'' => ⟨ UNMARK c, conv v'', convE e, Some r, MARKED :: k, s[r:= HAN (comp y r c) (convE e) h] ⟩
            | None => ⟪ Some r, MARKED :: k, s[r:= HAN (comp y r c) (convE e) h] ⟫
      end.
    <|= {apply IHE1}
        ⟨ comp x (next r) (UNMARK c), a, convE e, Some r, MARKED :: k, s[r:= HAN (comp y r c) (convE e) h] ⟩.
    <== {apply vm_mark}
        ⟨ MARK r (comp y r c) (comp x (next r) (UNMARK c)), a, convE e, h, k, s ⟩.
    [].
    

  
(** - [Var i ⇓[e] v] *)

  begin
    match nth e i with
    | Some v' => ⟨c, conv v', convE e, h, k, s⟩
    | None => ⟪ h, k, s ⟫
    end.
  <== {apply vm_lookup_fail; unfold convE; rewrite nth_map; rewr_assumption}
    match nth e i with
    | Some v' => ⟨c, conv v', convE e, h, k, s⟩
    | None => ⟨LOOKUP i c, a , convE e, h, k, s ⟩
    end.
  <== {apply vm_lookup; unfold convE; rewrite nth_map; rewr_assumption}
      ⟨LOOKUP i c, a , convE e, h, k, s ⟩.
   [].

(** - [Abs x ⇓[e] Clo x e] *)

  begin
    ⟨c, Clo' (comp x (next first) RET) (convE e), convE e, h, k, s ⟩.
  <== { apply vm_abs }
    ⟨ABS (comp x (next first) RET) c, a, convE e, h, k, s ⟩.
  [].

(** - [App x y ⇓[e] x''] *)

  begin
    match x'' with
    | Some v' => ⟨ c, conv v', convE e, h, k, s ⟩
    | None => ⟪ h, k, s ⟫
    end.
  <== { apply vm_ret }
      match x'' with
      | Some v' => ⟨RET, conv v', convE (y' :: e'), h, MEM s :: k, empty[first:=CLO c (convE e)]⟩
      | None => ⟪ h, k, s ⟫
      end.
  <== { apply vm_fail_pop }
      match x'' with
      | Some v' => ⟨RET, conv v', convE (y' :: e'), h, MEM s :: k, empty[first:=CLO c (convE e)]⟩
      | None => ⟪ h, MEM s :: k, empty[first:=CLO c (convE e)] ⟫
      end.
  <|= {apply IHE3}
      ⟨comp x' (next first) RET, Num' 0, convE (y' :: e'), h, MEM s :: k, empty[first:=CLO c (convE e)]⟩.
  = {auto}
      ⟨comp x' (next first) RET, Num' 0, conv y' :: convE e', h, MEM s:: k, empty[first:=CLO c (convE e)]⟩.
  <== {apply_eq vm_app;try rewrite truncate_set}
      ⟨APP r c, conv y', convE e, h, k, s[r:=CLO (comp x' (next first) RET) (convE e')]⟩.
  <|= {apply IHE2}
      ⟨comp y (next r) (APP r c), (Clo' (comp x' (next first) RET) (convE e')), convE e, h, k, s[r:=CLO (comp x' (next first) RET) (convE e')]⟩.
  <== { apply vm_stc }
    ⟨STC r (comp y (next r) (APP r c)), (Clo' (comp x' (next first) RET) (convE e')), convE e, h, k, s⟩.
  = {auto}
    ⟨STC r (comp y (next r) (APP r c)), conv (Clo x' e'), convE e, h, k, s ⟩.
  <|= { apply IHE1 }
    ⟨comp x r (STC r (comp y (next r) (APP r c))), a, convE e, h, k, s ⟩.
  [].

  begin
    ⟪ h, k, s ⟫.
  = {auto}
  match x' with
  | Some (Clo x'' e') => match y' with 
                         | Some v => ⟨ APP r c, conv v, convE e, h, k, s[ r := CLO (comp x'' (next first) RET) (map conv e')] ⟩
                         | None => ⟪h, k, s ⟫
                         end
  | _ => ⟪h, k, s ⟫
  end.
  ⊑ {auto}
  match x' with
  | Some (Clo x'' e') => match y' with 
                         | Some v => ⟨ APP r c, conv v, convE e, h, k, s[ r := CLO (comp x'' (next first) RET) (map conv e')] ⟩
                         | None => ⟪h, k, s[ r := CLO (comp x'' (next first) RET) (map conv e')] ⟫
                         end
  | _ => ⟪h, k, s ⟫
  end.
  <|= {apply IHE2}
  match x' with
  | Some (Clo x'' e') => ⟨comp y (next r) (APP r c), conv (Clo x'' e'), convE e, h, k, s[ r := CLO (comp x'' (next first) RET) (map conv e')] ⟩
  | _ => ⟪h, k, s ⟫
  end.
  = {reflexivity}
    match x' with
    | Some v => match v with
                | Clo x'' e' => ⟨comp y (next r) (APP r c), conv (Clo x'' e'), convE e, h, k,
                                 s[ r := CLO (comp x'' (next first) RET) (map conv e')] ⟩
                | _ => ⟪h, k, s ⟫
                end
    | _ => ⟪h, k, s ⟫
    end.
  <== {apply vm_stc}
    match x' with
    | Some v => match v with
                | Clo x'' e' => ⟨STC r (comp y (next r) (APP r c)), conv (Clo x'' e'), convE e, h, k, s ⟩
                | _ => ⟪h, k, s ⟫
                end
    | _ => ⟪h, k, s ⟫
    end.
  <== {apply vm_stc_fail}
    match x' with
    | Some v => ⟨STC r (comp y (next r) (APP r c)), conv v, convE e, h, k, s ⟩
    | _ => ⟪h, k, s ⟫
    end.
  <|= {apply IHE1}
      ⟨comp x r (STC r (comp y (next r) (APP r c))), a, convE e, h, k, s ⟩.
  [].
  
Qed.
  
(** * Soundness *)

Lemma determ_vm : determ VM.
  intros C C1 C2 V. induction V; intro V'; inversion V'; subst; congruence.
Qed.
  

Definition terminates (p : Expr) : Prop := exists r, p ⇓[nil] Some r.

Theorem sound p a s h C : freeFrom first s -> terminates p -> ⟨compile p, a, nil, h, nil, s⟩ =>>! C -> 
                          exists v s', C = ⟨HALT , conv v, nil, h, nil, s'⟩ /\ p ⇓[nil] Some v.
Proof.
  unfold terminates. intros F T M. destruct T as [v T].
  pose (spec p (Some v) nil first HALT a s nil h F T) as H'.
  unfold Reach in *. repeat autodestruct.
  pose (determ_trc determ_vm) as D.
  unfold determ in D. inversion H0.   inversion H5. subst.
  exists v. eexists. split. eapply D. apply M. split.
  unfold compile.
  simpl in *. apply H. intro Contra. destruct Contra.
  inversion H1. assumption.
Qed.

Example test1 := (Catch (App (Abs (Throw)) (Val 2)) (Val 3)).

Example test1_eval : exists v, test1 ⇓[ nil ] v.
unfold test1.
eexists.
apply eval_catch.
eapply eval_app.
eapply eval_abs.
eapply eval_val.
eapply eval_throw.
eapply eval_val.
Qed.

(* Compute (compile test1). *)

Example test1_vm h : exists s a, ⟨(compile (Catch (App (Abs (Throw)) (Val 2)) (Val 3))), a, nil, h, nil, empty⟩
                     =>> ⟨HALT, a, nil, h, nil, s⟩.
Proof.
  eexists. eexists.
  unfold compile. simpl.
  eapply trc_step_trans'.
  eapply vm_mark.
  eapply trc_step_trans'.
  eapply vm_abs.
  eapply trc_step_trans'.
  eapply vm_stc.
  eapply trc_step_trans'.
  eapply vm_load.
  eapply trc_step_trans'.
  eapply vm_app.
  rewrite get_set. reflexivity.
  eapply trc_step_trans'.
  eapply vm_throw.
  eapply trc_step_trans'.
  eapply vm_fail_pop.
  eapply trc_step_trans'.
  eapply vm_fail. rewrite truncate_set. rewrite get_set. reflexivity. apply freeFrom_set. auto with memory.
  eapply trc_step_trans'.
  eapply vm_load.
  eapply trc_refl.
Qed.


End Lambda.
