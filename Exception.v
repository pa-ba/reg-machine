(** Calculation of the simple arithmetic language. *)

Require Import List.
Require Import Tactics.
Require Import Memory.
Require Import ZArith.

(** * Syntax *)

Inductive Expr : Set := 
| Val : nat -> Expr 
| Add : Expr -> Expr -> Expr
| Throw : Expr 
| Catch : Expr -> Expr -> Expr.

(** * Semantics *)

Fixpoint eval (x: Expr) : option nat :=
  match x with
    | Val n => Some n
    | Add x1 x2 => match eval x1 with
                   | Some m => match eval x2 with
                               | Some n => Some (m + n)
                               | None => None
                               end
                   | None => None
                   end
    | Throw => None
    | Catch x h => match eval x with
                   | Some n => Some n
                   | None => eval h
                   end 
  end.

(** * Compiler *)

Inductive Code : Set :=
| LOAD : nat -> Code -> Code
| ADD : adr -> Code -> Code
| STORE : adr -> Code -> Code
| THROW : Code
| UNMARK : Code -> Code
| MARK : adr -> Code -> Code -> Code
| HALT : Code.

Fixpoint comp' (x : Expr) (r : nat) (c : Code) : Code :=
  match x with
  | Val n => LOAD n c
  | Add e1 e2 => comp' e1 r (STORE r (comp' e2 (r+1) (ADD r c)))
  | Throw => THROW
  | Catch e1 e2 => MARK r (comp' e2 r c) (comp' e1 (r+1) (UNMARK c))
  end.

Definition comp (x : Expr) : Code := comp' x 0 HALT.

Definition Han := option adr.

Inductive Elem : Set :=
| NUM : nat -> Elem
| HAN : Code -> Han -> Elem.

(** * Virtual Machine *)

Inductive Conf : Type :=
| conf : Code -> nat -> Mem Elem -> Han -> Conf
| fail : Mem Elem -> Han -> Conf.

Notation "⟨ x , y , z , p ⟩" := (conf x y z p).
Notation "⟪ x , y ⟫" := (fail x y).

Reserved Notation "x ==> y" (at level 80, no associativity).
Inductive VM : Conf -> Conf -> Prop :=
| vm_load n a c s p : ⟨LOAD n c, a , s, p⟩ ==> ⟨c , n,  s, p⟩ 
| vm_add c s a r n p : get r s = NUM n -> ⟨ADD r c, a , s, p⟩ ==> ⟨c , n + a,  s, p⟩
| vm_store c s a r p : ⟨STORE r c, a , s, p⟩ ==> ⟨c , a,  set r (NUM a) s, p⟩
| vm_throw a s p : ⟨THROW, a , s, p⟩ ==> ⟪s, p⟫
| vm_fail p p' s c : get p s = HAN c p' -> ⟪s, Some p⟫ ==> ⟨c, 0, s, p'⟩
| vm_unmark p p' s a c c' : get p s = HAN c' p' -> ⟨UNMARK c, a, s, Some p⟩ ==> ⟨c, a, s, p'⟩
| vm_mark p r s a c c' : ⟨MARK r c' c, a, s, p⟩ ==> ⟨c, a, set r (HAN c' p) s, Some r⟩
where "x ==> y" := (VM x y).

(** * Calculation *)

(** Boilerplate to import calculation tactics *)

Module VM <: Machine.
Definition Conf := Conf.
Definition Rel := VM.
End VM.
Module VMCalc := Calculation VM.
Import VMCalc.

(** Specification of the compiler *)

Theorem spec e r c p P :
  {a s , ⟨comp' e r c, a, s, p⟩ | P a s }
    =|> {a s s' n, ⟨c , n, s', p⟩ | s =[r] s' /\ P a s /\ eval e = Some n}
    ∪   {a s s', ⟪s', p⟫ | s =[r] s' /\ P a s /\ eval e = None}.


(** Setup the induction proof *)

Ltac lemma1 := first[first [eapply set_eqr|eapply set_get_eqr]; eauto using eqr_sym, eqr_trans; omega|eauto].
Ltac lemma1' := repeat lemma1.

Proof.
  intros.
  generalize dependent c.
  generalize dependent P.
  generalize dependent r.
  generalize dependent p.
  induction e;intros.

(** Calculation of the compiler *)

(** - [x = Val n]: *)

  begin
    ({a s s' n0, ⟨ c, n0, s', p ⟩ | s =[r] s' /\ P a s /\ eval (Val n) = Some n0}
       ∪ {a s s', ⟪ s', p ⟫ | s =[r] s' /\ P a s /\ eval (Val n) = None}).
  ⊇ { eauto }
    ({a s s' , ⟨ c, n, s', p ⟩ | s =[r] s' /\ P a s}).
  <== { apply vm_load }
    ({a s s' , ⟨ LOAD n c, a, s', p ⟩ | s =[r] s' /\ P a s}).
  ⊇ { auto using eqr_refl }
    ({a s , ⟨ LOAD n c, a, s, p ⟩ | P a s}).
  [].

(** - [x = Add x1 x2]: *)

  begin
    ({a s s' n, ⟨ c, n, s', p ⟩ | s =[r] s' /\ P a s /\ eval (Add e1 e2) = Some n}
    ∪ {a s s', ⟪ s', p ⟫ | s =[ r] s' /\ P a s /\ eval (Add e1 e2) = None}).
  ⊇ {eauto}
    ({a s s' m n , ⟨ c, m + n, s', p ⟩ | s =[r] s' /\ P a s /\ eval e1 = Some m /\ eval e2 = Some n}
     ∪ {a s s', ⟪ s', p ⟫ | s =[r] s' /\ P a s /\ eval e1 = None}
     ∪ {a s s', ⟪ s', p ⟫ | s =[r] s' /\ P a s /\ (exists m , eval e1 = Some m) /\ eval e2 = None}
    ).
  ⊇ {eauto}
    ({a s s' m n , ⟨ c, m + n, s', p ⟩ | s =[r] s' /\ get r s' = NUM m /\ P a s /\ eval e1 = Some m /\ eval e2 = Some n}
     ∪ {a s s', ⟪ s', p ⟫ | s =[r] s' /\ P a s /\ eval e1 = None}
     ∪ {a s s', ⟪ s', p ⟫ | s =[r] s' /\ P a s /\ (exists m , eval e1 = Some m) /\ eval e2 = None}
    ).
  <== { apply vm_add}
    ({a s s' m n , ⟨ ADD r c, n, s', p ⟩ | s =[r] s' /\ get r s' = NUM m /\ P a s /\ eval e1 = Some m /\ eval e2 = Some n}
     ∪ {a s s', ⟪ s', p ⟫ | s =[r] s' /\ P a s /\ eval e1 = None}
     ∪ {a s s', ⟪ s', p ⟫ | s =[r] s' /\ P a s /\ (exists m , eval e1 = Some m) /\ eval e2 = None}
    ).
  ⊇ { eauto }
    ({m s s' n , ⟨ ADD r c, n, s', p ⟩ | s =[r] s' /\ get r s' = NUM m /\ (exists a, P a s) /\ eval e1 = Some m /\ eval e2 = Some n}
     ∪ {m s s', ⟪ s', p ⟫ | s =[r] s' /\ (exists a, P a s) /\  get r s' = NUM m /\ eval e1 = Some m /\ eval e2 = None}
     ∪ {a s s', ⟪ s', p ⟫ | s =[r] s' /\ P a s /\ eval e1 = None}
    ).
  ⊇ {lemma1}
    ({m s'' s' n , ⟨ ADD r c, n, s', p ⟩ | s'' =[r+1] s' /\
        (exists a s, s'' =[r+1] set r (NUM m) s /\ P a s /\ eval e1 = Some m) /\ eval e2 = Some n}
     ∪ {m s'' s', ⟪ s', p ⟫ | s'' =[r+1] s' /\
        (exists a s, s'' =[r+1] set r (NUM m) s /\ P a s /\ eval e1 = Some m) /\ eval e2 = None}
     ∪ {a s s', ⟪ s', p ⟫ | s =[r] s' /\ P a s /\ eval e1 = None} ).  
  <|= { apply IHe2}
      ({m s'', ⟨comp' e2 (r+1) (ADD r c), m, s'', p ⟩ | exists a s, s'' =[r+1] set r (NUM m) s /\
                                                                    P a s /\ eval e1 = Some m}
         ∪ {a s s', ⟪ s', p ⟫ | s =[r] s' /\ P a s /\ eval e1 = None}).
  ⊇ {eauto}
    ({a m s s'', ⟨comp' e2 (r+1) (ADD r c), m, set r (NUM m) s'', p ⟩ | 
      set r (NUM m) s'' =[r+1] set r (NUM m) s /\ P a s /\ eval e1 = Some m}
      ∪ {a s s', ⟪ s', p ⟫ | s =[r] s' /\ P a s /\ eval e1 = None}).
  ⊇ { eauto using set_eqr_incr, eqr_sym }
    ({a s s'' m, ⟨comp' e2 (r+1) (ADD r c), m, set r (NUM m) s'', p ⟩ | s'' =[r]  s /\ P a s /\ eval e1 = Some m}
      ∪ {a s s', ⟪ s', p ⟫ | s =[r] s' /\ P a s /\ eval e1 = None}).
  <== { apply vm_store}
    ({a s s'' m, ⟨STORE r (comp' e2 (r+1) (ADD r c)), m,  s'', p ⟩ | s'' =[r]  s /\ P a s /\ eval e1 = Some m}
      ∪ {a s s', ⟪ s', p ⟫ | s =[r] s' /\ P a s /\ eval e1 = None}).
  ⊇ { eauto using eqr_sym}
    ({a s s'' m, ⟨STORE r (comp' e2 (r+1) (ADD r c)), m,  s'', p ⟩ | s =[r]  s'' /\ P a s /\ eval e1 = Some m}
      ∪ {a s s', ⟪ s', p ⟫ | s =[r] s' /\ P a s /\ eval e1 = None}).
  <|= { apply IHe1}
    ({a s, ⟨comp' e1 r (STORE r (comp' e2 (r+1) (ADD r c))), a, s, p⟩ | P a s }).
  [].

  (** - [x = Throw]: *)
  begin
    ({a s s' n, ⟨ c, n, s', p ⟩ | s =[ r] s' /\ P a s /\ eval Throw = Some n}
       ∪ {a s s', ⟪ s', p ⟫ | s =[ r] s' /\ P a s /\ eval Throw = None}).
  ⊇ {eauto}
    ({a s s', ⟪ s', p ⟫ | s =[ r] s' /\ P a s}).
  <== {eapply vm_throw}
    ({a s s', ⟨THROW, a, s', p⟩ | s =[ r] s' /\ P a s}).
  ⊇ {eauto using eqr_refl}
    ({a s , ⟨THROW, a, s, p⟩ | P a s}).
  [].

  (** - [x = Catch e1 e2]: *)
  begin
  ({a s s' n, ⟨ c, n, s', p ⟩ | s =[r] s' /\ P a s /\ eval (Catch e1 e2) = Some n}
  ∪ {a s s', ⟪ s', p ⟫ | s =[r] s' /\ P a s /\ eval (Catch e1 e2) = None}).
  ⊇ {eauto}
  ({a s s' n, ⟨ c, n, s', p ⟩ | s =[r] s' /\ P a s /\ eval e1 = Some n}
     ∪ {a s s' n, ⟨ c, n, s', p ⟩ | s =[r] s' /\ P a s /\ eval e1 = None /\ eval e2 = Some n}
     ∪ {a s s', ⟪ s', p ⟫ | s =[r] s' /\ P a s /\ eval e1 = None /\ eval e2 = None}).
  ⊇ {eauto using eqr_trans}
  ({a s s' n, ⟨ c, n, s', p ⟩ | s =[r] s' /\ P a s /\ eval e1 = Some n}
     ∪ ({ (a: nat) s'' s' n, ⟨ c, n, s', p ⟩ | s'' =[r] s' /\ (a = 0 /\ exists a s, s =[r] s'' /\ P a s /\ eval e1 = None) /\ eval e2 = Some n}
     ∪ {(a:nat) s'' s', ⟪ s', p ⟫ | s'' =[r] s' /\ (a = 0 /\ exists a s, s =[r] s'' /\ P a s /\ eval e1 = None) /\ eval e2 = None})).
  <|= {eapply IHe2}
  ({a s s' n, ⟨ c, n, s', p ⟩ | s =[r] s' /\ P a s /\ eval e1 = Some n}
     ∪ {a s'', ⟨ comp' e2 r c, a , s'', p ⟩ | a = 0 /\ exists a s, s =[r] s'' /\ P a s /\ eval e1 = None}).
  ⊇ {eauto}
  ({a s s' n, ⟨ c, n, s', p ⟩ | s =[r] s' /\ P a s /\ eval e1 = Some n}
     ∪ {a s s', ⟨ comp' e2 r c, 0 , s', p ⟩ | s =[r] s' /\ P a s /\ eval e1 = None}).
  ⊇ {eauto}
  ({a s s' n, ⟨ c, n, s', p ⟩ | s =[r] s' /\ get r s' = HAN (comp' e2 r c) p /\ P a s /\ eval e1 = Some n}
     ∪ {a s s', ⟨ comp' e2 r c, 0 , s', p ⟩ | s =[r] s' /\ get r s' = HAN (comp' e2 r c) p /\ P a s /\ eval e1 = None}).
  <== {apply vm_fail}
  ({a s s' n, ⟨ c, n, s', p ⟩ | s =[r] s' /\ get r s' = HAN (comp' e2 r c) p /\ P a s /\ eval e1 = Some n}
     ∪ {a s s', ⟪ s', Some r ⟫ | s =[r] s' /\ get r s' = HAN (comp' e2 r c) p /\ P a s /\ eval e1 = None}).
  ⊇ {lemma1}
  ({a s s' n, ⟨ c, n, s', p ⟩ | s =[r] s' /\ get r s' = HAN (comp' e2 r c) p /\ P a s /\ eval e1 = Some n}
     ∪ {a s s', ⟪ s', Some r ⟫ | set r (HAN (comp' e2 r c) p) s =[r+1] s' /\ P a s /\ eval e1 = None}).
  <== {eapply vm_unmark}
  ({a s s' n, ⟨UNMARK c, n, s', Some r⟩ | s =[r] s' /\ get r s' = HAN (comp' e2 r c) p /\ P a s /\ eval e1 = Some n}
     ∪ {a s s', ⟪ s', Some r⟫ | set r (HAN (comp' e2 r c) p) s =[r+1] s' /\ P a s /\ eval e1 = None}).
  ⊇ {lemma1}
    ({a s s' n, ⟨UNMARK c, n, s', Some r⟩ | set r (HAN (comp' e2 r c) p) s =[r+1] s' /\ P a s /\ eval e1 = Some n}
     ∪ {a s s', ⟪ s', Some r⟫ | set r (HAN (comp' e2 r c) p) s =[r+1] s' /\ P a s /\ eval e1 = None}).
  ⊇ {eauto}
    ({a s'' s' n, ⟨UNMARK c, n, s', Some r⟩ | s'' =[r+1] s' /\ (exists s, set r (HAN (comp' e2 r c) p) s = s'' /\ P a s) /\ eval e1 = Some n}
     ∪ {a s'' s', ⟪ s', Some r⟫ | s'' =[r+1] s' /\ (exists s, set r (HAN (comp' e2 r c) p) s = s'' /\ P a s) /\ eval e1 = None}).
  <|= {eapply IHe1}
    ({a s'', ⟨comp' e1 (r+1) (UNMARK c), a , s'', Some r⟩ | exists s, set r (HAN (comp' e2 r c) p) s = s'' /\ P a s}).
  ⊇ {eauto}
    ({a s, ⟨comp' e1 (r+1) (UNMARK c), a , set r (HAN (comp' e2 r c) p) s, Some r⟩ | P a s}).
  <== {apply vm_mark}
    ({a s, ⟨MARK r (comp' e2 r c) (comp' e1 (r+1) (UNMARK c)), a , s, p⟩ | P a s}).
  [].
Qed.



(* Specialise the spec to singleton sets. *)
Corollary spec' e r a c s p:
  exists s', ⟨comp' e r c, a, s, p⟩  =>> match eval e with
                                         | Some n => ⟨c , n, s', p⟩
                                         | None => ⟪ s', p⟫
                                         end /\ s =[r] s' .
Proof.
  pose (spec e r c p (fun a' s' => a = a' /\ s = s') (⟨comp' e r c, a, s, p⟩)) as S. simpl in S.
  premise S. eauto.
  repeat autodestruct. remember (eval e) as E.
  destruct E; destruct H; repeat autodestruct;subst; eexists; eauto. 
Qed.


(** * Soundness *)
  
(** Since the VM is defined as a small step operational semantics, we *)
(* have to prove that the VM is deterministic and does not get stuck in *)
(* order to derive soundness from the above theorem. *)


Ltac mem_get := match goal with
                | [H : get _ _ = _, I : get _ _ = _ |- _] => rewrite H in I; inversion I
                end.

Lemma determ_vm : determ VM.
  intros C C1 C2 V. induction V; intro V'; inversion V'; subst; try mem_get; reflexivity.
Qed.


Theorem sound x a s C : ⟨comp x, a, s, None⟩ =>>! C -> exists s', C = match eval x with
                                                                     | Some n => ⟨HALT, n, s', None⟩
                                                                     | None => ⟪ s', None⟫
                                                                     end.
Proof.
  intros.
  pose (spec' x 0 a HALT s None) as H'. repeat autodestruct. unfold comp in *. pose (determ_trc determ_vm) as D.
  unfold determ in D. remember (eval x) as E. destruct E.
  eexists. eapply D. apply H. split. apply H0. intro Contra. destruct Contra.
  inversion H2.

  eexists. eapply D. apply H. split. apply H0. intro Contra. destruct Contra.
  inversion H2.
Qed.
