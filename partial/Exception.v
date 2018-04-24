(** Calculation of the simple arithmetic language. *)

Require Import List.
Require Import Tactics.
Require Import Coq.Program.Equality.
Module Exception (mem : Memory).
Import mem.

  
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
                               | Some n => Some (m + n)%nat
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

Fixpoint comp' (x : Expr) (r : adr) (c : Code) : Code :=
  match x with
  | Val n => LOAD n c
  | Add e1 e2 => comp' e1 r (STORE r (comp' e2 (next r) (ADD r c)))
  | Throw => THROW
  | Catch e1 e2 => MARK r (comp' e2 r c) (comp' e1 (next r) (UNMARK c))
  end.

Definition comp (x : Expr) : Code := comp' x adr0 HALT.

Definition Han := option adr.

Inductive Elem : Set :=
| NUM : nat -> Elem
| HAN : Code -> Han -> Elem.

(** * Virtual Machine *)

Inductive Conf : Type :=
| conf : Code -> nat -> Han -> Conf
| fail : nat -> Han -> Conf.


Notation "⟨ x , y , z , s ⟩" := (conf x y z, s).
Notation "⟪ x , y , s ⟫" := (fail x y, s).

Reserved Notation "x ==> y" (at level 80, no associativity).
Inductive VM : Conf * Mem Elem -> Conf * Mem Elem -> Prop :=
| vm_load n a c s p : ⟨LOAD n c, a , p, s⟩ ==> ⟨c , n, p, s⟩ 
| vm_add c s a r n p : s[r]=  NUM n -> ⟨ADD r c, a , p, s⟩ ==> ⟨c , n + a, p, s⟩
| vm_store c s a r p : ⟨STORE r c, a, p, s⟩ ==> ⟨c , a, p, s[r:=NUM a]⟩
| vm_throw a s p : ⟨THROW, a, p, s⟩ ==> ⟪a, p, s⟫
| vm_fail p p' a s c : s[p] = HAN c p' -> ⟪a, Some p, s⟫ ==> ⟨c, a, p', s⟩
| vm_unmark p p' s a c c' : s[p] = HAN c' p' ->
                            ⟨UNMARK c, a, Some p, s⟩ ==> ⟨c, a, p', s⟩
| vm_mark p r s a c c' : ⟨MARK r c' c, a, p, s⟩ ==> ⟨c, a, Some r, s[r:= HAN c' p]⟩
where "x ==> y" := (VM x y).



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

Theorem spec e r c a p s :
  freeFrom r s ->
  ⟨comp' e r c, a, p, s⟩
    =|>
    match eval e with
    | Some n => ⟨c , n, p, s⟩
    | None => ⟪a, p, s⟫
    end.


(** Setup the induction proof *)

Proof.
  intros.
  generalize dependent c.
  generalize dependent s.
  generalize dependent r.
  generalize dependent a.
  generalize dependent p.
  induction e;intros.

(** Calculation of the compiler *)

(** - [x = Val n]: *)

  begin
    match eval (Val n) with
    | Some n' => ⟨c , n' ,p, s⟩
    | None => ⟪ a, p, s⟫
    end.
  = {auto}
      ⟨ c, n, p, s⟩.
  <== {apply vm_load}
      ⟨ LOAD n c, a, p, s ⟩.
  [].

(** - [x = Add x1 x2]: *)
  
  begin
    match eval (Add e1 e2) with
    | Some n => ⟨c , n ,p, s⟩
    | None => ⟪ a, p, s⟫
    end.
  = { auto }
    match eval e1 with
    | Some n => match eval e2 with
                | Some n' => ⟨c , n + n' ,p, s⟩
                | None => ⟪ a, p, s⟫
                end
    | None => ⟪ a, p, s⟫
    end.
  ≤ { auto }
    match eval e1 with
    | Some n => match eval e2 with
                | Some n' => ⟨c , n + n' ,p, s[r:=NUM n]⟩
                | None => ⟪ a, p, s[r:=NUM n]⟫
                end
    | None => ⟪ a, p, s⟫
    end.
  <== {apply vm_add; eauto using get_set}
      match eval e1 with
      | Some n => match eval e2 with
                  | Some n' => ⟨ADD r c , n' ,p, s[r:=NUM n]⟩
                  | None => ⟪ a, p, s[r:=NUM n]⟫
                  end
      | None => ⟪ a, p, s⟫
      end.
  <|= {?}
      match eval e1 with
      | Some n => ⟨comp' e2 (next r) (ADD r c) , a ,p, s[r:=NUM n]⟩
      | None => ⟪ a, p, s⟫
      end.
dist; eauto using freeFrom_set,IHe2.
  
      ⟨comp' e2 (next r) (ADD r c), eval e1, set r (eval e1) s⟩.
  <== { apply vm_store}
    ⟨STORE r (comp' e2 (next r) (ADD r c)), eval e1, s⟩.
  <|= { apply IHe1;eauto }
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