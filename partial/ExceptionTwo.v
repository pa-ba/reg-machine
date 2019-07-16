(** Calculation of the simple arithmetic language with exceptions
using two code continuations. *)

Require Import List.
Require Import Tactics.
Require Import Coq.Program.Equality.
Module Exception (Import mem : Memory).

  
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
| ADD : Reg -> Code -> Code
| STORE : Reg -> Code -> Code
| THROW : Code
| UNMARK : Code -> Code
| MARK : Reg -> Code -> Code -> Code
| HALT : Code.

Fixpoint comp' (x : Expr) (r : Reg) (c : Code) (f : Code) : Code :=
  match x with
  | Val n => LOAD n c
  | Add e1 e2 => comp' e1 r (STORE r (comp' e2 (next r) (ADD r c) f)) f
  | Throw => LOAD 0 f
  | Catch e1 e2 => comp' e1 r c (comp' e2  r c f)
  end.

Definition comp (x : Expr) : Code := comp' x first HALT HALT.


Inductive RVal : Set :=
| VAL : nat -> RVal.

(** * Virtual Machine *)

Inductive Conf' : Type :=
| conf : Code -> nat -> Conf'.

Definition Conf : Type := Conf' * Mem RVal.

Notation "⟨ x , y , s ⟩" := (conf x y, s).


Reserved Notation "x ==> y" (at level 80, no associativity).
Inductive VM : Conf -> Conf -> Prop :=
| vm_load n a c s : ⟨LOAD n c, a , s⟩ ==> ⟨c , n, s⟩ 
| vm_add c s a r n : s[r]=  VAL n -> ⟨ADD r c, a , s⟩ ==> ⟨c , n + a, s⟩
| vm_store c s a r : ⟨STORE r c, a, s⟩ ==> ⟨c , a, s[r:=VAL a]⟩
where "x ==> y" := (VM x y).

Inductive cle : Conf -> Conf -> Prop :=
 | cle_mem  f s s' : s ⊑ s' -> cle (f, s) (f, s').

Hint Constructors cle.


(** * Calculation *)

(** Boilerplate to import calculation tactics *)

Module VM <: Machine.
Definition Conf := Conf.
Definition Pre := cle.
Definition Rel := VM.
Lemma monotone : monotonicity cle VM.
prove_monotonicity. Qed.
Lemma preorder : is_preorder cle.
prove_preorder. Qed.
End VM.

Module VMCalc := Calculation mem VM.
Import VMCalc.


(** Specification of the compiler *)

Theorem spec : forall  e r c a f s,
  freeFrom r s ->
  ⟨comp' e r c f, a, s⟩
    =|>
    match eval e with
    | Some n => ⟨c , n, s⟩
    | None => ⟨f , 0, s⟩
    end.


(** Setup the induction proof *)

Proof.
  induction e;intros.

(** Calculation of the compiler *)

(** - [x = Val n]: *)

  begin
    match eval (Val n) with
    | Some n' => ⟨c , n', s⟩
    | None => ⟨c , 0, s⟩
    end.
  = {auto}
      ⟨ c, n, s⟩.
  <== {apply vm_load}
      ⟨ LOAD n c, a, s ⟩.
  [].

(** - [x = Add x1 x2]: *)
  
  begin
    match eval (Add e1 e2) with
    | Some n => ⟨c , n, s⟩
    | None => ⟨f , 0, s⟩
    end.
  = { auto }
    match eval e1 with
    | Some n => match eval e2 with
                | Some n' => ⟨c , n + n' ,s⟩
                | None => ⟨f , 0 ,s⟩
                end
    | None => ⟨f , 0 ,s⟩
    end.
  ⊑ { auto }
    match eval e1 with
    | Some n => match eval e2 with
                | Some n' => ⟨c , n + n' ,s[r:=VAL n]⟩
                | None => ⟨f , 0 ,s⟩
                end
    | None => ⟨f , 0 ,s⟩
    end.
  <== { apply vm_add }
      match eval e1 with
      | Some n => match eval e2 with
                  | Some n' => ⟨ADD r c , n', s[r:=VAL n]⟩
                  | None => ⟨f , 0 ,s⟩
                  end
      | None => ⟨f , 0 ,s⟩
      end.
  ⊑ { auto }
    match eval e1 with
    | Some n => match eval e2 with
                | Some n' => ⟨ADD r c , n', s[r:=VAL n]⟩
                | None => ⟨f , 0 ,s[r:=VAL n]⟩
                end
    | None => ⟨f , 0 ,s⟩
    end.
  <|= { apply IHe2 }
      match eval e1 with
      | Some n => ⟨comp' e2 (next r) (ADD r c) f , n, s[r:=VAL n]⟩
      | None => ⟨f , 0 ,s⟩
      end.
  <== { apply vm_store }
      match eval e1 with
      | Some n => ⟨STORE r (comp' e2 (next r) (ADD r c) f) , n , s⟩
      | None => ⟨f , 0 ,s⟩
      end.
  <|= { apply IHe1 }
    ⟨comp' e1 r (STORE r (comp' e2 (next r) (ADD r c) f)) f, a, s⟩.
  [].

(** - [x = Throw]: *)
  
  begin
    match eval Throw with
    | Some n => ⟨c , n, s⟩
    | None => ⟨f , 0 ,s⟩
    end.
  = { auto }
      ⟨f , 0 ,s⟩.
  <== { apply vm_load }
      ⟨LOAD 0 f , a ,s⟩.
  [].

(** - [x = Catch x1 x2]: *)
  
  begin
    match eval (Catch e1 e2) with
    | Some n => ⟨c , n ,s⟩
    | None => ⟨f , 0 ,s⟩
    end.
  = { auto }
      match eval e1 with
      | Some n => ⟨c , n ,s⟩
      | None => match eval e2 with
                | Some n' => ⟨c , n' , s⟩
                | None => ⟨f , 0 ,s⟩
                end
      end.
  <|= { apply IHe2 }
      match eval e1 with
      | Some n => ⟨c , n, s⟩
      | None => ⟨comp' e2  r c f , 0 ,s⟩
      end.

  <|= {apply IHe1}
      ⟨comp' e1 r c (comp' e2  r c f) , a , s⟩.
  [].
Qed.


(** * Soundness *)
  
(** Since the VM is defined as a small step operational semantics, we *)
(* have to prove that the VM is deterministic and does not get stuck in *)
(* order to derive soundness from the above theorem. *)


Lemma determ_vm : determ VM.
  intros C C1 C2 V. induction V; intro V'; inversion V'; subst;eauto.
  rewrite H in *; dist. 
Qed.


Theorem sound x a s n C : freeFrom first s -> eval x = Some n -> ⟨comp x, a, s⟩ =>>! C -> exists s', C = ⟨HALT, n,s'⟩.
Proof.
  intros F E M.
  pose (spec x first HALT a HALT s F). unfold Reach in *. repeat autodestruct.
  pose (determ_trc determ_vm) as D.
  unfold determ in D. inversion H0. subst. eexists. eapply D. apply M.
  rewrite E in *.
  split. inversion H1. subst.
  
  apply H. intro Contra. destruct Contra.
  inversion H3.
Qed.

End Exception.
