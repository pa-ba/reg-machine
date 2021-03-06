(** Calculation of the simple arithmetic language with exceptions
using explicit empty handler. *)

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
| HALT : Code
| LOAD : nat -> Code -> Code
| STORE : Reg -> Code -> Code
| ADD : Reg -> Code -> Code
| THROW : Code
| MARK : Reg -> Code -> Code -> Code
| UNMARK : Code -> Code.


Fixpoint comp (x : Expr) (r : Reg) (c : Code) : Code :=
  match x with
  | Val n => LOAD n c
  | Add e1 e2 => comp e1 r (STORE r (comp e2 (next r) (ADD r c)))
  | Throw => THROW
  | Catch e1 e2 => MARK r (comp e2 r c) (comp e1 (next r) (UNMARK c))
  end.

Definition compile (x : Expr) : Code := comp x first HALT.

Definition Han : Set := option (Code * Reg).

Inductive RVal : Set :=
| VAL : nat -> RVal
| HAN : Han -> RVal.

(** * Virtual Machine *)

Inductive Conf' : Type :=
| conf : Code -> nat -> Han -> Conf'
| fail : Han -> Conf'.

Definition Conf : Type := Conf' * Mem RVal.

Notation "⟨ x , y , z , s ⟩" := (conf x y z, s).
Notation "⟪ x , s ⟫" := (fail x, s).

Reserved Notation "x ==> y" (at level 80, no associativity).
Inductive VM : Conf -> Conf -> Prop :=
| vm_load n a c s h : ⟨LOAD n c, a , h, s⟩ ==> ⟨c , n, h, s⟩ 
| vm_store c s a r h : ⟨STORE r c, a, h, s⟩ ==> ⟨c , a, h, s[r:=VAL a]⟩
| vm_add c s a r n h : s[r]=  VAL n -> ⟨ADD r c, a , h, s⟩ ==> ⟨c , n + a, h, s⟩
| vm_throw a s h : ⟨THROW, a, h, s⟩ ==> ⟪h, s⟫
| vm_mark h r s a c c' : ⟨MARK r c' c, a, h, s⟩ ==> ⟨c, a, Some (c', r), s[r:= HAN h]⟩
| vm_unmark h h' r s a c : s[r] = HAN h' ->
                            ⟨UNMARK c, a, Some (h,r), s⟩ ==> ⟨c, a, h', s⟩
| vm_fail  s c r h : s[r] = HAN h -> ⟪ Some (c,r), s⟫ ==> ⟨c, 0, h, s⟩
where "x ==> y" := (VM x y).

Inductive cle : Conf -> Conf -> Prop :=
 | cle_mem  f s s' : s ⊑ s' -> cle (f, s) (f, s').

Hint Constructors cle : core.


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

Theorem spec : forall e r c a h s,
  freeFrom r s ->
  ⟨comp e r c, a, h, s⟩
    =|>
    match eval e with
    | Some n => ⟨c , n, h, s⟩
    | None => ⟪h, s⟫
    end.


(** Setup the induction proof *)

Proof.
  induction e;intros.

(** Calculation of the compiler *)

(** - [x = Val n]: *)

  begin
    match eval (Val n) with
    | Some n' => ⟨c , n' ,h, s⟩
    | None => ⟪h, s⟫
    end.
  = {auto}
      ⟨ c, n, h, s⟩.
  <== {apply vm_load}
      ⟨ LOAD n c, a, h, s ⟩.
  [].

(** - [x = Add x1 x2]: *)
  
  begin
    match eval (Add e1 e2) with
    | Some n => ⟨c , n ,h, s⟩
    | None => ⟪h, s⟫
    end.
  = { auto }
    match eval e1 with
    | Some n => match eval e2 with
                | Some n' => ⟨c , n + n' ,h, s⟩
                | None => ⟪h, s⟫
                end
    | None => ⟪h, s⟫
    end.
  ⊑ { auto }
    match eval e1 with
    | Some n => match eval e2 with
                | Some n' => ⟨c , n + n' ,h, s[r:=VAL n]⟩
                | None => ⟪h, s[r:=VAL n]⟫
                end
    | None => ⟪h, s⟫
    end.
  <== { apply vm_add }
      match eval e1 with
      | Some n => match eval e2 with
                  | Some n' => ⟨ADD r c , n' ,h, s[r:=VAL n]⟩
                  | None => ⟪h, s[r:=VAL n]⟫
                  end
      | None => ⟪h, s⟫
      end.
  <|= { apply IHe2 }
      match eval e1 with
      | Some n => ⟨comp e2 (next r) (ADD r c) , n ,h, s[r:=VAL n]⟩
      | None => ⟪h, s⟫
      end.
  <== { apply vm_store }
      match eval e1 with
      | Some n => ⟨STORE r (comp e2 (next r) (ADD r c)) , n ,h, s⟩
      | None => ⟪h, s⟫
      end.
  <|= { apply IHe1 }
    ⟨comp e1 r (STORE r (comp e2 (next r) (ADD r c))), a,h, s⟩.
  [].

(** - [x = Throw]: *)
  
  begin
    match eval Throw with
    | Some n => ⟨c , n ,h, s⟩
    | None => ⟪h, s⟫
    end.
  = { auto }
      ⟪h, s⟫.
  <== { apply vm_throw }
      ⟨THROW, a, h, s⟩.
  [].

(** - [x = Catch x1 x2]: *)
  
  begin
    match eval (Catch e1 e2) with
    | Some n => ⟨c , n ,h, s⟩
    | None => ⟪h, s⟫
    end.
  = { auto }
      match eval e1 with
      | Some n => ⟨c , n ,h, s⟩
      | None => match eval e2 with
                | Some n' => ⟨c , n' ,h, s⟩
                | None => ⟪h, s⟫
                end
      end.
  <|= { apply IHe2 }
      match eval e1 with
      | Some n => ⟨c , n ,h, s⟩
      | None => ⟨comp e2 r c, 0 ,h, s⟩
      end.
  ⊑ { eauto }
      match eval e1 with
      | Some n => ⟨c , n ,h, s⟩
      | None => ⟨comp e2  r c , 0 ,h, s[r:= HAN h]⟩
      end.
  <== {apply vm_fail}
      match eval e1 with
      | Some n => ⟨c, n, h, s⟩
      | None => ⟪Some (comp e2 r c,r), s[r:= HAN h]⟫
      end.
  ⊑ {auto}
      match eval e1 with
      | Some n => ⟨c, n, h, s[r:= HAN h]⟩
      | None => ⟪Some (comp e2 r c,r), s[r:= HAN h]⟫
      end.
  <== {eapply vm_unmark}
      match eval e1 with
      | Some n => ⟨UNMARK c, n, Some (comp e2 r c,r), s[r:= HAN h]⟩
      | None => ⟪Some (comp e2 r c,r), s[r:= HAN h]⟫
      end.
  <|= {apply IHe1}
      ⟨comp e1 (next r) (UNMARK c) , a ,Some (comp e2 r c,r), s[r:= HAN h]⟩.
  <== {apply vm_mark}
      ⟨MARK r (comp e2  r c) (comp e1 (next r) (UNMARK c)) , a ,h, s⟩.
  [].
Qed.

Definition empty := (@empty RVal).

(** Specification of the whole compiler *)

Theorem spec' e a h : ⟨compile e, a, h, empty⟩  =|> match eval e with
                                                      | Some n => ⟨HALT, n, h, empty⟩
                                                      | None => ⟪h, empty⟫
                                                    end.
Proof.
  begin
    match eval e with
    | Some n => ⟨HALT, n, h, empty⟩
    | None => ⟪h, empty⟫
    end.
  <|= {apply spec; apply empty_mem_free}
      ⟨comp e first HALT, a,h, empty⟩.
  [].
Qed.


(** * Soundness *)
  
(** Since the VM is defined as a small step operational semantics, we *)
(* have to prove that the VM is deterministic and does not get stuck in *)
(* order to derive soundness from the above theorem. *)


Lemma determ_vm : determ VM.
  intros C C1 C2 V. induction V; intro V'; inversion V'; subst;eauto.
  rewrite H in *; dist. rewrite H in H6. dist. rewrite H in H4. dist.
Qed.

Theorem sound x a C :
  ⟨compile x, a, None, empty⟩ =>>! C ->
  ((exists m n, C = ⟨HALT, n, None, m⟩ /\ eval x = Some n) \/ (exists m, C = ⟪None , m⟫ /\ eval x = None)).
Proof.
  intros E.
  pose (spec' x a None). unfold Reach in *. repeat autodestruct.
  pose (determ_trc determ_vm) as D.
  unfold determ in D. inversion H0. subst.
  remember (eval x) as X.
  destruct X.
  - left. inversion H0. subst. inversion H1. subst. eexists. eexists.
    split. eapply D. eapply E. split. apply H. intro Contra. destruct Contra.
    inversion H3. reflexivity.
  - right. inversion H0. subst. inversion H1. subst. eexists.
    split. eapply D. eapply E. split. apply H. intro Contra. destruct Contra.
    inversion H3. reflexivity.
Qed.

End Exception.
