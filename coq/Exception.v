(** Calculation of the simple arithmetic language with exceptions
(using CRASH instruction to signal uncaught exceptions). *)

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
    | Add x y => match eval x with
                   | Some n => match eval y with
                               | Some n' => Some (n + n')
                               | None => None
                               end
                   | None => None
                   end
    | Throw => None
    | Catch x y => match eval x with
                   | Some n => Some n
                   | None => eval y
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
| UNMARK : Code -> Code
| CRASH : Code.


Fixpoint comp (x : Expr) (r : Reg) (c : Code) : Code :=
  match x with
  | Val n     => LOAD n c
  | Add x y   => comp x r (STORE r (comp y (next r) (ADD r c)))
  | Throw     => THROW
  | Catch x y => MARK r (comp y r c) (comp x (next r) (UNMARK c))
  end.

Definition compile (x : Expr) : Code := comp x first HALT.

Definition Han : Set := Code * Reg.

Inductive val : Set :=
| VAL : nat -> val
| HAN : Han -> val.

(** * Virtual Machine *)

Inductive Conf' : Type :=
| conf : Code -> nat -> Han -> Conf'
| fail : Han -> Conf'.

Definition Conf : Type := Conf' * Mem val.

Notation "⟨ x , y , z , m ⟩" := (conf x y z, m).
Notation "⟪ x , m ⟫" := (fail x, m).

Reserved Notation "x ==> y" (at level 80, no associativity).
Inductive VM : Conf -> Conf -> Prop :=
| vm_load n a c m h :
    ⟨LOAD n c, a , h, m⟩    ==> ⟨c , n, h, m⟩ 
| vm_store c m a r h :
    ⟨STORE r c, a, h, m⟩    ==> ⟨c , a, h, m[r:=VAL a]⟩
| vm_add c m a r n h : m[r]=  VAL n ->
    ⟨ADD r c, a , h, m⟩     ==> ⟨c , n + a, h, m⟩
| vm_throw a m h : ⟨THROW, a, h, m⟩ ==> ⟪h, m⟫
| vm_mark h r m a c c' :
    ⟨MARK r c' c, a, h, m⟩  ==> ⟨c, a, (c', r), m[r:= HAN h]⟩
| vm_unmark h h' r m a c : m[r] = HAN h' ->
    ⟨UNMARK c, a, (h,r), m⟩ ==> ⟨c, a, h', m⟩
| vm_fail  m c r h : m[r] = HAN h ->
    ⟪(c,r), m⟫              ==> ⟨c, 0, h, m⟩
where "x ==> y" := (VM x y).

Inductive cle : Conf -> Conf -> Prop :=
 | cle_mem  f m m' : m ⊑ m' -> cle (f, m) (f, m').

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

Theorem spec : forall e r c a h m ,
  freeFrom r m ->
  ⟨comp e r c, a, h, m⟩
    =|>
    match eval e with
    | Some n => ⟨c , n, h, m⟩
    | None => ⟪h, m⟫
    end.


(** Setup the induction proof *)

Proof.
  induction e;intros.

(** Calculation of the compiler *)

(** - [x = Val n]: *)

  begin
    match eval (Val n) with
    | Some n' => ⟨c , n' ,h, m⟩
    | None => ⟪h, m⟫
    end.
  = {auto}
      ⟨ c, n, h, m⟩.
  <== {apply vm_load}
      ⟨ LOAD n c, a, h, m ⟩.
  [].

(** - [x = Add e1 e2]: *)
  
  begin
    match eval (Add e1 e2) with
    | Some n => ⟨c , n ,h, m⟩
    | None => ⟪h, m⟫
    end.
  = { auto }
    match eval e1 with
    | Some n => match eval e2 with
                | Some n' => ⟨c , n + n' ,h, m⟩
                | None => ⟪h, m⟫
                end
    | None => ⟪h, m⟫
    end.
  ⊑ { auto }
    match eval e1 with
    | Some n => match eval e2 with
                | Some n' => ⟨c , n + n' ,h, m[r:=VAL n]⟩
                | None => ⟪h, m[r:=VAL n]⟫
                end
    | None => ⟪h, m⟫
    end.
  <== { apply vm_add }
      match eval e1 with
      | Some n => match eval e2 with
                  | Some n' => ⟨ADD r c , n' ,h, m[r:=VAL n]⟩
                  | None => ⟪h, m[r:=VAL n]⟫
                  end
      | None => ⟪h, m⟫
      end.
  <|= { apply IHe2 }
      match eval e1 with
      | Some n => ⟨comp e2 (next r) (ADD r c) , n ,h, m[r:=VAL n]⟩
      | None => ⟪h, m⟫
      end.
  <== { apply vm_store }
      match eval e1 with
      | Some n => ⟨STORE r (comp e2 (next r) (ADD r c)) , n ,h, m⟩
      | None => ⟪h, m⟫
      end.
  <|= { apply IHe1 }
    ⟨comp e1 r (STORE r (comp e2 (next r) (ADD r c))), a,h, m⟩.
  [].

(** - [x = Throw]: *)
  
  begin
    match eval Throw with
    | Some n => ⟨c , n ,h, m⟩
    | None => ⟪h, m⟫
    end.
  = { auto }
      ⟪h, m⟫.
  <== { apply vm_throw }
      ⟨THROW, a, h, m⟩.
  [].

(** - [x = Catch e1 e2]: *)
  
  begin
    match eval (Catch e1 e2) with
    | Some n => ⟨c , n ,h, m⟩
    | None => ⟪h, m⟫
    end.
  = { auto }
      match eval e1 with
      | Some n => ⟨c , n ,h, m⟩
      | None => match eval e2 with
                | Some n' => ⟨c , n' ,h, m⟩
                | None => ⟪h, m⟫
                end
      end.
  <|= { apply IHe2 }
      match eval e1 with
      | Some n => ⟨c , n ,h, m⟩
      | None => ⟨comp e2 r c, 0 ,h, m⟩
      end.
  ⊑ { eauto }
      match eval e1 with
      | Some n => ⟨c , n ,h, m⟩
      | None => ⟨comp e2  r c , 0 ,h, m[r:= HAN h]⟩
      end.
  <== {apply vm_fail}
      match eval e1 with
      | Some n => ⟨c, n, h, m⟩
      | None => ⟪(comp e2 r c,r), m[r:= HAN h]⟫
      end.
  ⊑ {auto}
      match eval e1 with
      | Some n => ⟨c, n, h, m[r:= HAN h]⟩
      | None => ⟪(comp e2 r c,r), m[r:= HAN h]⟫
      end.
  <== {eapply vm_unmark}
      match eval e1 with
      | Some n => ⟨UNMARK c, n, (comp e2 r c,r), m[r:= HAN h]⟩
      | None => ⟪(comp e2 r c,r), m[r:= HAN h]⟫
      end.
  <|= {apply IHe1}
      ⟨comp e1 (next r) (UNMARK c) , a ,(comp e2 r c,r), m[r:= HAN h]⟩.
  <== {apply vm_mark}
      ⟨MARK r (comp e2  r c) (comp e1 (next r) (UNMARK c)) , a ,h, m⟩.
  [].
Qed.

Definition empty := (@empty val).

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

Theorem sound' x a r C :
  ⟨compile x, a, (CRASH, r), empty⟩ =>>! C ->
  ((exists m n, C = ⟨HALT, n, (CRASH, r), m⟩ /\ eval x = Some n)
   \/ ((forall n h m, C <> ⟨HALT, n, h, m⟩) /\ eval x = None)).
Proof.
  intros E.
  pose (spec' x a (CRASH, r)). unfold Reach in *. repeat autodestruct.
  pose (determ_trc determ_vm) as D.
  unfold determ in D. inversion H0. subst.
  remember (eval x) as X.
  destruct X.
  - left. inversion H0. subst. inversion H1. subst. eexists. eexists.
    split. eapply D. eapply E. split. apply H. intro Contra. destruct Contra.
    inversion H3. reflexivity.
  - right. inversion H0. subst. inversion H1. subst.
    remember (get r m') as G. split;auto.
    destruct G. destruct v.
    + assert (C = ⟪ (CRASH, r), m' ⟫) as R. eapply D. eapply E. split. auto. intro Contra. destruct Contra.
      inversion H3. rewrite H9 in HeqG. inversion HeqG. subst. intros. intro Contra. inversion Contra.
    + assert (C = ⟨ CRASH, 0, h, m' ⟩) as R.
      eapply D. eapply E. split. eapply trc_step_trans. apply H. econstructor. eauto. intro Contra. destruct Contra.
      inversion H3. subst. intros. intro Contra. inversion Contra.
    + assert (C = ⟪ (CRASH, r), m' ⟫) as R. eapply D. eapply E. split. auto. intro Contra. destruct Contra.
      inversion H3. rewrite H9 in HeqG. inversion HeqG. subst. intros. intro Contra. inversion Contra.
Qed.


End Exception.
