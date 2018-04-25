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
| HAN : Code -> Han -> Elem
| CUR : Han -> Elem.

(** * Virtual Machine *)

Inductive Conf : Type :=
| conf : Code -> Conf
| fail : Conf.


Notation "⟨ x , y ,  s ⟩" := (conf x , y, s).
Notation "⟪ x , s ⟫" := (fail, x, s).

Definition acc := named "acc".
Definition han := named "han".

Reserved Notation "x ==> y" (at level 80, no associativity).
Inductive VM : Conf * Mem Elem * Mem Elem -> Conf * Mem Elem * Mem Elem -> Prop :=
| vm_load n m c s : ⟨LOAD n c, m, s⟩ ==> ⟨c , m[acc:=NUM n], s⟩ 
| vm_add c s a r n m : s[r]=  NUM n -> m[acc]= NUM a
                       -> ⟨ADD r c, m, s⟩ ==> ⟨c , m[acc:=NUM (n + a)], s⟩
| vm_store c s a r m : m[acc] = NUM a -> ⟨STORE r c, m, s⟩ ==> ⟨c , m, s[r:=NUM a]⟩
| vm_throw s m : ⟨THROW, m, s⟩ ==> ⟪m, s⟫
| vm_fail p p' m s c : m[han]=CUR (Some p) -> s[p] = HAN c p'  ->
                     ⟪ m, s⟫ ==> ⟨c, m[han:=CUR p'], s⟩
| vm_unmark p p' s m c c' : m[han] = CUR(Some p) -> s[p] = HAN c' p' ->
                            ⟨UNMARK c, m, s⟩ ==> ⟨c, m[han:=CUR p'], s⟩
| vm_mark  r s m p c c' : ⟨MARK r c' c, m, s⟩ ==> ⟨c, m[han:= CUR (Some r)], s[r:= HAN c' p]⟩
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
Admitted.
(* prove_monotonicity. Qed. *)
End VM.
Module VMCalc := Calculation mem VM.
Import VMCalc.


(** Specification of the compiler *)

Theorem spec e r m c s :
  freeFrom r s ->
  ⟨comp' e r c, m, s⟩
    =|>
    match eval e with
    | Some n => ⟨c , m[acc:=NUM n] , s⟩
    | None => ⟪m, s⟫
    end.


(** Setup the induction proof *)

Proof.
  intros.
  generalize dependent c.
  generalize dependent s.
  generalize dependent r.
  generalize dependent m.
  induction e;intros.

(** Calculation of the compiler *)

(** - [x = Val n]: *)

  begin
    match eval (Val n) with
    | Some n' => ⟨c , m[acc:=NUM n'], s⟩
    | None => ⟪m, s⟫
    end.
  = {auto}
      ⟨ c, m[acc:=NUM n], s⟩.
  <== {apply vm_load}
      ⟨ LOAD n c, m, s ⟩.
  [].

(** - [x = Add x1 x2]: *)
  
  begin
    match eval (Add e1 e2) with
    | Some n => ⟨c , m[acc:=NUM n], s⟩
    | None => ⟪m, s⟫
    end.
  = { auto }
    match eval e1 with
    | Some n => match eval e2 with
                | Some n' => ⟨c , m[acc:= NUM (n + n')], s⟩
                | None => ⟪m, s⟫
                end
    | None => ⟪m, s⟫
    end.
  ≤ { auto }
    match eval e1 with
    | Some n => match eval e2 with
                | Some n' => ⟨c , m[acc:= NUM (n + n')], s[r:=NUM n]⟩
                | None => ⟪m, s[r:=NUM n]⟫
                end
    | None => ⟪m, s⟫
    end.
  <== { apply vm_add }
      match eval e1 with
      | Some n => match eval e2 with
                  | Some n' => ⟨ADD r c , m[acc:= NUM n'], s[r:=NUM n]⟩
                  | None => ⟪m, s[r:=NUM n]⟫
                  end
      | None => ⟪m, s⟫
      end.
  <|= { admit } (* apply IHe2 *)
      match eval e1 with
      | Some n => ⟨comp' e2 (next r) (ADD r c) , m[acc:=NUM n], s[r:=NUM n]⟩
      | None => ⟪m, s⟫
      end.
  <== { apply vm_store }
      match eval e1 with
      | Some n => ⟨STORE r (comp' e2 (next r) (ADD r c)) , m[acc:=NUM n],  s⟩
      | None => ⟪m, s⟫
      end.
  <|= { apply IHe1 }
    ⟨comp' e1 r (STORE r (comp' e2 (next r) (ADD r c))), m, s⟩.
  [].

(** - [x = Throw]: *)
  
  begin
    match eval Throw with
    | Some n => ⟨c ,m[acc:= NUM n], s⟩
    | None => ⟪m, s⟫
    end.
  = { auto }
      ⟪m, s⟫.
  <== { apply vm_throw }
      ⟨THROW, m, s⟩.
  [].

(** - [x = Catch x1 x2]: *)
  
  begin
    match eval (Catch e1 e2) with
    | Some n => ⟨c , m[acc:=NUM n], s⟩
    | None => ⟪m, s⟫
    end.
  = { auto }
      match eval e1 with
      | Some n => ⟨c , m[acc:=NUM n], s⟩
      | None => match eval e2 with
                | Some n' => ⟨c , m[acc:=NUM n'], s⟩
                | None => ⟪m, s⟫
                end
      end.
  <|= { apply IHe2 }
      match eval e1 with
      | Some n => ⟨c , m[acc:=NUM n], s⟩
      | None => ⟨comp' e2  r c , m, s⟩
      end.
  ≤ { eauto }
      match eval e1 with
      | Some n => ⟨c , m[acc:=NUM n], s⟩
      | None => ⟨comp' e2  r c , m, s[r:= HAN (comp' e2  r c) p]⟩
      end.
  <== {apply vm_fail}
      match eval e1 with
      | Some n => ⟨c , n ,p, s⟩
      | None => ⟪Some r, s[r:= HAN (comp' e2  r c) p]⟫
      end.
  ≤ {auto}
      match eval e1 with
      | Some n => ⟨c , n ,p, s[r:= HAN (comp' e2  r c) p]⟩
      | None => ⟪Some r, s[r:= HAN (comp' e2  r c) p]⟫
      end.
  <== {eapply vm_unmark; apply get_set}
      match eval e1 with
      | Some n => ⟨UNMARK c , n ,Some r, s[r:= HAN (comp' e2  r c) p]⟩
      | None => ⟪Some r, s[r:= HAN (comp' e2  r c) p]⟫
      end.
  <|= {apply IHe1}
      ⟨comp' e1 (next r) (UNMARK c) , a ,Some r, s[r:= HAN (comp' e2  r c) p]⟩.
  <== {apply vm_mark}
      ⟨MARK r (comp' e2  r c) (comp' e1 (next r) (UNMARK c)) , a ,p, s⟩.
  [].
Qed.


(** * Soundness *)
  
(** Since the VM is defined as a small step operational semantics, we *)
(* have to prove that the VM is deterministic and does not get stuck in *)
(* order to derive soundness from the above theorem. *)


Lemma determ_vm : determ VM.
  intros C C1 C2 V. induction V; intro V'; inversion V'; subst;eauto.
  rewrite H in *; dist. rewrite H in H3. dist. rewrite H in H5. dist.
Qed.


Theorem sound x a p s n C : freeFrom adr0 s -> eval x = Some n -> ⟨comp x, a, p, s⟩ =>>! C -> exists s', C = ⟨HALT, n,p, s'⟩.
Proof.
  intros F E M.
  pose (spec x adr0 HALT a p s F). unfold Reach in *. repeat autodestruct.
  pose (determ_trc determ_vm) as D.
  unfold determ in D. inversion H0. subst. eexists. eapply D. apply M.
  rewrite E in *.
  split. inversion H1. subst.
  
  apply H. intro Contra. destruct Contra.
  inversion H3.
Qed.

End Exception.
