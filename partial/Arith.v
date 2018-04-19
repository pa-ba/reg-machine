(** Calculation of the simple arithmetic language. *)

Require Import List.
Require Import Tactics.
Require Import Coq.Program.Equality.
Module Arith (mem : Memory).
Import mem.

  
(** * Syntax *)

Inductive Expr : Set := 
| Val : nat -> Expr 
| Add : Expr -> Expr -> Expr.

(** * Semantics *)

Fixpoint eval (x: Expr) : nat :=
  match x with
    | Val n => n
    | Add x1 x2 => eval x1 + eval x2
  end.

(** * Compiler *)

Inductive Code : Set :=
| LOAD : nat -> Code -> Code
| ADD : adr -> Code -> Code
| STORE : adr -> Code -> Code
| HALT : Code.

Fixpoint comp' (x : Expr) (r : adr) (c : Code) : Code :=
  match x with
    Val n => LOAD n c
  | Add e1 e2 => comp' e1 r (STORE r (comp' e2 (next r) (ADD r c)))
  end.

Definition comp (x : Expr) : Code := comp' x adr0 HALT.

(** * Virtual Machine *)

Inductive Conf : Type := conf : Code -> nat -> Mem nat -> Conf.

Notation "⟨ x , y , z ⟩" := (conf x y z).

Reserved Notation "x ==> y" (at level 80, no associativity).
Inductive VM : Conf -> Conf -> Prop :=
| vm_load n a c s : ⟨LOAD n c, a , s⟩ ==> ⟨c , n,  s⟩
| vm_add c s a r n : get r s = Some n -> ⟨ADD r c, a , s⟩ ==> ⟨c , n + a,  s⟩
| vm_store c s a r : ⟨STORE r c, a , s⟩ ==> ⟨c , a,  set r a s⟩
where "x ==> y" := (VM x y).

Module Mem := MemoryTheory mem.
Export Mem.

Inductive cle : Conf -> Conf -> Prop :=
  | cle_mem c a s s' : s =< s' -> cle ⟨c, a , s⟩ ⟨c, a , s'⟩.

Lemma monotone_machine_step : forall (C1 C1' C2 : Conf),
  cle C1 C1' ->
  C1 ==> C2 ->
  exists C2', C1' ==> C2' /\ cle C2 C2' .
Proof.
  intros C1 C1' C2 Hle Step.
  destruct Step;inversion Hle; inversion Hle;
    eexists; split; econstructor ; eauto using memle_get, set_monotone.
Qed.


(** * Calculation *)

(** Boilerplate to import calculation tactics *)

Module VM <: Machine.
Definition Conf := Conf.
Definition Rel := VM.
Definition cle := cle.
Definition monotone := monotone_machine_step.
End VM.
Module VMCalc := Calculation VM mem.
Import VMCalc.


(** Specification of the compiler *)

Theorem spec e r a c P : rProp r P -> { s , ⟨comp' e r c, a, s⟩ | P s } =|> {s , ⟨c , eval e, s⟩ | P s } .


(** Setup the induction proof *)

Proof.
  intros.
  generalize dependent c.
  generalize dependent P.
  generalize dependent r.
  generalize dependent a.
  induction e;intros.

(** Calculation of the compiler *)

(** - [x = Val n]: *)

  begin
    ({s , ⟨ c, eval (Val n), s ⟩ | P s}).
  ⊇ { auto }
    ({s , ⟨ c, n, s⟩ | P s}).
  <== { apply vm_load }
    ({s , ⟨ LOAD n c, a, s ⟩ | P s}).
  ⊇ { auto using eqr_refl }
    ({s , ⟨ LOAD n c, a, s ⟩ | P s}).
  [].

(** - [x = Add x1 x2]: *)
  
  begin
    ({s, ⟨ c, eval (Add e1 e2), s ⟩ | P s}).
  ⊇ {auto}
    ({s, ⟨ c, eval e1 + eval e2, s ⟩ | P s}).
  ⊇ {eauto}
    ({ s, ⟨c, get r s + eval e2, s⟩ | get r s = eval e1 /\ P s }).
  <== { apply vm_add}
    ({ s, ⟨ADD r c, eval e2, s⟩ | get r s = eval e1 /\ P s }).
  <|= {apply IHe2;eauto}
   ({ s, ⟨comp' e2 (next r) (ADD r c), eval e1, s⟩ | get r s = eval e1 /\ P s }).
  ⊇ {try (rewrite <- rProp_set); eauto using get_set}
    ({s, ⟨comp' e2 (next r) (ADD r c), eval e1, set r (eval e1) s⟩ | P s }).
  <== { apply vm_store}
    ({ s, ⟨STORE r (comp' e2 (next r) (ADD r c)), eval e1, s⟩ | P(s) }).
  <|= { apply IHe1 }
    ({ s, ⟨comp' e1 r (STORE r (comp' e2 (next r) (ADD r c))), a, s⟩ | P(s) }).
  [].
Qed.


(* Specialise the spec to singleton sets. *)
Corollary spec' e r a c s :
  exists s', ⟨comp' e r c, a, s⟩  =>> ⟨c , eval e, s'⟩ /\ s =[r] s'.
Proof.
  pose (spec e r a c (fun s' => s =[r] s')) as S. premise S. eapply rProp_eqr.
  pose (S (⟨comp' e r c, a, s⟩)) as S'. simpl in S'. premise S'. eexists. split;eauto. 
  repeat autodestruct; subst; eexists; eauto.
Qed.


(** * Soundness *)
  
(** Since the VM is defined as a small step operational semantics, we *)
(* have to prove that the VM is deterministic and does not get stuck in *)
(* order to derive soundness from the above theorem. *)


Lemma determ_vm : determ VM.
  intros C C1 C2 V. induction V; intro V'; inversion V'; subst; reflexivity.
Qed.


Theorem sound x a s C : ⟨comp x, a, s⟩ =>>! C -> exists s', C = ⟨HALT, eval x, s'⟩.
Proof.
  intros.
  pose (spec' x adr0 a HALT s) as H'. repeat autodestruct. unfold comp in *. pose (determ_trc determ_vm) as D.
  unfold determ in D. eexists. eapply D. apply H. split. apply H0. intro Contra. destruct Contra.
  inversion H2.
Qed.

End Arith.