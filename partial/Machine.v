Require Import Coq.Program.Equality.
Require Export Memory.

Module Type Machine (mem: Memory).
Export mem.
Parameter Conf : Type.
Parameter MemElem : Type.
Parameter Rel : Conf * (Mem MemElem) -> Conf * (Mem MemElem) -> Prop.
Parameter monotone : forall (C1 C2 : Conf) (m1 m2 m1' : Mem MemElem),
  m1 ≤ m1' ->
  Rel (C1, m1) (C2, m2)  ->
  exists m2', Rel (C1, m1') (C2, m2') /\ m2 ≤ m2'.
End Machine.

Require Import List.
Require Import Relations.

Module MetaTheory (mem: Memory) (machine : Machine mem).
Export machine.
Module mt := MemoryTheory mem.
Export mt.  
Import ListNotations.

Definition Config := (Conf * Mem MemElem)%type.

Infix "==>" := Rel(at level 80, no associativity) : machine_scope.

Definition trc := clos_refl_trans Config Rel.

Infix "=>>" := trc (at level 80, no associativity) : machine_scope.

Open Scope machine_scope.

Lemma trc_refl c : c =>> c.
Proof. apply rt_refl. Qed.

Lemma trc_step c1 c2 : c1 ==> c2 -> c1 =>> c2.
Proof. apply rt_step. Qed.

Lemma trc_step_trans c1 c2 c3 : c1 =>> c2 -> c2 ==> c3 -> c1 =>> c3.
Proof. intros. eapply rt_trans; eauto using rt_step. Qed.

Lemma trc_step_trans' c1 c2 c3 : c1 ==> c2 -> c2 =>> c3 -> c1 =>> c3.
Proof. intros. eapply rt_trans; eauto using rt_step. Qed.

Lemma trc_trans c1 c2 c3 : c1 =>> c2 -> c2 =>> c3 -> c1 =>> c3.
Proof. apply rt_trans. Qed.


Hint Resolve trc_step trc_step_trans.
Hint Immediate trc_refl.

Lemma trc_ind' :
forall P : Config -> Config -> Prop,
(forall c : Config, P c c) ->
(forall c1 c2 c3 : Config, c1 ==> c2 -> c2 =>> c3 -> P c2 c3 -> P c1 c3) ->
forall c c0 : Config, c =>> c0 -> P c c0.
Proof. 
  intros X Y Z c1 c2 S. unfold trc in S. rewrite -> clos_rt_rt1n_iff in S.
  induction S; eauto. rewrite <- clos_rt_rt1n_iff in S. eauto.
Qed.

Inductive cle : Config -> Config -> Prop :=
  clem c m1 m2 : m1 ≤ m2 -> cle (c,m1) (c,m2).

Infix "≤" := cle  (at level 70) : machine_scope.
Notation "x ≥ y" := (cle y x) (at level 70) : machine_scope.

Hint Constructors cle.

Lemma cle_trans (C1 C2 C3 : Config) : C1 ≤ C2 -> C2 ≤ C3 -> C1 ≤ C3.
Proof.
  intros L1 L2. destruct C1, C2, C3. inversion L1. inversion L2. subst. constructor.
  eapply memle_trans;eassumption.
Qed.
Lemma cle_refl (C : Config) : C ≤ C.
Proof.
  destruct C. auto.
Qed.

Hint Resolve cle_refl.

Lemma monotone_step (C1 C1' C2 : Config) :
  C1 ≤ C1' ->
  C1 ==> C2 ->
  exists C2', C1' ==> C2' /\ C2 ≤ C2' .
Proof.
  intros L S. destruct L as [C m1 m2 Ic]. destruct C2. eapply monotone in Ic; eauto. destruct Ic as [m2' SS].
  destruct SS as [S' I]. eexists. split; eauto. 
Qed. 

Lemma monotone_machine (C1 C1' C2 : Config) :
  C1 ≤ C1' ->
  C1 =>> C2 ->
  exists C2', C1' =>> C2' /\ C2 ≤ C2' .
Proof.
  intros I M. generalize dependent C1'. dependent induction M using trc_ind';intros.
  - exists C1'. split; eauto.
  - eapply monotone_step in I; eauto. destruct I as [m2' HS]. destruct HS as [S Ic'].
    apply IHM in Ic'. destruct Ic'. destruct H0. eexists. split. eapply trc_step_trans'; eassumption. assumption.
Qed.

Definition Reach (C1 C2 : Config) : Prop := exists C, C1 =>> C /\ C ≥ C2.

Infix "=|>" := Reach (at level 80, no associativity).

Lemma Reach_refl C : C =|> C.
Proof.
  exists C. destruct C. split; auto.
Qed.


Lemma Reach_trans C1 C2 C3 : C1 =|> C2 -> C2 =|> C3 -> C1 =|> C3.
Proof.
  intros L1 L2.
  destruct L1 as [C1' L1]. destruct L1 as [S1 M1].
  destruct L2 as [C2' L2]. destruct L2 as [S2 M2].
  eapply monotone_machine in S2;[|eassumption]. destruct S2 as [C3' G]. destruct G as [S2' M2'].
  eexists. split.
  - eapply trc_trans. apply S1. apply S2'.
  - eapply cle_trans;eassumption.
Qed. 

Lemma Reach_cle C1 C2 : C1 ≥ C2 -> C1 =|> C2.
Proof.
  intros L. eexists. split. apply trc_refl. assumption.
Qed.

Lemma Reach_trc C1 C2 : C1 =>> C2 -> C1 =|> C2.
Proof.
  intros L. eexists. split. eassumption. apply cle_refl. 
Qed.

Lemma Reach_vm C1 C2 : C1 ==> C2 -> C1 =|> C2.
Proof.
  intros L. apply Reach_trc. apply trc_step. assumption.
Qed.



Lemma Reach_eq C1 C2 : C1 = C2 -> C1 =|> C1.
Proof.
  intros E. rewrite E. apply Reach_refl.
Qed.

Definition determ {A} (R : A -> A -> Prop) : Prop := forall C C1 C2, R C C1 -> R C C2 -> C1 = C2.

Definition trc' C C' :=  C =>> C' /\ ~ exists C'', C' ==> C''.

Notation "x =>>! y" := (trc' x y) (at level 80, no associativity).


Lemma determ_factor C1 C2 C3 : determ Rel -> C1 ==> C2 -> C1 =>>! C3 -> C2 =>> C3.
Proof.
  unfold determ. intros. destruct H1.
  destruct H1 using trc_ind'.
  - exfalso. apply H2. eexists. eassumption.
  - assert (c2 = C2). eapply H. apply H1. apply H0. subst. auto.
Qed.


Lemma determ_trc : determ Rel -> determ trc'.
Proof.
  intros. unfold determ. intros. destruct H0. induction H0 using trc_ind'. 
  - destruct H1. destruct H0 using trc_ind'. reflexivity. exfalso. apply H2. eexists. eassumption.
  - apply IHtrc. apply H2. split. eapply determ_factor; eassumption. destruct H1. assumption.
Qed.

Close Scope memory_scope.

End MetaTheory.
