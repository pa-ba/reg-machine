Require Import Coq.Program.Equality.
Require Export Memory.

Definition is_preorder {Conf} (pre : Conf -> Conf -> Prop) : Prop
  := (forall c, pre c c) /\ (forall c1 c2 c3, pre c1 c2 -> pre c2 c3 -> pre c1 c3).
    

Definition monotonicity {Conf}
           (pre : Conf -> Conf -> Prop) (vm : Conf -> Conf -> Prop) :
     Prop := forall (C1 C1' C2 : Conf),
  pre C1 C1' ->
  vm C1 C2 ->
  exists C2', vm C1' C2' /\ pre C2 C2'.

Ltac prove_preorder :=
  split;[
    intros c; destruct c; eauto with memory
  | intros c1 c2 c3 L1 L2; destruct c1, c2, c3;
    inversion L1; inversion L2; subst; eauto with memory].

Ltac prove_monotonicity1 :=
  do 3 intro; intros Hle Step;
  dependent destruction Step; inversion Hle.

Ltac prove_monotonicity2 := subst;
  eexists; (split; [econstructor| idtac]);  eauto with memory.

Ltac prove_monotonicity := prove_monotonicity1; prove_monotonicity2.

Module Type Machine.
Parameter Conf : Type.
Parameter Pre : Conf -> Conf -> Prop.
Parameter Rel : Conf -> Conf -> Prop.
Parameter preorder : is_preorder Pre.
Parameter monotone : monotonicity Pre Rel.
End Machine.

Require Import List.
Require Import Relations.

Module MetaTheory (machine : Machine).
Export machine.
Import ListNotations.


Infix "==>" := Rel(at level 80, no associativity) : machine_scope.

Definition trc := clos_refl_trans Conf Rel.

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
forall P : Conf -> Conf -> Prop,
(forall c : Conf, P c c) ->
(forall c1 c2 c3 : Conf, c1 ==> c2 -> c2 =>> c3 -> P c2 c3 -> P c1 c3) ->
forall c c0 : Conf, c =>> c0 -> P c c0.
Proof. 
  intros X Y Z c1 c2 S. unfold trc in S. rewrite -> clos_rt_rt1n_iff in S.
  induction S; eauto. rewrite <- clos_rt_rt1n_iff in S. eauto.
Qed.

Infix "≤" := Pre  (at level 70) : machine_scope.
Notation "x ≥ y" := (Pre y x) (at level 70) : machine_scope.

Lemma cle_trans (C1 C2 C3 : Conf) : C1 ≤ C2 -> C2 ≤ C3 -> C1 ≤ C3.
Proof.
  intros. pose preorder as P. unfold is_preorder in *. destruct P. eauto.
Qed.
Lemma cle_refl (C : Conf) : C ≤ C.
Proof.
  intros. pose preorder as P. unfold is_preorder in *. destruct P. eauto.
Qed.

Hint Resolve cle_refl.

Lemma monotone_step (C1 C1' C2 : Conf) :
  C1 ≤ C1' ->
  C1 ==> C2 ->
  exists C2', C1' ==> C2' /\ C2 ≤ C2' .
Proof.
  intros. pose monotone as M. unfold monotonicity in M. eauto.
Qed. 

Lemma monotone_machine (C1 C1' C2 : Conf) :
  C1 ≤ C1' ->
  C1 =>> C2 ->
  exists C2', C1' =>> C2' /\ C2 ≤ C2' .
Proof.
  intros I M. generalize dependent C1'. dependent induction M using trc_ind';intros.
  - exists C1'. split; eauto.
  - eapply monotone_step in I; eauto. destruct I as [m2' HS]. destruct HS as [S Ic'].
    apply IHM in Ic'. destruct Ic'. destruct H0. eexists. split. eapply trc_step_trans'; eassumption. assumption.
Qed.

Definition Reach (C1 C2 : Conf) : Prop := exists C, C1 =>> C /\ C ≥ C2.

Infix "=|>" := Reach (at level 80, no associativity).

Lemma Reach_refl C : C =|> C.
Proof.
  exists C. split; auto.
Qed.

Hint Resolve Reach_refl.

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
End MetaTheory.
 