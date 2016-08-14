Import Nat.
Require Import ZArith.


Definition adr := nat.

Definition Mem : Set := adr -> nat.

Definition get (r : adr) (m : Mem) : nat := m r.

Definition set (r : adr) (v : nat) (m : Mem) : Mem :=
  fun r' => if eqb r r' then v else get r' m.

Definition Eqr (r : adr) (m1 m2 : Mem) :=
  forall i : adr, i < r -> get i m1 = get i m2.

Notation "x =[ r ] y" := (Eqr r x y) (at level 70).


Lemma eqr_refl x r : x =[ r ] x.
Proof. intros i H. reflexivity. Qed.

Lemma eqr_sym x y r : x =[ r ] y -> y =[ r ] x.
Proof. intros R i E. apply R in E. auto. Qed.

Lemma eqr_trans x y z r : x =[ r ] y -> y =[ r ] z -> x =[ r ] z.
Proof.
  unfold Eqr. intros H1 H2 i R. pose (H1 i R) as E1. pose (H2 i R) as E2.
  rewrite E1. auto.
Qed. 

Lemma eqr_less x y r r' : x =[ r ] y -> r' <= r -> x =[ r' ] y.
Proof. intros R L i L'. apply R. omega. Qed.


Lemma set_get_neq r i s n : r <> i -> get i s = get i (set r n s).
Proof.
  intro E. unfold get, set. remember (r =? i) as t. destruct t.
  - rewrite <- Nat.eqb_neq in *. rewrite E in *. inversion Heqt.
  - reflexivity.
Qed.

Lemma set_eqr n s s' r r' : set r n s =[r'] s' -> r < r' -> s =[r] s'.
Proof.
  intros H R i E. assert (i < r') as E' by omega. apply H in E'. rewrite <- E'.
  apply set_get_neq. omega.
Qed.


Lemma set_get r s n : get r (set r n s) = n.
Proof.
  unfold get, set. rewrite <- beq_nat_refl. reflexivity.
Qed.

Lemma set_get_eqr r r' s s' n : set r n s =[r'] s' -> r < r' -> get r s' = n.
Proof.
  intros R E. apply R in E. rewrite <- E. apply set_get.
Qed.


Lemma set_eqr_incr r s s' n : s =[r] s' -> set r n s =[r + 1] set r n s'.
Proof.
  admit.
Admitted.

