Import Nat.
Require Import ZArith.


Parameter adr : Set.

Parameter adr0 : adr.
Parameter next : adr -> adr.

Fixpoint nextN (n : nat) (r : adr) : adr :=
  match n with
  | 0 => r
  | S n' => next (nextN n' r)
  end.

Notation "r + n" := (nextN n r).

Inductive lta (r : adr) : adr -> Prop :=
| lea_self : lta r (next r)
| lea_next r' : lta r r' -> lta r (next r').

Hint Constructors lta.

Infix "<" := lta.

Definition lea r r' := r < r' \/ r = r'.

Infix "<=" := lea.

Axiom next_fresh : forall (r r' : adr), r < r' -> r <> r'.

Parameter Mem : Type -> Type.

Parameter get : forall {T}, adr -> Mem T -> T.
Parameter set : forall {T}, adr -> T -> Mem T -> Mem T.

Axiom get_set : forall T (r : adr) (v : T) (s :  Mem T), get r (set r v s) = v.
Axiom get_get : forall T (r r' : adr) (v : T) (s :  Mem T), r <> r' -> get r (set r' v s) = get r s.

Lemma lta_trans (r1 r2 r3 : adr) : r1 < r2 -> r2 < r3 -> r1 < r3.
Proof.
  intros R1 R2. induction R2;auto.
Qed.

Hint Resolve lta_trans.

Lemma next_nextN r n : next (r + n) = next r + n.
Proof.
  generalize dependent r. induction n. reflexivity.
  intros. simpl. rewrite IHn. reflexivity.
Qed.

Lemma lta_nextN r n : r < r + (S n).
Proof.
  induction n;simpl in *; auto.
Qed.

Lemma lta_next_eq (r r' : adr) : r < r' <-> exists n, r' = r + (S n).
Proof.
  split;intros.
  - induction H.
    + exists 0. reflexivity.
    + destruct IHlta. exists (S x). simpl in *. subst. reflexivity.
  - destruct H. subst. apply lta_nextN.
Qed. 

Lemma lea_lta r1 r2 r3 : r1 <= r2 -> r2 < r3 -> r1 < r3.
Proof.
  intros R1 R2. destruct R1. eauto. subst. assumption.
Qed. 


Lemma lta_lea r1 r2 r3 : r1 < r2 -> r2 <= r3 -> r1 < r3.
Proof.
  intros R1 R2. destruct R2. eauto. subst. assumption.
Qed.

Lemma lea_refl r : r <= r.
Proof. unfold lea. auto. Qed.

Lemma lea_sym r1 r2 r3 : r1 <= r2 -> r2 <= r3 -> r1 <= r3.
Proof.
  intros R1 R2.
  destruct R1;subst;try assumption.
  destruct R2; subst;try (left; assumption).
  left. eauto.
Qed. 

Hint Resolve lta_lea lea_lta lea_sym lea_refl.

Definition Eqr {T} (r : adr) (m1 m2 : Mem T) :=
  forall i : adr, i < r -> get i m1 = get i m2.

Notation "x =[ r ] y" := (Eqr r x y) (at level 70).


Lemma eqr_refl T (x : Mem T) r : x =[ r ] x.
Proof. intros i H. reflexivity. Qed.

Hint Resolve eqr_refl.

Lemma eqr_sym T (x y : Mem T) r : x =[ r ] y -> y =[ r ] x.
Proof. intros R i E. apply R in E. auto. Qed.

Lemma eqr_trans T (x y z : Mem T) r : x =[ r ] y -> y =[ r ] z -> x =[ r ] z.
Proof.
  unfold Eqr. intros H1 H2 i R. pose (H1 i R) as E1. pose (H2 i R) as E2.
  rewrite E1. auto.
Qed. 

Lemma eqr_lea T (x y : Mem T) r r' : x =[ r ] y -> r' <= r -> x =[ r' ] y.
Proof. intros R L i L'. apply R. eauto. Qed.

Lemma eqr_lta T (x y : Mem T) r r' : x =[ r ] y -> r' < r -> x =[ r' ] y.
Proof. intros R L i L'. apply R. eauto. Qed.


Lemma set_eqr T n (s s' : Mem T) r r' : set r n s =[r'] s' -> r < r' -> s =[r] s'.
Proof.
  intros H R i E. assert (i < r') as E' by eauto. apply H in E'. rewrite <- E'.
  symmetry. eauto using get_get, next_fresh.
Qed.


Lemma set_get_eqr T r r' (s s' : Mem T) n : set r n s =[r'] s' -> r < r' -> get r s' = n.
Proof.
  intros R E. apply R in E. rewrite <- E. apply get_set.
Qed.

Lemma eqr_set  T r r' (s: Mem T) n : r <= r' -> set r' n s =[r] s.
Proof.
  unfold Eqr. intros R i I. apply get_get. apply next_fresh. eauto.
Qed. 


Definition rProp {T} (r: adr) (P : Mem T -> Prop) : Prop := forall s s', s =[r] s' -> (P s <-> P s').


Ltac rProp_log := unfold rProp; intros Pr Qr s s' E;
  pose (Pr s s' E) as Pr'; pose (Qr s s' E) as Qr';
  rewrite Pr'; rewrite Qr'; tauto.

Lemma rProp_conj r T (P Q : Mem T -> Prop) : rProp r P -> rProp r Q -> rProp r (fun s => P s /\ Q s).
Proof. rProp_log. Qed. 

Lemma rProp_disj r T (P Q : Mem T -> Prop) : rProp r P -> rProp r Q -> rProp r (fun s => P s \/ Q s).
Proof. rProp_log. Qed.

Lemma rProp_impl r T (P Q : Mem T -> Prop) : rProp r P -> rProp r Q -> rProp r (fun s => P s -> Q s).
Proof. rProp_log. Qed.

Lemma rProp_ex r T S (P : S -> Mem T -> Prop) : (forall a, rProp r (P a)) -> rProp r (fun s => exists a, P a s).
Proof.
  unfold rProp; intros Pr s s' E.
  split; intros; destruct H; eexists.
  rewrite <- Pr; eauto.
  rewrite -> Pr; eauto.
Qed.

Lemma rProp_const T r P : rProp r (fun s : Mem T => P).
Proof.
  unfold rProp. tauto.
Qed.

Lemma rProp_get T r r' (v : T) : r' < r -> rProp r (fun s => get r' s = v).
Proof.
  unfold rProp. intros R s s' E. rewrite E. tauto. eauto.
Qed.

Lemma rProp_eqr T r (s' : Mem T) : rProp r (fun s => s' =[r] s).
Proof.
  unfold rProp. intros s1 s2 E. split; eauto using eqr_sym, eqr_trans. 
Qed.


Lemma rProp_lea T r r' (P : Mem T -> Prop) : r < r' -> rProp r P -> rProp r' P.
Proof.
  unfold rProp. intros R Pr s s' E. eapply Pr. eauto using eqr_lta.
Qed .

Lemma rProp_ext T r (P : Mem T -> Prop) : rProp r P -> rProp r (fun s => P s).
Proof. auto. Qed.

Hint Resolve rProp_conj rProp_disj rProp_impl rProp_ex rProp_get rProp_lea rProp_ext rProp_const.

Lemma rProp_set T (P : Mem T -> Prop) v s r r' : rProp r P -> r <= r' -> (P s <-> P (set r' v s)).
Proof.
  unfold rProp. intros Pr R. split;intro Ps; rewrite <- Pr; eauto using eqr_sym, eqr_set.
Qed.

Lemma rProp_set_r T (P : Mem T -> Prop) v s r: rProp r P -> P s -> P (set r v s).
Proof. intros. rewrite <- rProp_set; eauto. Qed.

Lemma rProp_set_l T (P : Mem T -> Prop) v s r : rProp r P -> P (set r v s) -> P s.
Proof. intros. rewrite <- rProp_set in *; eauto. Qed.


Ltac rProp_set_solve := eauto;try (rewrite <- rProp_set; eauto).