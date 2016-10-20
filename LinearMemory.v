Require Import Memory.
Require Import ZArith.
Module LinearMemory <: Memory.
Definition adr := nat.
Definition adr0 := 0.
Definition next := S.

Definition lta' := lta nat S.

Lemma lta_le : forall (r r' : adr), lta' r r' -> r < r'.
Proof.
  intros r r' R. induction R; omega.
Qed. 

Lemma next_fresh : forall (r r' : adr), lta' r r' -> r <> r'.
Proof.
  intros r r' R. apply lta_le in R. omega.
Qed. 

Definition Mem T := adr -> T.

Definition get {T:Type} r (m : Mem T) := m r.
Definition set {T:Type} r v (m : Mem T) r' :=
  if r' =? r then v else m r'.

Lemma get_set : forall T (r : adr) (v : T) (s :  Mem T), get r (set r v s) = v.
Proof.
  intros. unfold get, set. rewrite <- beq_nat_refl. reflexivity.
Qed.

Lemma get_get : forall T (r r' : adr) (v : T) (s :  Mem T), r <> r' -> get r (set r' v s) = get r s.
Proof.
  intros. unfold get, set. rewrite <- Nat.eqb_neq in H. rewrite H. reflexivity.
Qed. 

Require Import FunctionalExtensionality.

Lemma set_set : forall T (r : adr) (v v' : T) (s :  Mem T),
    set r v (set r v' s) = set r v s.
Proof.
  intros. apply functional_extensionality. intro. unfold set.
  destruct (x =? r); reflexivity.
Qed.
  
Lemma set_get : forall T (r : adr) (s :  Mem T),
    set r (get r s) s = s.
Proof.
  intros. apply functional_extensionality. intro. unfold get, set.
  remember (x =? r) as b. destruct b. symmetry in Heqb. apply beq_nat_true in Heqb.
  subst. reflexivity. reflexivity.
Qed. 

  
End LinearMemory.