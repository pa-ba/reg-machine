Require Import Memory.
Require Import ZArith.
Require Import FunctionalExtensionality.
Module LinearMemory <: Memory.
Definition adr := nat.
Definition adr0 := 0.
Definition next := S.
Definition empty_mem :=  fun T => (fun _ => None) : adr -> option T.

Definition lta' := lta nat S.

Lemma lta_le : forall (r r' : adr), lta' r r' -> r < r'.
Proof.
  intros r r' R. induction R; omega.
Qed. 

Lemma next_fresh : forall (r r' : adr), lta' r r' -> r <> r'.
Proof.
  intros r r' R. apply lta_le in R. omega.
Qed. 

Definition Mem T := adr -> option T.

Definition get {T:Type} r (m : Mem T) := m r.
Definition set {T:Type} r v (m : Mem T) r' :=
  if r' =? r then Some v else m r'.

Lemma get_set : forall T (r : adr) (v : T) (s :  Mem T), get r (set r v s) = Some v.
Proof.
  intros. unfold get, set. rewrite <- beq_nat_refl. reflexivity.
Qed.

Lemma get_get : forall T (r r' : adr) (v : T) (s :  Mem T), r <> r' -> get r (set r' v s) = get r s.
Proof.
  intros. unfold get, set. rewrite <- Nat.eqb_neq in H. rewrite H. reflexivity.
Qed. 

Lemma set_set : forall T (r : adr) (v v' : T) (s :  Mem T),
    set r v (set r v' s) = set r v s.
Proof.
  intros. apply functional_extensionality. intro. unfold set.
  destruct (x =? r); reflexivity.
Qed.
  
Lemma set_get : forall T (r : adr) (v : T) (s :  Mem T),
    get r s = Some v -> set r v  s = s.
Proof.
  intros. apply functional_extensionality. intro. unfold get, set.
  remember (x =? r) as b. destruct b. symmetry in Heqb. apply beq_nat_true in Heqb.
  subst. auto. auto.
Qed. 

Lemma empty_fresh : forall r {T}, ~ exists v, get r (empty_mem T) = Some v.
Proof.
  intros. intro Contra. destruct Contra. compute in H. inversion H.
Qed. 

Definition dec_eq := Nat.eq_dec.
  
End LinearMemory.