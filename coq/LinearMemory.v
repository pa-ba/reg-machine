Require Import Memory.
Require Import ZArith.
Require Import FunctionalExtensionality.


Module LinearMemory <: TruncMem.

Definition Reg := nat.
Definition Mem (T : Type) := nat -> option T.

Definition first := 0.
Definition next := S.
Definition empty :=  fun T => (fun _ => None) : Mem T.
Definition set {T} (r : Reg) (v : T) (m : Mem T) : Mem T :=
  fun r' => if r' =? r then Some v else m r'.
Definition get {T} (r : Reg) (m : Mem T) : option T := m r.



Definition freeFrom {T} (r : Reg) (m : Mem T) :=
  forall r', r <= r' -> m r' = None.

Definition memle {T} (m m' : Mem T) :=
  forall r v, m r = Some v -> m' r = Some v.

Notation "s ⊑ t" := (memle s t) (at level 70) : memory_scope.
Open Scope memory_scope.
Notation "s ⊒ t" := (t ⊑ s) (at level 70) : memory_scope.

(* Property 1 *)
Lemma empty_mem_free: forall T, freeFrom first (empty T). 
Proof.
  unfold freeFrom, first, empty. intros. reflexivity.
Qed.
  
(* Property 2 *)

Lemma get_set : forall T (r : Reg) (v : T) (s :  Mem T),
    get r (set r v s) = Some v.
Proof.
  unfold set, get. intros. rewrite <- beq_nat_refl. reflexivity.
Qed.

(* Property 3 *)

Lemma memle_set : forall {T} (s : Mem T) r v, freeFrom r s -> s ⊑ set r v s.
Proof.
  unfold freeFrom, set, memle. intros.
  remember (r0 =? r) as R. symmetry in HeqR. destruct R. apply beq_nat_true in HeqR. subst.
  rewrite H in H0;auto. inversion H0. assumption.
Qed.
  
(* Property 4 *)

Lemma freeFrom_set : forall {T} r (v : T) s, freeFrom r s ->  freeFrom (next r) (set r v s).
Proof.
  unfold freeFrom, next, set. intros.
  remember (r' =? r) as R. symmetry in HeqR. destruct R. apply beq_nat_true in HeqR. subst. omega.
  apply H. omega.
Qed.

(* Property 5 *)

Lemma memle_refl : forall {T} (s : Mem T), s ⊑ s.
Proof.
  unfold memle. intros. assumption.
Qed.

Lemma memle_trans : forall {T} (s t u : Mem T), s ⊑ t -> t ⊑ u -> s ⊑ u.
Proof.
  unfold memle. intros. eauto.
Qed.

(* Property 6 *)

Lemma set_monotone : forall {T} (s t : Mem T) r v, s ⊑ t -> set r v s ⊑ set r v t .
Proof.
  unfold set, memle. intros. destruct (r0 =? r); eauto.
Qed.
  

(* Property 7 *)

Lemma memle_get : forall {T} (s t : Mem T) r v, s ⊑ t -> get r s = Some v -> get r t = Some v.
Proof.
  unfold get, memle. intros. auto.
Qed.


(* Additional axiom *)

Lemma set_set : forall T (r : Reg) (v v' : T) (s :  Mem T),
    set r v (set r v' s) = set r v s.
Proof.
  unfold set. intros. apply functional_extensionality. intros.
  destruct (x =? r); auto.
Qed.

(* truncation operation and axioms *)

Definition truncate {T} (r : Reg) (m : Mem T) : Mem T :=
  fun r' => if r <=? r' then None else m r'.

Lemma truncate_monotone : forall {T} (s t : Mem T) r, s ⊑ t -> truncate r s ⊑ truncate r t.
Proof.
  unfold truncate, memle. intros.
  destruct (r <=? r0);auto.
Qed.
  
Lemma truncate_set : forall {T} (s : Mem T) v r , freeFrom r s -> truncate r (set r v s) = s.
Proof.
  unfold freeFrom, truncate, set. intros.
  apply functional_extensionality. intros.
  remember (r <=? x) as R. symmetry in HeqR. destruct R. apply leb_complete in HeqR.
  symmetry. auto. apply leb_complete_conv in HeqR.
  remember (x =? r) as R'. symmetry in HeqR'. destruct R'. apply beq_nat_true in HeqR'. subst. omega. reflexivity.
Qed.

End LinearMemory.


