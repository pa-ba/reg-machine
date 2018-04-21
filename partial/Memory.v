(* Abstract specification of memory *)


Inductive lta T n (r : T) : T -> Prop :=
| lea_self : lta T n r (n r)
| lea_next r' : lta T n r r' -> lta T n r (n r').


Module Type Memory.

Parameter adr : Set.

Parameter adr0 : adr.
Parameter next : adr -> adr.

Parameter dec_eq : forall (r r' : adr),  {r  = r'} + { r <> r'}.

Hint Constructors lta.

Infix "<" := (lta adr next) (at level 70).

Axiom next_fresh : forall (r r' : adr), r < r' -> r <> r'.

Parameter Mem : Type -> Type.

Parameter get : forall {T}, adr -> Mem T -> option T.
Parameter set : forall {T}, adr -> T -> Mem T -> Mem T.

Axiom get_set : forall T (r : adr) (v : T) (s :  Mem T),
    get r (set r v s) = Some v.
Axiom get_get : forall T (r r' : adr) (v : T) (s :  Mem T),
    r <> r' -> get r (set r' v s) = get r s.
Axiom set_set : forall T (r : adr) (v v' : T) (s :  Mem T),
    set r v (set r v' s) = set r v s.
Axiom set_get : forall T (r : adr) (v : T) (s :  Mem T),
    get r s = Some v -> set r v  s = s.


End Memory.

Require Import Setoid.  
Module MemoryTheory (mem : Memory).

Export mem.


Definition dom {T} (s : Mem T) (r : adr) : Prop
  := exists v, get r s = Some v.


Notation "x ∈ y" := (@dom _ y x) (at level 70).
Notation "x ∉ y" := (~(x ∈ y)) (at level 70).

Infix "≤" := memle  (at level 70) .
Notation "x ≥ y" := (memle y x) (at level 70).

Definition lea r r' := r < r' \/ r = r'.

Infix "<=" := lea.

Definition freeFrom {T} (r : adr) (s : Mem T) := forall r', r <= r' -> r' ∉ s.

Definition memle {T} (s t : Mem T) : Prop :=
  forall r, r ∈ s -> get r s = get r t.





Lemma memle_refl T (s : Mem T) : s ≤ s.
Proof.
  intros r D. reflexivity.
Qed.

Hint Resolve memle_refl.

Lemma memle_get T r v (s t : Mem T) :
  s ≤ t -> get r s = Some v -> get r t = Some v.
Proof.
  intros. assert (exists t, get r s = Some t) as E by eauto.
  apply H in E. rewrite <- E. assumption.
Qed.


Lemma memle_dom T r (s t : Mem T) : s ≤ t -> r ∈ s -> r ∈ t.
Proof.
  intros L D. destruct D as [v E]. eapply memle_get in E; eauto.
  exists v. assumption.
Qed.

Lemma memle_trans T (s t u : Mem T) : s ≤ t -> t ≤ u -> s ≤ u.
Proof.
  intros L1 L2 r D. rewrite L1 by assumption. eauto using memle_dom.
Qed. 

Lemma not_memle T r (s : Mem T) : r ∉ s -> get r s = None.
Proof.
  intros.
  remember (get r s) as G. destruct G.
  - assert (exists t, get r s = Some t) as E by eauto. contradiction.
  - reflexivity.
Qed.

Lemma memle_set T r v (s : Mem T) : (r ∉ s) ->  s ≤ set r v s.
Proof.
  intros rs r' rs'.
  remember (dec_eq r r') as R. destruct R.
  - subst. contradiction.
  - symmetry. apply get_get. auto.
Qed.

Lemma set_dom T r r' v (s : Mem T) : r ∈ s -> r ∈ (set r' v s).
Proof.
  intro D. destruct (dec_eq r r').
  - subst. eexists. rewrite get_set. eauto.
  - destruct D. eexists. rewrite get_get by eauto. eauto.
Qed.
  
Lemma set_dom_fresh T r r' v (s : Mem T) : r <> r' -> r ∈ (set r' v s) -> r ∈ s.
Proof.
  intros I D. destruct D. eexists. rewrite get_get in H by auto. eassumption.
Qed.
  


Lemma set_monotone T r v (s t : Mem T) :
  s ≤ t -> set r v s ≤ set r v t.
Proof.
  intros L r' D. destruct (dec_eq r r').
  - subst. do 2 rewrite get_set. reflexivity.
  - do 2 rewrite get_get by auto. apply L. eapply set_dom_fresh; eauto.
Qed.

  
Lemma lta_trans (r1 r2 r3 : adr) : r1 < r2 -> r2 < r3 -> r1 < r3.
Proof.
  intros R1 R2. induction R2;auto.
Qed.

Hint Resolve lta_trans.


Fixpoint nextN (n : nat) (r : adr) : adr :=
  match n with
  | 0 => r
  | S n' => next (nextN n' r)
  end.

Notation "r + n" := (nextN n r).


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

Lemma lta_to_lea r r' : r < r' -> r <= r'.
Proof.
  intro. unfold "<=". tauto.
Qed.

Lemma lea_sym r1 r2 r3 : r1 <= r2 -> r2 <= r3 -> r1 <= r3.
Proof.
  intros R1 R2.
  destruct R1;subst;try assumption.
  destruct R2; subst;try (left; assumption).
  left. eauto.
Qed. 

Hint Resolve lta_lea lea_lta lea_sym lea_refl.


End MemoryTheory.
