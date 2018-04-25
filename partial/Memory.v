Require Export String.

(* Abstract specification of memory *)


Inductive lta T n (r : T) : T -> Prop :=
| lea_self : lta T n r (n r)
| lea_next r' : lta T n r r' -> lta T n r (n r').


Module Type Memory.

Parameter adr : Set.

Parameter adr0 : adr.
Parameter next : adr -> adr.

Parameter named : string -> adr.

Parameter dec_eq : forall (r r' : adr),  {r  = r'} + { r <> r'}.

Hint Constructors lta.

Infix "<" := (lta adr next) (at level 70) : memory_scope.

Open Scope memory_scope.

Axiom next_fresh : forall (r r' : adr), r < r' -> r <> r'.

Axiom named_fresh : forall (n m : string), n <> m -> named n <> named m.

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


Notation "r ∈ s" := (exists v, get r s = Some v) (at level 70) : memory_scope.
Notation "x ∉ y" := (~(x ∈ y)) (at level 70) : memory_scope.

Notation "s ≤ t" := (forall r, r ∈ s -> get r s = get r t) (at level 70) : memory_scope.
Notation "s ≥ t" := (t ≤ s) (at level 70) : memory_scope.

Notation "r <= r'" := (r < r' \/ r = r') (at level 70) : memory_scope.

Notation "s [ r ] = v" := (get r s = Some v) (at level 70).
Notation "s [ r := v ]" := (set r v s) (at level 70).

End Memory.

Require Import Setoid.  
Module MemoryTheory (mem : Memory).

Export mem.



    

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
Qed.

Lemma memle_trans T (s t u : Mem T) : s ≤ t -> t ≤ u -> s ≤ u.
Proof.
  intros L1 L2 r D. rewrite L1 by assumption. eauto using memle_dom.
Qed. 

(* Lemma not_memle T r (s : Mem T) : r ∉ s -> get r s = None. *)
(* Proof. *)
(*   intros. *)
(*   remember (get r s) as G. destruct G. *)
(*   - assert (r ∈ s) as E by eauto. contradiction. *)
(*   - reflexivity. *)
(* Qed. *)

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


Lemma lea_lta r1 r2 r3 : r1 <= r2 -> r2 < r3 -> r1 < r3.
Proof.
  intros R1 R2. destruct R1. eauto. subst. assumption.
Qed. 


Lemma lta_lea r1 r2 r3 : r1 < r2 -> r2 <= r3 -> r1 < r3.
Proof.
  intros R1 R2. destruct R2. eauto. subst. assumption.
Qed.

Lemma lea_refl r : r <= r.
Proof. auto. Qed.

Lemma lta_to_lea r r' : r < r' -> r <= r'.
Proof.
  intro. tauto.
Qed.

Lemma lea_sym r1 r2 r3 : r1 <= r2 -> r2 <= r3 -> r1 <= r3.
Proof.
  intros R1 R2.
  destruct R1;subst;try assumption.
  destruct R2; subst;try (left; assumption).
  left. eauto.
Qed. 

Hint Resolve lta_lea lea_lta lea_sym lea_refl.


Definition freeFrom {T} (r : adr) (s : Mem T) := forall r', r <= r' -> r' ∉ s.


Lemma lta_next r r' : next r < r' -> r < r'.
Proof.
  intros L. remember (next r) as R. induction L;subst;auto.
Qed.
        
Lemma lea_next_lta r r' : next r <= r' -> r < r'.
Proof.
  intros L. inversion L.
  - apply lta_next. assumption.
  - subst. auto.
Qed.        

Lemma lea_next r r' : next r <= r' -> r <= r'.
Proof.
  intros L. left. apply lea_next_lta. assumption.
Qed.


Lemma lea_next_neq r r' : next r <= r' -> r <> r'.
Proof.
  auto using next_fresh, lea_next_lta.
Qed.

Lemma freeFrom_set T r (v : T) s : freeFrom r s ->  freeFrom (next r) (set r v s).
Proof.
  intros F r' L.
  assert (r <> r') as NE by auto using lea_next_neq.
  intros I.
  apply set_dom_fresh in I; eauto. apply F in I; auto. apply lea_next. assumption.
Qed.

End MemoryTheory.
