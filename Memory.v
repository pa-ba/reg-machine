(* Abstract specification of memory *)


Inductive lta T n (r : T) : T -> Prop :=
| lea_self : lta T n r (n r)
| lea_next r' : lta T n r r' -> lta T n r (n r').


Module Type Memory.

Parameter adr : Set.

Parameter adr0 : adr.
Parameter next : adr -> adr.

Hint Constructors lta.

Infix "<" := (lta adr next).

Axiom next_fresh : forall (r r' : adr), r < r' -> r <> r'.

Parameter Mem : Type -> Type.

Parameter get : forall {T}, adr -> Mem T -> T.
Parameter set : forall {T}, adr -> T -> Mem T -> Mem T.

Axiom get_set : forall T (r : adr) (v : T) (s :  Mem T),
    get r (set r v s) = v.
Axiom get_get : forall T (r r' : adr) (v : T) (s :  Mem T),
    r <> r' -> get r (set r' v s) = get r s.
Axiom set_set : forall T (r : adr) (v v' : T) (s :  Mem T),
    set r v (set r v' s) = set r v s.
Axiom set_get : forall T (r : adr) (s :  Mem T),
    set r (get r s) s = s.

End Memory.

Module MemoryTheory (mem : Memory).

Import mem.
Require Import Setoid.  
       

Lemma lta_trans (r1 r2 r3 : adr) : r1 < r2 -> r2 < r3 -> r1 < r3.
Proof.
  intros R1 R2. induction R2;auto.
Qed.

Hint Resolve lta_trans.

Definition lea r r' := r < r' \/ r = r'.

Infix "<=" := lea.


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

Inductive eqr {T} (r : adr) : Mem T ->  Mem T -> Prop :=
| eqr_refl m : eqr r m m
| eqr_set r' m v : r <= r' -> eqr r m (set r' v m)
| eqr_trans m1 m2 m3 : eqr r m1 m2 -> eqr r m2 m3 -> eqr r m1 m3. 

Notation "x =[ r ] y" := (eqr r x y) (at level 70).

Hint Constructors eqr.



Lemma eqr_set'  T r r' (m: Mem T) v : r <= r' -> set r' v m =[r] m.
Proof.
  intros l. apply eqr_set with (m0 := set r' v m) (v0 := get r' m) in l.
  rewrite set_set in l. rewrite set_get in l. assumption.
Qed. 


Lemma eqr_sym T (x y : Mem T) r : x =[ r ] y -> y =[ r ] x.
Proof.
  intros R. induction R.
  - constructor.
  - apply eqr_set'; assumption.
  - eapply eqr_trans;eassumption.
Qed. 
  

Lemma eqr_lea T (x y : Mem T) r r' : x =[ r ] y -> r' <= r -> x =[ r' ] y.
Proof.
  intros R L. induction R; eauto.
Qed.

Lemma eqr_lta T (x y : Mem T) r r' : x =[ r ] y -> r' < r -> x =[ r' ] y.
Proof. intros. eauto using eqr_lea, lta_to_lea. Qed.
       

Lemma set_eqr T n (s s' : Mem T) r r' : s =[r] s' -> r <= r' -> set r' n s =[r] s'.
Proof.
  intros H R. induction H.
  - apply eqr_sym. auto.
  - eapply eqr_trans. apply eqr_sym. apply eqr_set.
    assumption. apply eqr_set. assumption.
  - eapply eqr_trans. apply IHeqr1. assumption.
Qed.


(* Lemma set_get_eqr T r r' (s s' : Mem T) n : set r n s =[r'] s' -> r < r' -> get r s' = n. *)
(* Proof. *)
(*   intros R E. apply R in E. rewrite <- E. apply get_set. *)
(* Qed. *)


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

Lemma eqr_get T (m m' : Mem T) r r' :
  m =[r] m' -> r' < r -> get r' m = get r' m'.
Proof.
  intros R E. induction R.
  - reflexivity.
  - rewrite get_get. reflexivity. apply next_fresh. eauto.
  - rewrite IHR1. rewrite <- IHR2. reflexivity.
Qed. 

Lemma rProp_get T r r' (v : T) : r' < r -> rProp r (fun s => get r' s = v).
Proof.
  unfold rProp. intros R s s' E. eapply eqr_get in E. rewrite E. tauto. assumption.
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


Lemma rProp_def T (P : Mem T -> Prop) r :
  rProp r P <-> (forall m r' v, r <= r' -> (P m <-> P (set r' v m))).
Proof.
  split; intro.
  - auto.
  - intros m m' R. induction R.
    * tauto.
    * auto.
    * rewrite IHR1. assumption.
Qed .
    

End MemoryTheory.