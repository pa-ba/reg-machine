Require Import Coq.Program.Equality.

Module Type Machine.
Parameter Conf : Type.
Parameter Rel : Conf -> Conf -> Prop.
Parameter cle : Conf -> Conf -> Prop.
Parameter monotone : forall (C1 C1' C2 : Conf),
  cle C1 C1' ->
  Rel C1 C2 ->
  exists C2', Rel C1' C2' /\ cle C2 C2' .
End Machine.

Require Import List.
Require Import Relations.

Module MetaTheory (mod : Machine).
Import mod.
Import ListNotations.

Infix "==>" := Rel(at level 80, no associativity).

Definition trc := clos_refl_trans Conf Rel.

Infix "=>>" := trc (at level 80, no associativity).


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


Lemma monotone_machine (C1 C1' C2 : Conf) :
  cle C1 C1' ->
  C1 =>> C2 ->
  exists C2', C1' =>> C2' /\ cle C2 C2' .
Proof.
  intros I M. generalize dependent C1'. dependent induction M using trc_ind';intros.
  - exists C1'. split; eauto.
  - eapply monotone in I; eauto. destruct I. destruct H0.
    apply IHM in H1. destruct H1. destruct H1. eexists. split. eapply trc_step_trans'; eassumption. assumption.
Qed.

Definition Reach (C1 C2 : Conf) : Prop := exists C, C1 =>> C /\ cle C C2.




(* Fixpoint tuple (ts : list Type) : Type := *)
(*   match ts with *)
(*     | []       => unit *)
(*     | t :: ts' => (t * tuple ts')%type *)
(*   end. *)


(* Inductive SetCom : list Type -> Type := *)
(* | BaseSet : Conf -> Prop -> SetCom nil *)
(* | ExSet {t ts} : (t -> SetCom ts) -> SetCom (t :: ts). *)

(* Definition funtail {t ts A} (x : t) (f : forall (args : tuple (t :: ts)),  A args)  *)
(* : forall (args : tuple ts), A (x, args) := *)
(*   fun xs => f (x, xs). *)


(* Fixpoint mkSetCom {ts} (C : tuple ts -> Conf) (P : tuple ts -> Prop) : SetCom ts := *)
(*   match ts return (tuple ts -> Conf) -> (tuple ts -> Prop) -> SetCom ts with *)
(*     | nil => fun C P => BaseSet (C tt) (P tt) *)
(*     | t :: ts' => fun C P => @ExSet t ts'  (fun x => @mkSetCom ts' (funtail x C) (funtail x P)) *)
(*   end C P. *)



(* Fixpoint getConf {ts} (S : SetCom ts) : tuple ts -> Conf := *)
(*   match S with *)
(*     | BaseSet C P => fun xs => C *)
(*     | ExSet ex => fun xs =>  let (x, xs') := xs in  getConf (ex x) xs' *)
(*   end. *)

(* Fixpoint getProp {ts} (S : SetCom ts) : tuple ts -> Prop := *)
(*   match S with *)
(*     | BaseSet C P => fun xs => P *)
(*     | ExSet ex => fun xs => let (x, xs') := xs in getProp (ex x) xs' *)
(*   end. *)

(* Lemma getConf_sound ts (C : tuple ts -> Conf) P x : getConf (mkSetCom C P) x = C x. *)
(* Proof. *)
(*   intros. induction ts; destruct x. reflexivity. simpl. apply (IHts (funtail a0 C)). *)
(* Qed. *)


(* Lemma getProp_sound ts (C : tuple ts -> Conf) P x : getProp (mkSetCom C P) x = P x. *)
(* Proof. *)
(*   intros. induction ts;destruct x. reflexivity. simpl. apply (IHts _ (funtail a0 P)). *)
(* Qed. *)

(* Fixpoint  SetComElem  {ts} (C : Conf) (S : SetCom ts) : Prop := *)
(*   match S with *)
(*       | BaseSet C' P => C' = C /\ P  *)
(*       | ExSet e => exists x, SetComElem C (e x) *)
(*   end. *)

(* Lemma set_com_elem {ts} (C : Conf) (S : SetCom ts) :  *)
(*   SetComElem C S <-> exists xs, getConf S xs = C /\ getProp S xs. *)
(* Proof. *)
(*   split; intros.  *)
(*   * induction S. *)
(*     - exists tt. assumption. *)

(*     - simpl in H. destruct H. apply H0 in H. *)
(*       decompose [ex and] H.  exists (x, x0). auto. *)
(*   * induction S. *)
(*     - decompose [ex and] H. simpl in *. tauto. *)
(*     - decompose [ex and] H. simpl. destruct x. *)
(*       exists t0. apply H0. exists t1. tauto. *)
(* Qed. *)


(* Inductive ConfSet : Type := *)
(*   | Sing {ts} : SetCom ts -> ConfSet *)
(*   | Empty : ConfSet *)
(*   | Union : ConfSet -> ConfSet -> ConfSet. *)


(* Fixpoint ConfElem (C : Conf) (S : ConfSet) : Prop := *)
(*   match S with *)
(*     | Sing s => SetComElem C s *)
(*     | Empty => False *)
(*     | Union S1 S2 => ConfElem C S1 \/  ConfElem C S2 *)
(*   end. *)

(* Notation "{| C | P |}" := (Sing (mkSetCom C P)) (at level 70, no associativity). *)
(* Infix "∈" := ConfElem (at level 80, no associativity). *)
(* Infix "∪" := Union (at level 76, left associativity). *)

(* Notation "S ⊆ T" := (forall x, x ∈ S -> x ∈ T) (at level 80, no associativity). *)
(* Notation "S == T" := (S ⊆ T /\ T ⊆ S) (at level 80, no associativity). *)


(* Lemma mkSetComCompl' {ts} (S : SetCom ts) : {| getConf S | getProp S |} == Sing S. *)
(* Proof. *)
(*   simpl. split; intros; induction S; auto; simpl in *; destruct H; eexists; apply H0; apply H. *)
(* Qed. *)

(* Lemma sing_set_elem {ts} (C' : Conf) (C : tuple ts -> Conf) P : *)
(*   C' ∈ {| C | P |} <-> exists xs, C xs = C' /\ P xs. *)
(* Proof. *)
(*   simpl. rewrite set_com_elem. split; intro H; decompose [ex and] H; eexists;  *)
(*   rewrite getConf_sound in *; rewrite getProp_sound in *; split; eassumption. *)
(* Qed. *)




(* Notation "{ x .. y , C | P }" := (Sing (ExSet ( fun x =>  .. (ExSet (fun y => BaseSet C P)) ..  ))) *)
(* (at level 70, x binder, y binder, no associativity). *)


(* Notation "{, C | P }" := (Sing (BaseSet C  P)) *)
(* (at level 70, no associativity). *)



(* Lemma union_incll S T : S ⊆ S ∪ T. *)
(* Proof. simpl. auto. Qed. *)

(* Lemma union_inclr S T : T ⊆ S ∪ T. *)
(* Proof. simpl. auto. Qed. *)

(* Hint Resolve union_incll union_inclr. *)

(* Definition active (c : Conf) := exists c', c ==> c'. *)

(* (* normal form, an irreducible configuration *) *)

(* Definition nf (c : Conf) := forall c', ~ (c ==> c'). *)

(* Hint Unfold active nf. *)


(* Lemma nf_trc c c' : nf c -> c =>> c' -> c = c'. *)
(* Proof. *)
(*   intros R S. destruct S using trc_ind'. reflexivity. autounfold in *. apply R in H. contradiction. *)
(* Qed. *)


(* Definition Reach (P Q : ConfSet) : Prop := forall c1, c1 ∈ P -> exists c2, c2 ∈ Q /\ c1 =>> c2. *)
(* Hint Unfold Reach. *)


(* Notation "P =|> Q" := (Reach P Q) (at level 80, no associativity). *)

(* Lemma Reach_refl_if P Q : P ⊆ Q -> P =|> Q. *)
(* Proof. *)
(*   unfold Reach. intros. exists c1.  split. auto. apply trc_refl. *)
(* Qed. *)


(* Lemma Reach_if P P' Q Q' : P =|> Q -> P' ⊆ P -> Q ⊆ Q' -> P' =|> Q'. *)
(* Proof. *)
(*   unfold Reach. intros. apply H0 in H2. apply H in H2. decompose [ex and] H2. eexists. split; eauto. *)
(* Qed. *)

(* Lemma Reach_trans P Q R : P =|> Q -> Q =|> R -> P =|> R. *)
(* Proof. *)
(*   unfold Reach. intros. apply H in H1. decompose [ex and] H1. *)
(*   apply H0 in H3. decompose [ex and] H3. eexists. split. eassumption.  *)
(*   eapply trc_trans; eassumption. *)
(* Qed. *)

(* Lemma Reach_union P P' Q Q' : P =|> P' -> Q =|> Q' -> P ∪ Q =|> P' ∪ Q'. *)
(* Proof. *)
(*   unfold Reach. intros. auto. destruct H1; [apply H in H1| apply H0 in H1]; *)
(*   decompose [ex and] H1; eauto. *)
(* Qed. *)





(* (* Lemma bidir_refl_iff P Q : P == Q -> P =|> Q. *) *)
(* (* Proof. split;[apply Reach_refl_if| apply Barred_refl_if]; tauto. Qed. *) *)


(* (* Lemma bidir_iff P P' Q Q' : P =|> Q -> P == P' -> Q == Q' -> P' =|> Q'. *) *)
(* (* Proof.  *) *)
(* (*   intros. destruct H. split; [eapply Reach_if| eapply Barred_if]; eauto; try tauto. *) *)
(* (* Qed. *) *)

(* Lemma Reach_refl P :  P =|> P. *)
(* Proof. apply Reach_refl_if. auto. Qed. *)

(* (* Lemma bidir_trans P Q R : P =|> Q -> Q =|> R -> P =|> R. *) *)
(* (* Proof. *) *)
(* (*   unfold Bidir. intros. destruct H. destruct H0. *) *)
(* (*   split. eapply Reach_trans; eassumption. eapply Barred_trans; eassumption. *) *)
(* (* Qed. *) *)

(* (* Lemma bidir_union P P' Q Q' : P =|> P' -> Q =|> Q' -> P ∪ Q =|> P' ∪ Q'. *) *)
(* (* Proof. *) *)
(* (*   unfold Bidir. intros. split. apply Reach_union; tauto. apply Barred_union; tauto. *) *)
(* (* Qed. *) *)

(* Lemma Reach_step ts (C C' : tuple ts -> Conf) (P P' : tuple ts -> Prop) T:  *)
(*   (forall x, P' x -> C x  ==> C' x) -> (forall x, P x -> P' x) ->  {| C | P |} ∪ T =|> {| C' | P' |} ∪ T. *)
(* Proof. *)
(*   unfold Reach. intros. destruct H1. *)
(*   * rewrite sing_set_elem in H1. decompose [ex and] H1. subst. exists (C' x). split.  *)
(*     - left. rewrite sing_set_elem. exists x. auto. *)
(*     - apply trc_step. auto. *)
(*   * exists c1. split; auto. *)
(* Qed. *)


(* (* The above lemma cannot be used directly in a proof *)
(* calculation. Therefore, we reformulat it using [getProp] and [getConf] *)
(* instead of the [ {| C | P |} ] construction. *) *)

(* Lemma union_sub_left S1 S2 T : S1 ⊆ S2 -> S1 ∪ T ⊆ S2 ∪ T . *)
(* Proof. *)
(*   intros. simpl in *. destruct H0; auto. *)
(* Qed. *)

(* Lemma union_eq_left S1 S2 T : S1 == S2 -> S1 ∪ T == S2 ∪ T . *)
(* Proof. *)
(*   simpl in *; split;intros; destruct H0; solve [left; destruct H; auto| right; destruct H; auto]. *)
(* Qed. *)

(* Lemma union_sub_eq S1 S2 : S1 == S2 -> S1 ⊆ S2 . *)
(* Proof. *)
(*   intros. simpl in *. destruct H. auto. *)
(* Qed. *)

(* Lemma set_eq_ref S T : S == T -> T == S. *)
(* Proof. *)
(*   intros. destruct H. split; auto. *)
(* Qed. *)


(* Corollary Reach_step' ts (S S' : SetCom ts) T : *)
(*   (forall x, getProp S' x -> getConf S x  ==> getConf S' x) ->  *)
(*   (forall x, getProp S x -> getProp S' x) ->  *)
(*   Sing S ∪ T =|> Sing S' ∪ T. *)
(* Proof. *)
(*   intros.  *)
(*   assert ({| getConf S | getProp S |} ∪ T =|> {| getConf S' | getProp S' |} ∪ T). *)
(*   apply Reach_step; auto. intros. eapply Reach_if. apply H1. apply union_sub_left. *)
(*   apply union_sub_eq. apply set_eq_ref. apply mkSetComCompl'. *)
(*   apply union_sub_left. apply union_sub_eq. apply mkSetComCompl'. *)
(* Qed. *)



(* Ltac Reach_if := intros; eapply Reach_if; eauto; simpl; tauto. *)

(* (* The following lemmas are for guiding the proof search *) *)

(* Lemma Reach_step_simp ts (S S' : SetCom ts) : *)
(*   (forall x, getProp S' x -> getConf S x  ==> getConf S' x) ->  *)
(*   (forall x, getProp S x -> getProp S' x) ->  *)
(*   Sing S =|> Sing S'. *)
(* Proof. *)
(*   intros. assert (Sing S ∪ Empty =|> Sing S' ∪ Empty). *)
(*   apply Reach_step'; auto; intros. Reach_if. *)
(* Qed. *)

(* Lemma Reach_assoc1 S1 S2 S T : S1 ∪ (S ∪ T) =|> S2 ∪ (S ∪ T) -> (S1 ∪ S) ∪ T =|> (S2 ∪ S) ∪ T. *)
(* Proof. Reach_if. Qed. *)

(* Lemma Reach_assoc2 S1 S2 S T : S1 ∪ (S ∪ T) =|> S2 ∪ (S ∪ T) -> (S ∪ S1) ∪ T =|> (S ∪ S2) ∪ T. *)
(* Proof. Reach_if. Qed. *)

(* Lemma Reach_comm S1 S2 T : S1 ∪ T =|> S2 ∪ T -> T ∪ S1 =|> T ∪ S2. *)
(* Proof. Reach_if. Qed. *)


(* Definition determ {A} (R : A -> A -> Prop) : Prop := forall C C1 C2, R C C1 -> R C C2 -> C1 = C2. *)

(* Definition trc' C C' :=  C =>> C' /\ ~ exists C'', C' ==> C''. *)

(* Notation "x =>>! y" := (trc' x y) (at level 80, no associativity). *)


(* Lemma determ_factor C1 C2 C3 : determ Rel -> C1 ==> C2 -> C1 =>>! C3 -> C2 =>> C3. *)
(* Proof. *)
(*   unfold determ. intros. destruct H1. *)
(*   destruct H1 using trc_ind'. *)
(*   - exfalso. apply H2. eexists. eassumption. *)
(*   - assert (c2 = C2). eapply H. apply H1. apply H0. subst. auto. *)
(* Qed. *)


(* Lemma determ_trc : determ Rel -> determ trc'. *)
(* Proof. *)
(*   intros. unfold determ. intros. destruct H0. induction H0 using trc_ind'.  *)
(*   - destruct H1. destruct H0 using trc_ind'. reflexivity. exfalso. apply H2. eexists. eassumption. *)
(*   - apply IHtrc. apply H2. split. eapply determ_factor; eassumption. destruct H1. assumption. *)
(* Qed. *)

End MetaTheory.
