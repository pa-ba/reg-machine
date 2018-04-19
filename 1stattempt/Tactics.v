Require Export SetOf.


Require Import List.
Import ListNotations.

Definition Admit {A} : A. admit. Admitted. 



Ltac destruct_tuple := idtac; match goal with
  | [l : tuple nil |- _ ] => destruct l; destruct_tuple
  | [l : tuple (_ :: _) |- _ ] => destruct l; destruct_tuple
  | _ => idtac
end.



Ltac lift_union t := first [apply sub_union; first [apply sub_refl| lift_union t]| t].


Ltac dist' ev := simpl; intros; subst; ev;
                match goal with
                  | [ H: and _ _ |- _ ] => destruct H; dist' ev
                  | [ H: ex _ |- _ ] => destruct H; dist' ev
                  | [ H: or _ _ |- _ ] => destruct H; dist' ev
                  | [ |- and _ _ ] => split; dist' ev
                  | [ |- _ <-> _ ] => split; dist' ev
                  | [ |- ex _ ] => eexists; dist' ev
                  | [ |- or _ _] => solve [right;dist' ev|left; dist' ev]
                end.

Ltac dist := dist' eauto.



(* Ltac barred_nostep := apply barred_here; dist. *)
(* Ltac barred_step :=  *)
(*   let h := fresh "barred_step" in *)
(*   apply barred_next; [intro; intro h; inversion h; subst; clear h| *)
(*                       unfold active; *)
(*                         repeat (match goal with *)
(*                                   | [T : and _ _ |- _] => destruct T *)
(*                                   | [T : ex _ |- _] => destruct T *)
(*                                 end); *)
(*                                eexists;econstructor;eauto]. *)


(* Ltac barred_onestep := barred_step; barred_nostep. *)
(* Ltac barred_tac := solve [barred_onestep | barred_nostep |  *)
(*                           barred_step ; solve [barred_nostep | barred_step ; solve [barred_nostep | barred_onestep]]]. *)



Ltac check_exp x y := let h := fresh "check" in assert (h: x = y) by reflexivity; clear h.

Ltac check_rel Bidir Rel := first [check_exp Bidir Rel|
                             fail 2 "wrong goal; expected relation =>> but found" Rel].

Tactic Notation "[]" := apply sub_refl.


Tactic Notation  (at level 2)    "=" "{?}" constr(e2) := 
  match goal with
    | [|- ?Rel ?lhs ?rhs] => check_rel Subset Rel;
                            let h := fresh "rewriting" in 
                            assert(h : forall c, c ∈ e2  <-> c ∈ rhs)
      | _ => fail 1 "goal is not a VM"
    end.



Tactic Notation  (at level 2)    ">=" "{?}" constr(e2) := 
  match goal with
    | [|- ?Rel ?lhs ?rhs] => check_rel Subset Rel;
        first [let h := fresh "rewriting" in 
               assert(h : Subset e2 rhs) | fail 2]
      | _ => fail 1 "goal is not a VM"
    end.

Tactic Notation  (at level 2)    ">=" "{"tactic(t1) "}" constr(e2) := 
  match goal with
    | [|- ?Rel ?lhs ?rhs] => check_rel Subset Rel;
        first [let h := fresh "rewriting" in 
               assert(h : Subset e2 rhs) by (lift_union t1); 
                 apply (fun x => sub_trans _ _ _ x h); clear h | fail 2]
      | _ => fail 1 "goal is not a VM"
    end.

Tactic Notation  (at level 2)    ">=" "{{"tactic(t1) "}}" constr(e2) := 
  match goal with
    | [|- ?Rel ?lhs ?rhs] => check_rel Subset Rel;
        first [let h := fresh "rewriting" in 
               assert(h : Subset e2 rhs) by t1; 
                 apply (fun x => sub_trans _ _ _ x h); clear h | fail 2]
      | _ => fail 1 "goal is not a VM"
    end.


Tactic Notation  (at level 2)    "=" "{"tactic(t) "}" constr(e) := 
  >= {{ apply sub_eq; dist' t }} e .


Tactic Notation  (at level 2)  "begin" constr(rhs) :=
  match goal with
    | [|- ?Rel ?lhs ?rhs'] => check_rel Subset Rel; check_exp rhs rhs'
    | _ => fail 1 "rhs does not match"
  end.
