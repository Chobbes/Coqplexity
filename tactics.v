Require Import classes_sigma.
Require Import ord.

Require Import Coq.Reals.Reals.
Require Import Coquelicot.Coquelicot.
Require Import Psatz.
Require Import Omega.


Ltac unfold_limits :=
  unfold is_lim_seq; unfold eventually; unfold filterlim;
  unfold filter_le; unfold filtermap; unfold Rbar_locally;
  unfold locally; unfold ball; simpl; unfold AbsRing_ball; simpl.


Ltac unfold_complexity :=
  unfold BigO; unfold LittleO; unfold BigOmega; unfold LittleOmega; unfold BigTheta.


Lemma lt_eq_le_R :
  forall (a b : R),
    (a < b \/ a = b)%R <-> (a <= b)%R.
Proof.
  intros a b. split; intros H; lra.
Qed.


Lemma lt_eq_le_nat :
  forall (a b : nat),
    (a < b \/ a = b)%nat <-> (a <= b)%nat.
Proof.
  intros a b. split; intros H; omega.
Qed.


Ltac lt_fix :=
  repeat match goal with
         | H : context[(?a < ?b \/ ?a = ?b)%R] |- _ => rewrite lt_eq_le_R in H
         | H : _ |- context[(?a < ?b \/ ?a = ?b)%R] => rewrite lt_eq_le_R
         | H : context[(?a < ?b \/ ?a = ?b)%nat] |- _ => rewrite lt_eq_le_nat in H
         | H : _ |- context[(?a < ?b \/ ?a = ?b)%nat] => rewrite lt_eq_le_nat
         end.


Ltac unfold_ord :=
  unfold ge_ord; unfold gt_ord; unfold le_ord; unfold lt_ord; simpl; lt_fix.


Ltac unfold_ord_in H :=
  unfold ge_ord in H; unfold gt_ord in H; unfold le_ord in H; unfold lt_ord in H; simpl in H; lt_fix.


Ltac unfold_ord_all :=
  unfold ge_ord in *; unfold gt_ord in *; unfold le_ord in *; unfold lt_ord in *; simpl in *; lt_fix.


Tactic Notation "unfold_ord" "in" hyp(l) := unfold_ord_in l.
Tactic Notation "unfold_ord" "in" "*" := unfold_ord_all.

Ltac ord_lra :=
  unfold_ord in *; lra.
