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


Ltac unfold_limits_in H :=
  unfold is_lim_seq in H; unfold eventually in H; unfold filterlim in H;
  unfold filter_le in H; unfold filtermap in H; unfold Rbar_locally in H;
  unfold locally in H; unfold ball in H; simpl in H; unfold AbsRing_ball in H; simpl in H.


Ltac unfold_limits_all :=
  unfold is_lim_seq in *; unfold eventually in *; unfold filterlim in *;
  unfold filter_le in *; unfold filtermap in *; unfold Rbar_locally in *;
  unfold locally in *; unfold ball in *; simpl in *; unfold AbsRing_ball in *; simpl in *.


Tactic Notation "unfold_limits" "in" hyp(l) := unfold_limits_in l.
Tactic Notation "unfold_limits" "in" "*" := unfold_limits_all.


Ltac unfold_complexity :=
  unfold BigO; unfold LittleO; unfold BigOmega; unfold LittleOmega; unfold BigTheta.


Ltac unfold_complexity_in H :=
  unfold BigO in H; unfold LittleO in H; unfold BigOmega in H; unfold LittleOmega in H; unfold BigTheta in H.

Ltac unfold_complexity_all :=
  unfold BigO in *; unfold LittleO in *; unfold BigOmega in *; unfold LittleOmega in *; unfold BigTheta in *.


Tactic Notation "unfold_complexity" "in" hyp(l) := unfold_complexity_in l.
Tactic Notation "unfold_complexity" "in" "*" := unfold_complexity_all.


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


Lemma gt_eq_ge_R :
  forall (a b : R),
    (a > b \/ a = b)%R <-> (a >= b)%R.
Proof.
  intros a b. split; intros H; lra.
Qed.


Lemma gt_eq_ge_nat :
  forall (a b : nat),
    (a > b \/ a = b)%nat <-> (a >= b)%nat.
Proof.
  intros a b. split; intros H; omega.
Qed.


Lemma lt_eq_le_R' :
  forall (a b : R),
    (a < b \/ b = a)%R <-> (a <= b)%R.
Proof.
  intros a b. split; intros H; lra.
Qed.


Lemma lt_eq_le_nat' :
  forall (a b : nat),
    (a < b \/ b = a)%nat <-> (a <= b)%nat.
Proof.
  intros a b. split; intros H; omega.
Qed.


Lemma gt_eq_ge_R' :
  forall (a b : R),
    (a > b \/ b = a)%R <-> (a >= b)%R.
Proof.
  intros a b. split; intros H; lra.
Qed.


Lemma gt_eq_ge_nat' :
  forall (a b : nat),
    (a > b \/ b = a)%nat <-> (a >= b)%nat.
Proof.
  intros a b. split; intros H; omega.
Qed.


Ltac ineq_fix :=
  repeat match goal with
         | H : context[(?a < ?b \/ ?a = ?b)%R] |- _ => rewrite lt_eq_le_R in H
         | H : _ |- context[(?a < ?b \/ ?a = ?b)%R] => rewrite lt_eq_le_R
         | H : context[(?a < ?b \/ ?a = ?b)%nat] |- _ => rewrite lt_eq_le_nat in H
         | H : _ |- context[(?a < ?b \/ ?a = ?b)%nat] => rewrite lt_eq_le_nat

         | H : context[(?a > ?b \/ ?a = ?b)%R] |- _ => rewrite gt_eq_ge_R in H
         | H : _ |- context[(?a > ?b \/ ?a = ?b)%R] => rewrite gt_eq_ge_R
         | H : context[(?a > ?b \/ ?a = ?b)%nat] |- _ => rewrite gt_eq_ge_nat in H
         | H : _ |- context[(?a > ?b \/ ?a = ?b)%nat] => rewrite gt_eq_ge_nat

         | H : context[(?a < ?b \/ ?b = ?a)%R] |- _ => rewrite lt_eq_le_R' in H
         | H : _ |- context[(?a < ?b \/ ?b = ?a)%R] => rewrite lt_eq_le_R'
         | H : context[(?a < ?b \/ ?b = ?a)%nat] |- _ => rewrite lt_eq_le_nat' in H
         | H : _ |- context[(?a < ?b \/ ?b = ?a)%nat] => rewrite lt_eq_le_nat'

         | H : context[(?a > ?b \/ ?b = ?a)%R] |- _ => rewrite gt_eq_ge_R' in H
         | H : _ |- context[(?a > ?b \/ ?b = ?a)%R] => rewrite gt_eq_ge_R'
         | H : context[(?a > ?b \/ ?b = ?a)%nat] |- _ => rewrite gt_eq_ge_nat' in H
         | H : _ |- context[(?a > ?b \/ ?b = ?a)%nat] => rewrite gt_eq_ge_nat'
         end.


Ltac unfold_ord :=
  unfold ge_ord; unfold gt_ord; unfold le_ord; unfold lt_ord; simpl; ineq_fix.


Ltac unfold_ord_in H :=
  unfold ge_ord in H; unfold gt_ord in H; unfold le_ord in H; unfold lt_ord in H; simpl in H; ineq_fix.


Ltac unfold_ord_all :=
  unfold ge_ord in *; unfold gt_ord in *; unfold le_ord in *; unfold lt_ord in *; simpl in *; ineq_fix.


Tactic Notation "unfold_ord" "in" hyp(l) := unfold_ord_in l.
Tactic Notation "unfold_ord" "in" "*" := unfold_ord_all.

Ltac ord_lra :=
  unfold_ord in *; lra.
