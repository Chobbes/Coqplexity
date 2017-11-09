Require Import classes_sigma.
Require Import ord.

Require Import Coquelicot.Coquelicot.
Require Import Psatz.


Ltac unfold_limits :=
  unfold is_lim_seq; unfold eventually; unfold filterlim;
  unfold filter_le; unfold filtermap; unfold Rbar_locally;
  unfold locally; unfold ball; simpl; unfold AbsRing_ball; simpl.


Ltac unfold_complexity :=
  unfold BigO; unfold LittleO; unfold BigOmega; unfold LittleOmega; unfold BigTheta.


Ltac unfold_ord :=
  unfold ge_ord; unfold gt_ord; unfold le_ord; unfold lt_ord; simpl.


Ltac unfold_ord_in H :=
  unfold ge_ord in H; unfold gt_ord in H; unfold le_ord in H; unfold lt_ord in H; simpl in H.


Ltac unfold_ord_all :=
  unfold ge_ord in *; unfold gt_ord in *; unfold le_ord in *; unfold lt_ord in *; simpl in *.


Tactic Notation "unfold_ord" "in" hyp(l) := unfold_ord_in l.
Tactic Notation "unfold_ord" "in" "*" := unfold_ord_all.

Ltac ord_lra :=
  unfold_ord in *; lra.
