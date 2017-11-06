Require Import Coquelicot.Coquelicot.
Require Import classes_sigma.

Ltac unfold_limits :=
  unfold is_lim_seq; unfold eventually; unfold filterlim;
  unfold filter_le; unfold filtermap; unfold Rbar_locally;
  unfold locally; unfold ball; simpl; unfold AbsRing_ball; simpl.

Ltac unfold_complexity :=
  unfold BigO; unfold LittleO; unfold BigOmega; unfold LittleOmega; unfold BigTheta.
