Require Import Coq.Program.Basics.
Require Import Coq.Reals.Reals.
Require Import Coq.Reals.RIneq.
Require Import Coquelicot.Coquelicot.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import classes_sigma.
Require Import Psatz.
Require Import Omega.
Require Import classes_sigma.
Require Import tactics.
Require Import ord.


Local Open Scope Ord_scope.


Lemma BigTheta_BigO :
  forall {A} `{Ord A} (f g : A -> R),
    f ∈ Θ(g) -> f ∈ O(g).
Proof.
  unfold BigTheta. unfold BigO.
  intros A HOrd f g [c1 [c2 [n0 HTheta]]].
  exists c2. exists n0.
  intros n Hn_n0.
  pose proof HTheta n Hn_n0 as [H0 H1].

  simpl in *. assumption.
Qed.


Lemma BigTheta_BigOmega :
  forall {A} `{Ord A} (f g : A -> R),
    f ∈ Θ(g) -> f ∈ Ω(g).
Proof.
  unfold BigTheta. unfold BigOmega.
  intros A HOrd f g [c1 [c2 [n0 HTheta]]].
  exists c1. exists n0.
  intros n Hn_n0.
  destruct c1 as [c1 Hc1]. simpl in *.
  pose proof HTheta n Hn_n0 as [Hc1g Hc2g].

  apply Rle_ge.
  assumption.
Qed.


Theorem BigTheta_is_BigO_and_BigOmega :
  forall {A} `{Ord A} (f g : A -> R),
    f ∈ O(g) /\ f ∈ Ω(g) <-> f ∈ Θ(g).
Proof.
  intros A HOrd f g.
  split. {
    intros [[sc2 [n2 HO]] [sc1 [n1 HOmega]]].
    simpl in *.

    unfold BigTheta.
    
    exists sc1. exists sc2. exists (max n1 n2).

    intros n Hmax.
    apply max_lub_lt_iff in Hmax as [Hn1 Hn2].
    destruct sc1 as [c1 Hc1]. destruct sc2 as [c2 Hc2]. simpl in *.

    pose proof HOmega n Hn1 as Hf_c1_g.
    pose proof HO n Hn2 as Hf_c2_g.

    unfold_ord in *.

    split; assumption.
  } {
    auto using (@BigTheta_BigO A), (@BigTheta_BigOmega A).
  }
Qed.


Lemma gt0 : (1 > 0)%R. Proof. lra. Qed.


Theorem LittleO_BigO :
  forall {A} `{Ord A} (f g : A -> R),
    f ∈ o(g) -> f ∈ O(g).
Proof.
  unfold LittleO. unfold BigO.
  intros A HOrd f g Ho.

  pose proof (exist _ 1%R gt0) as sc.
  
  pose proof Ho sc as Ho. destruct Ho as [n0 Ho].
  exists sc. exists n0.

  unfold_ord in *.

  intros n H.
  apply Rlt_le. auto.
Qed.


Theorem Limit_LittleO :
  forall (f g : nat -> R),
    (exists n0, forall n, n > n0 -> Rabs (g n) > 0) ->
    is_lim_seq (fun n => (Rabs (f n) / Rabs (g n))%R) 0%R -> f ∈ o(g).
Proof.
  unfold_limits. intros f g [n0 Hres] H.
  unfold_complexity. intros [c Hc]. simpl in *.

  pose proof H (fun fg => (fg < c)%R) as H. simpl in H.

  destruct H. exists (mkposreal c Hc).
  intros y H. simpl in *. apply Rabs_def2 in H as [Hyc Hcy].

  replace y with (minus y 0)%R.
  apply Hyc. replace 0%R with (zero : R). apply minus_zero_r.
  reflexivity.

  exists (Nat.max x n0).

  intros n Hmax. apply Nat.max_lub_lt_iff in Hmax as [Hx Hn0].
  apply Nat.lt_le_incl in Hx.

  pose proof H n Hx as H.

  apply Rlt_div_l. apply Hres. auto.
  assumption.
Qed.


Theorem LittleO_Limit :
  forall (f g : nat -> R),
    f ∈ o(g) ->
    is_lim_seq (fun n => (Rabs (f n) / Rabs (g n))%R) 0%R.
Proof.
  unfold_complexity.
  unfold_limits.
  intros f g Ho P Hball.

  unfold locally in Hball. simpl in *. destruct Hball as [eps Hball].
  unfold ball in *. simpl in *. unfold AbsRing_ball in *. simpl in *.

  destruct eps as [eps Heps]. simpl in *.
  pose proof Ho (exist _ eps Heps) as Ho. destruct Ho as [n0 Ho].

  exists (S n0).
  intros n Hn0n. simpl in *.

  apply Hball.
  replace 0%R with (zero: R); try reflexivity. rewrite minus_zero_r.

  apply -> Nat.le_succ_l in Hn0n.
  pose proof Ho n Hn0n as Hfg.

  unfold_ord in *.
  assert (0 <= Rabs (f n)) as H0f by apply Rabs_pos.

  apply Rabs_def1.
  apply Rlt_div_l.
  - pose proof Rle_lt_trans 0 (Rabs (f n)) (eps * Rabs (g n))%R H0f Hfg.
    apply (Rmult_lt_reg_r eps); lra.
  - lra.
  - apply Rlt_div_r; try ord_lra. pose proof Rle_lt_trans 0 (Rabs (f n)) (eps * Rabs (g n))%R H0f Hfg.
    apply (Rmult_lt_reg_r eps); lra.
Qed.


(* Converse is not necessarily true, since the limit need not exist. *)
Theorem Limit_BigTheta :
  forall (f g : nat -> R),
    (exists n0, forall n, n > n0 -> Rabs (g n) > 0) ->
    (exists (c : R), (c > 0)%R /\ is_lim_seq (fun n => (Rabs (f n) / Rabs (g n))%R) c) ->
    f ∈ Θ(g).
Proof.
  unfold_limits.
  intros f g [n Hres] [c [Hc Hlim]].

  assert (c/2 > 0)%R as Hc_2 by lra.
  pose proof Hlim (fun fg => (c/2 < fg < 3 * c / 2)%R) as H. simpl in H.
  destruct H.

  - exists (mkposreal (c/2)%R Hc_2). intros y H. simpl in *.
    apply Rabs_lt_between in H as [Hl Hr].

    apply Rlt_minus_l in Hl.
    apply Rlt_minus_l in Hr.

    rewrite <- Ropp_plus_minus_distr in Hl.
    rewrite Ropp_plus_distr in Hl. rewrite Ropp_involutive in Hl.

    lra.
  - unfold_complexity.
    rename x into N.

    assert (3 * c / 2 > 0)%R as H3c_2 by lra.
    exists (exist _ (c/2)%R Hc_2). exists (exist _ (3 * c / 2)%R H3c_2). exists (Nat.max N n).

    simpl.

    intros n0 Hmax. apply Nat.max_lub_lt_iff in Hmax as [HN Hn0].

    pose proof Hres n0 Hn0 as Hres.

    apply Nat.lt_le_incl in HN.
    pose proof H n0 HN as [Hc_fg Hfg_c].

    split.
    + apply Rlt_le. apply Rlt_div_r; assumption.
    + apply Rle_div_l; lra.
Qed.


Lemma lt_0_Ropp :
  forall (b : R),
    (b < 0)%R -> exists c, (Ropp c = b /\ c > 0)%R.
Proof.
  intros b H.
  exists (-b). split; lra.
Qed.


Lemma c_0_lt :
  forall (x : R),
    (0 < x)%R -> exists c, (0 < c < x)%R.
Proof.
  intros x H. exists (x/2).
  lra.
Qed.


Lemma lt_0_c :
  forall (x : R),
    (exists c, (0 < c < x)%R) -> (0 < x)%R.
Proof.
  intros x [c [H0c Hcx]].
  lra.
Qed.


Lemma gt_neq_1 :
  forall (n : nat),
    (n > 0 -> n <> 1 -> 1 < n)%nat.
Proof.
  intros n Hgt0 Hne1.
  induction n; intuition.
Qed.


Lemma INR_1:
  1%R = INR 1.
Proof.
  reflexivity.
Qed.


Theorem BigO_power_nat :
  forall (a b : nat),
    a <= b -> (fun (x : nat) => (INR x) ^ a) ∈ O(fun (x : nat) => (INR x) ^ b).
Proof.
  intros a b H.
  unfold_complexity.

  exists (exist _ 1 gt0). exists 0%nat.
  intros n H0.

  simpl.
  unfold_ord in *.

  rewrite Rmult_1_l.

  pose proof pow_le (INR n) a (pos_INR n) as Ha.
  pose proof pow_le (INR n) b (pos_INR n) as Hb.
  apply Rle_ge in Ha. apply Rle_ge in Hb.

  pose proof Rabs_right (INR n ^ a) Ha as Habs_a.
  pose proof Rabs_right (INR n ^ b) Hb as Habs_b.

  rewrite Habs_a. rewrite Habs_b.

  (* pow_le: forall (a : R) (n : nat), (0 <= a)%R -> (0 <= a ^ n)%R *)
  apply Rle_pow. rewrite INR_1. apply le_INR.
  - omega.
  - assumption.
Qed.


Lemma f_pow_1 :
  (fun (x : nat) => INR x) = (fun (x : nat) => INR x ^ 1).
Proof.
  apply functional_extensionality.
  intros x.

  symmetry.
  apply pow_1.
Qed.


Theorem BigO_power_nat_1 :
  forall (b : nat),
    1%nat <= b -> (fun (x : nat) => INR x) ∈ O(fun (x : nat) => (INR x) ^ b).
Proof.
  intros b H.
  replace (fun (x : nat) => INR x) with (fun (x : nat) => INR x ^ 1) by (symmetry; apply f_pow_1).
  apply BigO_power_nat.
  assumption.
Qed.


Lemma f_lambda :
  forall {A} {B} (f : A -> B),
    (fun x => f x) = f.
Proof.
  intros A B f.
  apply functional_extensionality.
  reflexivity.
Qed.


Theorem BigO_power_nat_inr :
  forall (b : nat),
    1%nat <= b -> INR ∈ O(fun (x : nat) => (INR x) ^ b).
Proof.
  intros b H.
  unfold_complexity.
  apply BigO_power_nat_1.
  assumption.
Qed.


Theorem BigO_const_nat :
  forall (c : R),
    (fun (n : nat) => c) ∈ O(fun x => INR x).
Proof.
  intros c.
  unfold_complexity.

  pose proof Rmax_r (Rabs c) 1%R.
  assert (0 < Rmax (Rabs c) 1)%R as Hmax by lra.

  exists (exist _ (Rmax (Rabs c) 1) Hmax). exists 0%nat.

  intros n Hn0.
  simpl in *.

  apply (Rle_trans _ (Rmax (Rabs c) 1)).
  - apply Rmax_l.
  - assert (1 <= n)%nat as H1n by omega.
    apply (Rle_trans _ (Rmax (Rabs c) 1 * 1)); try lra.
    apply Rmult_le_compat_l. lra.  apply le_INR in H1n.
    rewrite Rabs_pos_eq. rewrite INR_1. assumption.
    apply pos_INR.
Qed.


Lemma div_cancel :
  forall c k,
    k <> 0 ->
    c / k * k = c.
Proof.
  intros c k H.
  field. assumption.
Qed.


Theorem BigO_const_mult :
  forall (k : R) f g,
    k <> 0 ->
    f ∈ O(g) ->
    f ∈ O(fun n => k * g n).
Proof.
  unfold_complexity.
  intros k f g Hkne0 [[c Hc] [n0 Hfg]].

  simpl in *.

  assert ((c / Rabs k) > 0)%R.
  apply Rlt_div_r. pose proof Rabs_pos k.

  destruct H.
  - assumption.
  - symmetry in H. apply Rabs_eq_0 in H. contradiction.
  lra.

  exists (exist _ (c / Rabs k) H). exists n0.

  intros n H0. simpl. rewrite Rabs_mult.
  rewrite <- Rmult_assoc.

  apply Rabs_no_R0 in Hkne0.
  rewrite div_cancel; try assumption.
  auto.
Qed.


Theorem BigO_const_mult_lambda :
  forall {A} `{Ord A} k (h f g : A -> R),
    k <> 0 ->
    (forall n, h n = k) ->
    f ∈ O(g) ->
    f ∈ O(fun n => h n * g n).
Proof.
  unfold_complexity.
  intros A H k h f g Hkne0 Hhk [[c Hc] [n0 Hfg]].

  simpl in *.

  assert ((c / Rabs k) > 0)%R.
  apply Rlt_div_r. pose proof Rabs_pos k.

  destruct H0.
  - assumption.
  - symmetry in H0. apply Rabs_eq_0 in H0. contradiction.
  lra.

  exists (exist _ (c / Rabs k) H0). exists n0.

  intros n H1. simpl. rewrite Rabs_mult.
  rewrite <- Rmult_assoc.

  apply Rabs_no_R0 in Hkne0.
  rewrite Hhk.
  rewrite div_cancel; try assumption.
  auto.
Qed.


Theorem BigO_const_mult_lambda_l :
  forall {A} `{Ord A} k (h f g : A -> R),
    k <> 0 ->
    (forall n, h n = k) ->
    f ∈ O(g) ->
    (fun n => h n * f n) ∈ O(g).
Proof.
  unfold_complexity.
  intros A H k h f g Hkne0 Hhk [[c Hc] [n0 Hfg]].

  simpl in *.

  assert ((c * Rabs k) > 0)%R.
  apply Rmult_lt_0_compat; try lra.  pose proof Rabs_pos k.

  destruct H0.
  - assumption.
  - symmetry in H0. apply Rabs_eq_0 in H0. contradiction.

  exists (exist _ (c * Rabs k) H0). exists n0.

  intros n H1. simpl. rewrite Rabs_mult.
  rewrite Hhk.
  replace (c * Rabs k) with (Rabs k * c) by apply Rmult_comm.
  rewrite Rmult_assoc.

  apply Rmult_le_compat_l; try apply Rabs_pos.
  
  unfold_ord in *.
  unfold Rle.
  auto.
Qed.


Theorem BigO_refl :
  forall {A} `{Ord A} (a : A) (f : A -> R),
    f ∈ O(f).
Proof.
  intros A HOrd a f.

  unfold_complexity.

  exists (exist _ 1 gt0). exists a.

  simpl. intros n Hnn0.
  rewrite Rmult_1_l. 
  apply Rle_refl.
Qed.


Theorem BigO_refl_lambda :
  forall {A} `{Ord A} (a : A) (f : A -> R),
    f ∈ O(fun n => f n).
Proof.
  intros A HOrd a f.

  unfold_complexity.
  apply BigO_refl.
  exact a.
Qed.



Theorem BigO_trans :
  forall {A} `{Ord A} (f1 f2 g : A -> R),
    f1 ∈ O(f2) -> f2 ∈ O(g) -> f1 ∈ O(g).
Proof.
  unfold_complexity.
  intros A HOrd f1 f2 g [[c1 Hc1] [n1 Hf1]] [[c2 Hc2] [n2 Hf2]].

  simpl in *.
  unfold_ord in *.

  assert (c1 * c2 > 0)%R as Hc by (apply Rmult_lt_0_compat; lra).
  exists (exist _ (c1 * c2)%R Hc).

  exists (max n1 n2). intros n Hmax. apply max_lub_lt_iff in Hmax as [Hn1 Hn2].

  pose proof Hf1 n Hn1 as Hf1f2.
  pose proof Hf2 n Hn2 as Hf2g.

  simpl in *.
  ineq_fix.

  apply (Rle_trans (Rabs (f1 n)) (c1 * Rabs (f2 n))). assumption.
  replace (c1 * c2 * Rabs (g n))%R with (c1 * (c2 * Rabs (g n)))%R by lra.
  apply (Rmult_le_compat_l c1 (Rabs (f2 n)) (c2 * Rabs (g n))); lra.
Qed.


Theorem BigO_add :
  forall {A} `{Ord A} (f1 f2 g : A -> R),
    f1 ∈ O(g) -> f2 ∈ O(g) -> (fun n => f1 n + f2 n) ∈ O(g).
Proof.
  unfold_complexity.
  intros A HOrd f1 f2 g [[c1 Hc1] [n1 Hf1]] [[c2 Hc2] [n2 Hf2]].

  assert (c1 + c2 > 0)%R as Hc by lra.
  exists (exist _ (c1 + c2)%R Hc).

  exists (max n1 n2). intros n Hmax. apply max_lub_lt_iff in Hmax as [Hn1 Hn2].

  pose proof (Hf1 n Hn1) as Hf1.
  pose proof (Hf2 n Hn2) as Hf2.

  simpl in *.
  unfold_ord in *.

  apply (Rle_trans (Rabs (f1 n + f2 n)) (Rabs (f1 n) + Rabs (f2 n)) ((c1 + c2) * Rabs (g n))).
  apply Rabs_triang. lra.
Qed.


Lemma Rpower_ln  :
  forall a b,
    ln (Rpower a b) = b * ln a.
Proof.
  intros a b.
  unfold Rpower.
  rewrite ln_exp.
  reflexivity.
Qed.


Lemma Rpower_pos :
  forall a b,
    0 < Rpower a b.
Proof.
  intros a b.
  apply exp_pos.
Qed.


Lemma ln_gt_0 :
  forall a,
    (a > 1 -> ln a > 0)%R.
Proof.
  intros a H.
  apply exp_lt_inv.
  rewrite exp_ln; try lra.
  rewrite exp_0. assumption.
Qed.


Lemma BigO_ln_x :
  ln ∈ O(id).
Proof.
  unfold_complexity.
  unfold_ord.
  exists (exist _ 1 gt0). exists 1.
  intros n H.

  pose proof ln_gt_0 n H as Hln_pos.
  unfold id.
  repeat rewrite Rabs_right; try lra.

  simpl.
  left. rewrite Rmult_1_l.

  apply exp_lt_inv.
  rewrite exp_ln; try lra.

  apply Rlt_trans with (r2:=1+n).

  - lra.
  - apply exp_ineq1. lra.
Qed.


Lemma ln_x_le_x :
  forall x,
    (0 < x)%R ->
    (ln x <= x)%R.
Proof.
  left. apply exp_lt_inv.
  rewrite exp_ln.
  - apply Rlt_trans with (r2:=1+x).
    lra. apply exp_ineq1. assumption.
  - assumption.
Qed.


Ltac calvin :=
  unfold_complexity in *;
  unfold_ord in *;
  repeat (ineq_fix;
   match goal with
   (* Get rid of scalar identity *)
   | |- context[1 * ?x] => repeat rewrite Rmult_1_l
   | H : context[1 * ?x] |- _ => repeat rewrite Rmult_1_l in H

   (* Identity rules *)
   | |- context[id ?n] => replace (id n) with n by reflexivity

   (* Unfold compositions *)
   | |- context[compose] => repeat unfold compose
   | H : context[compose] |- _ => repeat unfold compose

   (* Destruct existential quantification *)
   | H : exists x, _ |- _ => destruct H

   (* Big O stuff *)
   | H : ?T |- exists (sc : ?T), _ => try (exists H; calvin)
   | |- exists (sc : {c | (0<c)%R}), _ => try (exists (exist _ 1 gt0); calvin)
   | |- exists (sc : {c | (c>0)%R}), _ => try (exists (exist _ 1 gt0); calvin)

   | |- forall x, _ => intros
   | |- _ -> _ => intros

   (* Logs and exponents *)
   | |- (ln ?x <= ?x)%R => apply ln_x_le_x
   | |- (ln ?x > 0)%R => eapply ln_gt_0
   | |- (ln ?x >= 0)%R => left; eapply ln_gt_0

   (* Powers *)
   | |- (?n ^ ?a <= ?n ^ ?b)%R => apply Rle_pow
   | |- (INR ?n ^ ?b >= 0)%R => apply Rle_ge; apply pow_le; apply pos_INR
   | |- (0 <= INR ?n ^ ?b)%R => apply pow_le; apply pos_INR

   (* Square roots *)
   | |- (sqrt ?n <= ?n)%R => left; apply sqrt_less_alt
   | |- (sqrt ?x >= 0)%R => auto using sqrt_pos, Rle_ge
   | |- (sqrt ?x <= 0)%R => auto using sqrt_pos, Rle_ge

   (* Inequality stuff *)
   | |- (1 <= INR ?n)%R => replace 1%R with (INR 1) by reflexivity; apply le_INR; omega
   | |- (1 < INR ?n)%R => replace 1%R with (INR 1) by reflexivity; apply lt_INR; omega

   (* Rabs rules *)
   | H : (_ < ?x)%R |- context[Rabs ?x] => progress replace (Rabs x) with x by (rewrite Rabs_right; lra)
   | H : (_ <= ?x)%R |- context[Rabs ?x] => progress replace (Rabs x) with x by (rewrite Rabs_right; lra)
   | H : (_ > ?x)%R |- context[Rabs ?x] => progress replace (Rabs x) with x by (rewrite Rabs_right; lra)
   | H : (_ >= ?x)%R |- context[Rabs ?x] => progress replace (Rabs x) with x by (rewrite Rabs_right; lra)
   | |- context[Rabs ?x] => rewrite Rabs_right

   (* Modus ponens *)
   | H1 : (forall (n : ?A), _), H2 : ?A |- _ => solve [specialize (H1 H2); calvin]
   | H1 : ?A -> ?B, H2 : ?A |- _ => solve [specialize (H1 H2); calvin]

   (* Might as well try solvers *)
   | |- _ => lia
   | |- _ => lra
   | |- _ => nia
   | |- _ => nra
   | |- _ => omega
end).


Lemma BigO_ln :
  forall {A} `{Ord A} (f : A -> R),
  (exists (n0 : A), forall n, n > n0 -> 1 < f n) ->
  compose ln f ∈ O(f).
Proof.
  calvin.
Qed.


Theorem sqrt_big_o :
  sqrt ∈ O(id).
Proof.
  calvin. exists 1.
  calvin.
Qed.


Ltac big_O_additive :=
  repeat apply BigO_add.


Ltac pow_match :=
  match goal with
  | |- INR ∈ O(fun k => INR k ^ ?b) => apply BigO_power_nat_inr; unfold_ord; omega
  | |- (fun n => INR n) ∈ O(fun k => INR k ^ ?b) => apply BigO_power_nat_1; unfold_ord; omega
  | |- (fun n => INR n ^ ?a) ∈ O(fun k => INR k ^ ?b) => apply BigO_power_nat; unfold_ord; omega
  end.


Ltac const_match :=
  match goal with
  | |- (fun x : nat => ?h * _) ∈ O(?f) => apply (BigO_const_mult_lambda_l h); try lra; try reflexivity
  end.


Ltac const_elim :=
  repeat match goal with
  | |- ?f ∈ O(fun x => ?h * _) => apply BigO_const_mult_lambda with (k:=h); try lra; try reflexivity
  end.


Ltac big_O_refl :=
  match goal with
  | |- ?f ∈ O(?f) => try apply (BigO_refl 0%R); try apply (BigO_refl 0%nat)
  | |- ?f ∈ O(fun x => ?f x) => try apply (BigO_refl_lambda 0%R); try apply (BigO_refl_lambda 0%nat)
  end.


Ltac big_O_polynomial :=
  big_O_additive; try const_match; try pow_match; try big_O_refl.


Ltac big_O :=
  const_elim; repeat big_O_polynomial; calvin.


Theorem additions_big_o :
  (fun n => INR n + INR n + INR n + INR n + INR n + INR n) ∈ O(fun n => INR n).
Proof.
  big_O.
Qed.


Theorem additions_big_o_R :
  (fun n => n + n + n + n + n + n) ∈ O(fun n => n).
Proof.
  big_O.
Qed.


Theorem poly_big_o :
  forall c,
    c <> 0 ->
  (fun k => let n := INR k in 3 * (7 * n ^ 7 + n ^ 6) + n ^ 5 + n ^ 4 + n ^ 3 + n ^ 2 + n) ∈ O(fun n => 7 * c * 8 * INR n ^ 20).
Proof.
  intros c H.
  big_O.
Qed.
