Require Import Coq.Program.Basics.
Require Import Coq.Reals.Reals.
Require Import Coq.Reals.RIneq.
Require Import Coquelicot.Coquelicot.
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
  pose proof HTheta n Hn_n0 as [H0 [H1 H2]].

  split; ord_lra.
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
  pose proof HTheta n Hn_n0 as [H0g [Hc1g Hc2g]].

  unfold_ord in *.
  simpl in *.

  split.
  - apply Rmult_le_reg_l with (r:=c1); lra.
  - lra.
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

    pose proof HOmega n Hn1 as [H0g Hf_c1_g].
    pose proof HO n Hn2 as [H0f Hf_c2_g].

    unfold_ord in *.
    
    split.
    - apply Rmult_le_pos; lra.
    - split; lra.
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
  
  split.
  - apply Ho. auto.
  - apply Rlt_le. apply Ho. auto.
Qed.


Theorem Limit_LittleO :
  forall (f g : nat -> R),
    (exists n0, forall n, n > n0 -> (f n > 0)%R /\ (g n > 0)%R) -> 
    is_lim_seq (fun n => (f n / g n)%R) 0%R -> f ∈ o(g).
Proof.
  unfold_limits. intros f g Hres H.
  unfold_complexity. intros [c Hc]. simpl in *.

  pose proof H (fun fg => (fg < c)%R) as H. simpl in H.

  destruct H. exists (mkposreal c Hc).
  intros y H. simpl in *. apply Rabs_def2 in H as [Hyc Hcy].

  replace y with (minus y 0)%R.
  apply Hyc. replace 0%R with (zero : R). apply minus_zero_r.
  reflexivity.

  destruct Hres as [n0_res Hres].
  exists (Nat.max x n0_res).

  intros n Hmax. apply Nat.max_lub_lt_iff in Hmax as [Hx Hn0].
  apply Nat.lt_le_incl in Hx.

  pose proof Hres n Hn0 as [Hfn0 Hgn0].
  pose proof H n Hx as H.

  unfold_ord.

  split.
  - lra.
  - apply Rlt_div_l; assumption.
Qed.


Theorem LittleO_Limit :
  forall (f g : nat -> R),
    f ∈ o(g) ->
    is_lim_seq (fun n => (f n / g n)%R) 0%R.
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
  pose proof Ho n Hn0n as [H0f Hfg].

  apply Rabs_def1.
  apply Rlt_div_l.
  - pose proof Rle_lt_trans 0 (f n) (eps * g n)%R H0f Hfg.
    apply (Rmult_lt_reg_r eps); lra.
  - lra.
  - apply Rlt_div_r; try ord_lra. pose proof Rle_lt_trans 0 (f n) (eps * g n)%R H0f Hfg.
    apply (Rmult_lt_reg_r eps); lra.
Qed.


(* Converse is not necessarily true, since the limit need not exist. *)
Theorem Limit_BigTheta :
  forall (f g : nat -> R),
    (exists n0, forall n, n > n0 -> (f n > 0)%R /\ (g n > 0)%R) ->
    (exists (c : R), (c > 0)%R /\ is_lim_seq (fun n => (f n / g n)%R) c) ->
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

    pose proof Hres n0 Hn0 as Hres. destruct Hres as [Hf0 Hg0].

    split.
    + apply Rlt_le. apply Rmult_lt_0_compat; lra.
    + apply Nat.lt_le_incl in HN. pose proof H n0 HN as H.
      destruct H as [Hc2f Hf3c2].
      split; apply Rlt_le.
      * apply Rlt_div_r; lra.
      * apply Rlt_div_l; lra.
Qed.
