Require Import Coq.Reals.Reals.
Require Import Coq.Reals.RIneq.
Require Import Coquelicot.Coquelicot.
Require Import classes_sigma.
Require Import Psatz.
Require Import Omega.
Require Import classes_sigma.
Require Import tactics.

Local Open Scope R_scope.
Local Open Scope nat_scope.


Lemma BigTheta_BigO :
  forall (f g : nat -> R),
    f ∈ Θ(g) -> f ∈ O(g).
Proof.
  unfold BigTheta. unfold BigO.
  intros f g [c1 [c2 [n0 HTheta]]].
  exists c2. exists n0.
  intros n Hn_n0.
  pose proof HTheta n Hn_n0.
  split; lra. 
Qed.


Lemma BigTheta_BigOmega :
  forall (f g : nat -> R),
    f ∈ Θ(g) -> f ∈ Ω(g).
Proof.
  unfold BigTheta. unfold BigOmega.
  intros f g [c1 [c2 [n0 HTheta]]].
  exists c1. exists n0.
  intros n Hn_n0.
  destruct c1 as [c1 Hc1]. simpl in *.
  pose proof HTheta n Hn_n0 as [H0g [Hc1g Hc2g]].
  split.
  - apply Rmult_le_reg_l with (r:=c1); lra.
  - lra.
Qed.


Theorem BigTheta_is_BigO_and_BigOmega :
  forall (f g : nat -> R),
    f ∈ O(g) /\ f ∈ Ω(g) <-> f ∈ Θ(g).
Proof.
  intros f g.
  split. {
    intros [[sc2 [n2 HO]] [sc1 [n1 HOmega]]].
    simpl in *.

    unfold BigTheta.
    
    exists sc1. exists sc2. exists (Nat.max n1 n2).

    intros n Hmax.
    apply Nat.max_lub_lt_iff in Hmax. destruct Hmax as [Hn1 Hn2].
    destruct sc1 as [c1 Hc1]. destruct sc2 as [c2 Hc2]. simpl in *.

    pose proof HOmega n Hn1 as [H0g Hf_c1_g].
    pose proof HO n Hn2 as [H0f Hf_c2_g].

    split.
    - apply Rmult_le_pos; lra.
    - split; lra.
  } {
    auto using BigTheta_BigO, BigTheta_BigOmega.
  }
Qed.


Theorem LittleO_BigO :
  forall (f g : nat -> R),
    f ∈ o(g) -> f ∈ O(g).
Proof.
  unfold LittleO. unfold BigO.
  intros f g Ho.

  Lemma gt0 : (1 > 0)%R. Proof. lra. Qed.
  pose proof (exist _ 1%R gt0) as sc.
  
  pose proof Ho sc as Ho. destruct Ho as [n0 Ho].
  exists sc. exists n0.
  
  split.
  - apply Ho. auto.
  - apply Rlt_le. apply Ho. auto.
Qed.


Theorem Limit_LittleO :
  forall (f g : nat -> R),
    is_lim_seq (fun n => (f n / g n)%R) 0%R -> f ∈ o(g).
Proof.
  unfold_limits. intros f g H.
  unfold_complexity. intros [c Hc]. simpl in *.

  pose proof H (fun fg => (fg < c)%R) as H. simpl in H.

  destruct H. exists (mkposreal c Hc).
  intros y H. simpl in H. admit.
  
  exists x. intros n H0.
  unfold gt in H0. apply Nat.lt_le_incl in H0.
  pose proof H n H0 as H.
Abort.