Require Import Coq.Reals.Reals.
Require Import Psatz.
Require Import Omega.

Local Open Scope R_scope.
Local Open Scope nat_scope.


Definition BigO (f : nat -> R) (g : nat -> R) :=
  exists (sc : {c : R | (c > 0) % R}) (n0 : nat), forall (n : nat),
      let c := proj1_sig sc in
      n > n0 ->
      (0 <= f n /\ f n <= c * g n) % R.


Definition LittleO (f : nat -> R) (g : nat -> R) :=
  forall (sc : {c : R | (c > 0) % R}), exists (n0 : nat), forall (n : nat),
      let c := proj1_sig sc in
      n > n0 ->
      (0 <= f n /\ f n < c * g n) % R.


Definition BigOmega (f : nat -> R) (g : nat -> R) :=
  exists (sc : {c : R | (c > 0) % R}) (n0 : nat), forall (n : nat),
      let c := proj1_sig sc in
      n > n0 ->
      (0 <= g n /\ f n >= c * g n) % R.


Definition LittleOmega (f : nat -> R) (g : nat -> R) :=
  forall (sc : {c : R | (c > 0) % R}), exists (n0 : nat), forall (n : nat),
      let c := proj1_sig sc in
      n > n0 ->
      (0 <= f n /\ f n > c * g n) % R.


Definition BigTheta (f : nat -> R) (g : nat -> R) :=
  exists (sc1 sc2 : {c : R | (c > 0) % R}), exists (n0 : nat), forall (n : nat),
      let c1 := proj1_sig sc1 in
      let c2 := proj1_sig sc2 in
      n > n0 ->
      (0 <= c1 * g n /\ c1 * g n <= f n <= c2 * g n) % R.



Notation "f ∈ O( g )" := (BigO f g) (at level 80).
Notation "f ∈ Ω( g )" := (BigOmega f g) (at level 80).
Notation "f ∈ o( g )" := (LittleO f g) (at level 80).
Notation "f ∈ ω( g )" := (LittleOmega f g) (at level 80).
Notation "f ∈ Θ( g )" := (BigTheta f g) (at level 80).


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
    BigO f g /\ BigOmega f g <-> BigTheta f g.
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
