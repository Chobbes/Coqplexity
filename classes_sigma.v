Require Import Coq.Reals.Reals.
Require Import Coquelicot.Coquelicot.
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
