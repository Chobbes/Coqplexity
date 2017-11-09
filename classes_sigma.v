Require Import Coq.Reals.Reals.
Require Import ord.

Local Open Scope R_scope.
Local Open Scope Ord_scope.


Definition BigO {A} `{Ord A} (f : A -> R) (g : A -> R) :=
  exists (sc : {c : R | (c > 0) % R}) (n0 : A), forall (n : A),
      let c := proj1_sig sc in
      n > n0 ->
      0%R <= f n /\ f n <= c * g n.


Definition LittleO {A} `{Ord A} (f : A -> R) (g : A -> R) :=
  forall (sc : {c : R | (c > 0) % R}), exists (n0 : A), forall (n : A),
      let c := proj1_sig sc in
      n > n0 ->
      0%R <= f n /\ f n < c * g n.


Definition BigOmega {A} `{Ord A} (f : A -> R) (g : A -> R) :=
  exists (sc : {c : R | (c > 0) % R}) (n0 : A), forall (n : A),
      let c := proj1_sig sc in
      n > n0 ->
      0%R <= g n /\ f n >= c * g n.


Definition LittleOmega {A} `{Ord A} (f : A -> R) (g : A -> R) :=
  forall (sc : {c : R | (c > 0) % R}), exists (n0 : A), forall (n : A),
      let c := proj1_sig sc in
      n > n0 ->
      0%R <= f n /\ f n > c * g n.


Definition BigTheta {A} `{Ord A} (f : A -> R) (g : A -> R) :=
  exists (sc1 sc2 : {c : R | (c > 0) % R}), exists (n0 : A), forall (n : A),
      let c1 := proj1_sig sc1 in
      let c2 := proj1_sig sc2 in
      n > n0 ->
      0%R <= c1 * g n /\ c1 * g n <= f n <= c2 * g n.


Notation "f ∈ O( g )" := (BigO f g) (at level 80).
Notation "f ∈ Ω( g )" := (BigOmega f g) (at level 80).
Notation "f ∈ o( g )" := (LittleO f g) (at level 80).
Notation "f ∈ ω( g )" := (LittleOmega f g) (at level 80).
Notation "f ∈ Θ( g )" := (BigTheta f g) (at level 80).
