Require Import Coq.Reals.Reals.


Class Ord A : Type :=
  {
    (* Slightly more verbose than necessary *)
    lt_ord : A -> A -> Prop;

    (* Axioms *)
    le_dec (x : A) (y : A) : {lt_ord x y \/ x = y} + {lt_ord y x};
    lt_trans (x y z : A) : lt_ord x y -> lt_ord y z -> lt_ord x z;
  }.


Delimit Scope Ord_scope with O.
Open Scope Ord_scope.

Infix "<" := lt_ord : Ord_scope.

Definition le_ord {A} `{Ord A} x y : Prop := (x < y \/ x = y)%O.
Infix "<=" := le_ord : Ord_scope.

Definition gt_ord {A} `{Ord A} x y : Prop := (y < x)%O.
Infix ">" := gt_ord : Ord_scope.

Definition ge_ord {A} `{Ord A} x y : Prop := (x > y \/ x = y)%O.
Infix ">=" := ge_ord : Ord_scope.


Notation "x <= y <= z" := (x <= y /\ y <= z) : Ord_scope.
Notation "x <= y < z" := (x <= y /\ y < z) : Ord_scope.
Notation "x < y < z" := (x < y /\ y < z) : Ord_scope.
Notation "x < y <= z" := (x < y /\ y <= z) : Ord_scope.


Theorem nat_le_lt_dec :
  forall x y,
    {(x < y \/ x = y)%nat} + {(y < x)%nat}.
Proof.
  intros x y.
  destruct (le_lt_dec x y); auto using le_lt_or_eq.
Qed.


Local Open Scope nat_scope.
Instance ordNat : Ord nat :=
  {|
    lt_ord x y := x < y;
    le_dec := nat_le_lt_dec;
    lt_trans := Nat.lt_trans;
  |}.


Local Open Scope R_scope.
Instance ordReal : Ord R :=
  {|
    lt_ord x y := x < y;
    le_dec x y := Rle_lt_dec x y;
    lt_trans := Rlt_trans;
  |}.


Local Open Scope Ord_scope.


Definition max {A} `{Ord A} x y : A :=
  match le_dec x y with
  | left _ => y
  | right _ => x
  end.


Theorem max_lub_lt_iff :
  forall {A} `{Ord A} (x y z : A),
    max x y < z <-> (x < z) /\ (y < z).
Proof.
  intros A H x y z.
  split; unfold max; destruct (le_dec x y) as [[Hlt | Heq] | Heq]; try tauto;
  subst; eauto using lt_trans.
Qed.

