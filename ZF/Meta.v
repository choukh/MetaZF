(** Coq coding by choukh, May 2022 **)

Require Export Utf8_core Classical ProofIrrelevance.
Global Set Implicit Arguments. 
Global Unset Strict Implicit.
Global Unset Printing Implicit Defensive.

(** 经典逻辑 **)

Tactic Notation "排中" constr(P) :=
  destruct (classic P).
Tactic Notation "排中" constr(P) "as" simple_intropattern(L) :=
  destruct (classic P) as L.

Ltac 反证 := match goal with
  |- ?G => destruct (classic G) as [?正设|?反设]; [assumption|exfalso]
end.

(** 关系的性质 **)

Definition 函数性 {X Y} (R : X → Y → Prop) :=
  ∀ x y y', R x y → R x y' → y = y'.

Definition 单射性 {X Y} (R : X → Y → Prop) :=
  ∀ x x' y, R x y → R x' y → x = x'.

Definition 左完全 {X Y} (R : X → Y → Prop) :=
  ∀ x, ∃ y, R x y.

Definition 右完全 {X Y} (R : X → Y → Prop) :=
  ∀ y, ∃ x, R x y.
