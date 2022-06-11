(** Coq coding by choukh, May 2022 **)

Require Export Utf8_core.
Global Set Implicit Arguments.
Global Unset Strict Implicit.
Global Unset Printing Implicit Defensive.

(** 关系的性质 **)

Definition 函数性 {X Y} (R : X → Y → Prop) :=
  ∀ x y y', R x y → R x y' → y = y'.

Definition 单射性 {X Y} (R : X → Y → Prop) :=
  ∀ x x' y, R x y → R x' y → x = x'.

Definition 左完全 {X Y} (R : X → Y → Prop) :=
  ∀ x, ∃ y, R x y.

Definition 右完全 {X Y} (R : X → Y → Prop) :=
  ∀ y, ∃ x, R x y.
