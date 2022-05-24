(** Coq coding by choukh, May 2022 **)

Require Import Full.Meta.

(** 与关系有关的定义 **)

Definition 谓词尊重 {T} (R : T → T → Prop) (P : T → Prop) :=
  ∀ x y, R x y → P x → P y.

Definition 函数尊重 {T} (R : T → T → Prop) (f : T → T) :=
  ∀ x y, R x y → R (f x) (f y).
