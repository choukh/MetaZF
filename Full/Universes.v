(** Coq coding by choukh, May 2022 **)

Require Import Full.Structures.

(*** 格罗滕迪克宇宙 ***)

(* y ∈ x ∈ P → y ∈ P *)
Definition 传递的 {𝓜 : ZF结构} (P : 𝓜 → Prop) :=
  ∀ x y, y ∈ x → P x → P y.

(* y ⊆ x ∈ P → y ∈ P *)
Definition 膨胀的 {𝓜 : ZF结构} (P : 𝓜 → Prop) :=
  ∀ x y, y ⊆ x → P x → P y.

Definition 偶封闭 {𝓜 : ZF结构} (U : 𝓜 → Prop) :=
  ∀ x y, U x → U y → U [x, y].

Definition 并封闭 {𝓜 : ZF结构} (U : 𝓜 → Prop) :=
  ∀ x, U x → U (⋃ x).

Definition 幂封闭 {𝓜 : ZF结构} (U : 𝓜 → Prop) :=
  ∀ x, U x → U (𝒫 x).

Definition 分离封闭 {𝓜 : ZF结构} (U : 𝓜 → Prop) :=
  ∀ P A, 谓词尊重 集等价 P → U A → U (P ∩ A).

Definition 替代封闭 {𝓜 : ZF结构} (U : 𝓜 → Prop) :=
  ∀ F A, 函数尊重 集等价 F → U A → F @ A ⊑ U → U (F @ A).
