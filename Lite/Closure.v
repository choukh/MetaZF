(** Coq coding by choukh, May 2022 **)

Require Import Lite.Basic.

(** 封闭性 **)

Section Closure.

Context {𝓜 : ZF}.
Implicit Type A a b x y z : 𝓜.
Implicit Type P : 𝓜 → Prop.

Definition 空集封闭 x := ∅ ∈ x.
Definition 并集封闭 x := ∀ y ∈ x, ⋃ y ∈ x.
Definition 幂集封闭 x := ∀ y ∈ x, 𝒫 y ∈ x.
Definition 配对封闭 x := ∀ a b ∈ x, [a, b] ∈ x.
Definition 分离封闭 x := ∀ P, ∀ y ∈ x, y ∩ₚ P ∈ x.

Definition 替代封闭 x := ∀ R y, 函数性 R → (∀ a b, R a b → a ∈ y → b ∈ x) → y ∈ x → R @ y ∈ x.
Definition 替代封闭' x := ∀ R y,  函数性 R → R @ y ⊆ x → y ∈ x → R @ y ∈ x.

Fact 替代封闭_等价表述 x : 替代封闭 x ↔ 替代封闭' x.
Proof.
  split; intros C R A FR H1 H2; apply C; auto.
  - intros a b Rab aA. apply H1.
    apply 替代. auto. now exists a.
  - intros z [y [yA Ryz]]%替代; auto. eapply H1; eauto.
Qed.

Class 封闭传递类 P : Prop := {
  传递类 : ∀ x y, x ∈ y → y ∈ₚ P → x ∈ₚ P;
  空集封闭类 : ∅ ∈ₚ P;
  并集封闭类 : ∀ x, x ∈ₚ P → ⋃ x ∈ₚ P;
  幂集封闭类 : ∀ x, x ∈ₚ P → 𝒫 x ∈ₚ P;
  替代封闭类 : ∀ R A, 函数性 R → 
    (∀ x y, R x y → x ∈ A → y ∈ₚ P) → A ∈ₚ P → R @ A ∈ₚ P
}.

End Closure.
