(** Coq coding by choukh, May 2022 **)

Require Import Lite.Basic Lite.InnerModel Lite.Hierarchy.

Section IsoDef.

Context {𝓜 𝓝 : ZF}.
Implicit Type x₁ y₁ : 𝓜.
Implicit Type x₂ y₂ : 𝓝.
Implicit Type R : 𝓜 → 𝓝 → Prop.

Definition 左完全 R x₁ x₂ := ∀ y₁ ∈ x₁, ∃ y₂ ∈ x₂, R y₁ y₂.

Definition 右完全 R x₁ x₂ := ∀ y₂ ∈ x₂, ∃ y₁ ∈ x₁, R y₁ y₂.

Inductive 同构 x₁ x₂ : Prop := 
  | iso_intro : 左完全 同构 x₁ x₂ → 右完全 同构 x₁ x₂ → 同构 x₁ x₂.

End IsoDef.

Notation "x₁ ≅ x₂" := (同构 x₁ x₂) (at level 80) : zf_scope.
Notation "x₁ ▷ x₂" := (左完全 同构 x₁ x₂) (at level 80) : zf_scope.
Notation "x₁ ◁ x₂" := (右完全 同构 x₁ x₂) (at level 80) : zf_scope.

Lemma 同构_对称 {𝓜 𝓝 : ZF} (x₁ : 𝓜) (x₂ : 𝓝) : x₁ ≅ x₂ → x₂ ≅ x₁.
Proof.
  pose proof (正则 x₁) as WF. revert x₂.
  induction WF as [x₁ _ IH].
  intros x₂ [l r]. split.
  - intros y₂ y₂x₂. destruct (r y₂ y₂x₂) as [y₁ [y₁x₁ y₁y₂]].
    exists y₁. split; auto.
  - intros y₁ y₁x₁. destruct (l y₁ y₁x₁) as [y₂ [y₂x₂ y₁y₂]].
    exists y₂. split; auto.
Qed.

Lemma 完全_对称 {𝓜 𝓝 : ZF} (x₁ : 𝓜) (x₂ : 𝓝) : x₁ ▷ x₂ ↔ x₂ ◁ x₁.
Proof.
  split.
  - intros l y₁ y₁x₁. destruct (l y₁ y₁x₁) as [y₂ [y₂x₂ y₁y₂]].
    exists y₂. split; auto. now apply 同构_对称.
  - intros r y₁ y₁x₁. destruct (r y₁ y₁x₁) as [y₂ [y₂x₂ y₁y₂]].
    exists y₂. split; auto. now apply 同构_对称.
Qed.
