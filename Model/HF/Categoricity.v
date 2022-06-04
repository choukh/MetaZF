(** Coq coding by choukh, June 2022 **)

Require Import HF Extensionality.

Inductive R (𝓜 𝓝 : HF) : 𝓜 → 𝓝 → Prop :=
  | R空 : R ∅ ∅
  | R并 x y a b : R x a → R y b → R (x ⨮ y) (a ⨮ b).

Section R.
Context {𝓜 𝓝 : HF}.
Implicit Types x y : 𝓜.
Implicit Types a b : 𝓝.

Fact R对称 x a : R x a → R a x.
Proof. intros H. induction H; auto using R. Qed.

End R.
