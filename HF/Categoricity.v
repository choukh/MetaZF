(** Coq coding by choukh, June 2022 **)

Require Import HF Extensionality.

(** 不同模型的集合间的相似关系 **)
Inductive 相似 (𝓜 𝓝 : HF) : 𝓜 → 𝓝 → Prop :=
  | 空相似 : 相似 ∅ ∅
  | 并相似 x y a b : 相似 x a → 相似 y b → 相似 (x ⨮ y) (a ⨮ b).

Notation "x ≈ y" := (相似 x y) (at level 80) : hf_scope.

Section Bisimilarity.
Context {𝓜 𝓝 : HF}.
Implicit Types x y z : 𝓜.
Implicit Types a b c : 𝓝.

Lemma 相似对称 x a : x ≈ a → a ≈ x.
Proof. intros H. induction H; auto using 相似. Qed.

Lemma ϵ相似性 x a y: x ≈ a → y ∈ x → ∃ b, b ∈ a ∧ y ≈ b.
Proof.
  intros xa. revert y.
  induction xa as [|x y a b xa _ _ IHx].
  - hf.
  - intros z [->|zy]%属.
    + exists a. hf.
    + destruct (IHx _ zy) as [c [cb zc]]. exists c. hf.
Qed.

End Bisimilarity.

(** 相似关系有函数性 **)
Section Functional.
Context {𝓜 𝓝 : HF}.
Implicit Types x y z : 𝓜.
Implicit Types a b c : 𝓝.

Lemma 相似的完全性 x : Σ a, x ≈ a.
Proof.
  hf_ind x.
  - exists ∅. constructor.
  - intros x y [a xa] [b yb].
    exists (a ⨮ b). now constructor.
Qed.

End Functional.
