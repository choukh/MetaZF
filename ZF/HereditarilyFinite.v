(** Coq coding by choukh, July 2022 **)

From ZF Require Import Basic AdjunctionFacts Hierarchy.

(** 遗传有限集 **)
Section HereditarilyFinite.
Context {𝓜 : ZF}.

Inductive 有限集 : 𝓜 → Prop :=
  | 有限集_空 : 有限集 ∅
  | 有限集_并 x y : 有限集 y → 有限集 (x ⨮ y).

Inductive 遗传有限集 : 𝓜 → Prop :=
  | 遗传有限集引入 x : 有限集 x → (∀ y ∈ x, 遗传有限集 y) → 遗传有限集 x.

(* 遗传有限集之类 *)
Notation HF := 遗传有限集.

Lemma HF集是有限集 x : HF x → 有限集 x.
Proof. now intros []. Qed.

Lemma HF是成员封闭类 : 传递类 HF.
Proof. destruct 2. now apply H1. Qed.

Lemma HF是空集封闭类 : ∅ ∈ₚ HF.
Proof. constructor. constructor. constructor; zf. Qed.

Lemma 二元并对有限集封闭 a b : 有限集 a → 有限集 b → 有限集 (a ∪ b).
Proof.
  intros H. revert b. induction H as [|x z H IH].
  - intros b Fb. now rewrite 左并空.
  - intros b Fb. rewrite 并入二元并结合律.
    constructor. now apply IH.
Qed.

Lemma HF是并集封闭类 a : HF a → HF ⋃ a.
Proof.
  intros [x Fx HFx]. constructor.
  - induction Fx as [|x y Fin].
    + rewrite 并空. constructor.
    + rewrite 并入之并. apply 二元并对有限集封闭.
      * apply HF集是有限集, HFx, 并入. auto.
      * apply IHFin. intros z zy.
        apply HFx, 并入. auto.
  - intros y [z [yz zx]]%并集. apply HFx in zx.
    destruct zx as [z]. now apply H0.
Qed.

Lemma 子集对有限集封闭 a b : b ⊆ a → 有限集 a → 有限集 b.
Proof.
  revert b. induction 2 as [|x z Fx IH].
  - apply 空集的子集 in H as ->. constructor.
Admitted.

Lemma 幂集对有限集封闭 a : 有限集 a → 有限集 (𝒫 a).
Proof.
  induction 1 as [|x y H IH].
  - rewrite 幂空. repeat constructor.
  - rewrite 并入之幂. apply 二元并对有限集封闭; trivial.
    admit.
Admitted.

Fact HF是封闭类 : 封闭类 HF.
Proof.
  split.
  - apply HF是成员封闭类.
  - apply HF是空集封闭类.
  - apply HF是并集封闭类.
  - admit.
Admitted.

End HereditarilyFinite.
