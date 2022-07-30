(** Coq coding by choukh, July 2022 **)

From ZF Require Import Basic Hierarchy HereditarilyFinite.

(** 无穷公理的定义 **)

Fixpoint 幂迭代 {𝓜 : ZF} n :=
  match n with
  | O => ∅
  | S m => 𝒫 (幂迭代 m)
  end.

(* V_<ω 类 *)
Definition 有限层 {𝓜 : ZF} x := ∃ n, x = 幂迭代 n.
(* 无穷公理变体: V_<ω 是集合 *)
Definition 无穷 (𝓜 : ZF) := ∃ x, 集化 有限层 x.

(** 假设一个无穷公理成立的模型 **)
Section Infinity.
Context {𝓜 : ZF}.
Hypothesis Inf : 无穷 𝓜.

Definition Vltω := δ (λ x, 集化 有限层 x).
Definition Vω := ⋃ Vltω.

Lemma 集化有限层 : 集化 有限层 Vltω.
Proof. destruct Inf as [x H]. apply (δ规范 H), 集化唯一. Qed.

Lemma ω层成员属某n层 x : x ∈ Vω → ∃ n, x ∈ 幂迭代 n.
Proof.
  intros [y [xy yV]] % 并集.
  apply 集化有限层 in yV as [n ->]. now exists n.
Qed.

Lemma n层 n : 幂迭代 n ∈ₚ 层.
Proof. induction n. apply 空集层. now constructor. Qed.

Section Omega.

Definition 归纳集 A := ∅ ∈ A ∧ ∀ a ∈ A, a⁺ ∈ A.
Definition 自然数 n := ∀ A, 归纳集 A → n ∈ A.
Definition ω := Vω ∩ₚ 自然数.

Lemma ω层是归纳集 : 归纳集 Vω.
Proof.
  split.
  - apply 并集. exists (幂迭代 1). split.
    + now apply 幂集.
    + apply 集化有限层. now exists 1.
  - intros. apply ω层成员属某n层 in H as [n an].
    apply 并集. exists (幂迭代 (S n)). split.
    + simpl. apply 幂集. intros x xa. apply 后继 in xa as [].
      * congruence.
      * apply 层传递 with a; auto. apply n层.
    + apply 集化有限层. now exists (S n).
Qed.

Fact ω里有且仅有自然数 : ∀ n, n ∈ ω ↔ 自然数 n.
Proof.
  split; intros.
  - now apply 分离 in H.
  - apply 分离. split; auto. apply H. apply ω层是归纳集.
Qed.

End Omega.

Lemma n层属ω层 n : 幂迭代 n ∈ Vω.
Proof.
  apply 并集. exists (幂迭代 (S n)). split.
  - now apply 幂集.
  - apply 集化有限层. now exists (S n).
Qed.

Lemma 空集属ω层 : ∅ ∈ Vω.
Proof.
  replace ∅ with (幂迭代 0) by reflexivity.
  apply n层属ω层.
Qed.

Lemma ω层 : Vω ∈ₚ 层.
Proof.
  constructor. intros y Y.
  apply 集化有限层 in Y as [n ->]. apply n层.
Qed.

Lemma ω层之并 : Vω ⊆ ⋃ Vω.
Proof.
  intros x X. apply ω层成员属某n层 in X as [n X].
  apply 并集. exists (幂迭代 n). split; trivial. apply n层属ω层.
Qed.

Lemma ω层是极限层 : Vω ∈ₚ 极限层.
Proof. split. apply ω层. apply ω层之并. Qed.

End Infinity.
