(** Coq coding by choukh, July 2022 **)

Require Import ZF.Basic.

(** 无穷公理的定义 **)

Fixpoint 幂迭代 {𝓜 : ZF} n :=
  match n with
  | O => ∅
  | S m => 𝒫 (幂迭代 m)
  end.

(* V_<ω *)
Definition 有限层 {𝓜 : ZF} x := ∃ n, x = 幂迭代 n.
(* 无穷公理变体: V_<ω 是集合 *)
Definition 无穷 (𝓜 : ZF) := ∃ x, 集化 有限层 x.

(** 假设一个无穷公理成立的模型 **)
Section Infinity.
Context {𝓜 : ZF}.
Hypothesis Inf : 无穷 𝓜.

Definition V_ltω := δ (λ x, 集化 有限层 x).
Definition V_ω := ⋃ V_ltω.

Lemma 集化有限层 : 集化 有限层 V_ltω.
Proof. destruct Inf as [x H]. apply (δ规范 H), 集化唯一. Qed.

Lemma n层属ω层 n : 幂迭代 n ∈ V_ω.
Proof.
  apply 并集. exists (幂迭代 (S n)). split.
  - now apply 幂集.
  - apply 集化有限层. now exists (S n).
Qed.

End Infinity.
