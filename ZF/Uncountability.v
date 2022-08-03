(** Coq coding by choukh, May 2022 **)

From ZF Require Import Basic Universe Embedding Categoricity
  Infinity Omega.

(* 模型可数 *)
Definition Cnt {𝓜 : ZF} := ∃ f : nat → 𝓜, ∀ x, ∃ n, f n = x.

Lemma 无穷模型不可数 {𝓜 : ZF} : Infⱽ → ¬ Cnt.
Proof.
  intros inf [f f满射].
  apply Infⱽ_to_Infʷ in inf as [].
  (* A = {n ∈ ω | n ∉ f n} *)
  set (ω ∩ₚ (λ x, ∃ n, x = 嵌入 n ∧ 嵌入 n ∉ f n)) as A.
  pose proof (f满射 A) as [m fm].
  排中 (嵌入 m ∈ A) as [mA|false].
  - apply 分离 in mA as H. destruct H as [_ [m' [eq false]]].
    apply false. apply 嵌入单射 in eq. congruence.
  - apply false. apply 分离. split. apply 无穷. now exists m.
    exists m. split; congruence.
Qed.

Lemma 反无穷模型同构 {𝓜 𝓝 : ZF} : ¬ @Infⱽ 𝓜 → ¬ @Infⱽ 𝓝 → 𝓜 ≅ 𝓝.
Proof.
  intros H1 H2. apply 反无穷模型等价于极小模型, ZFₙO in H1, H2.
  now apply 极小模型同构.
Qed.

Section 假设存在反无穷可数模型.
Context {𝓜 : ZF}.
Hypothesis 𝓜反无穷 : ¬ @Infⱽ 𝓜.
Hypothesis 𝓜可数 : @Cnt 𝓜.

Lemma 反无穷模型可数 {𝓝 : ZF} : ¬ Infⱽ → Cnt.
Proof.
  set (i := @i 𝓜 𝓝).
  set (j := @j 𝓜 𝓝).
  destruct 𝓜可数 as [f f满射]. exists (λ n, i (f n)).
  intros a. specialize (f满射 (j a)) as [n fn].
  exists n. rewrite fn. apply ij. now apply 反无穷模型同构.
Qed.

Theorem 无穷模型等价于不可数模型 {𝓝 : ZF} : Infⱽ ↔ ¬ Cnt.
Proof.
  split.
  - apply 无穷模型不可数.
  - intros cnt. 反证. apply 反无穷模型可数 in 反设. auto.
Qed.

End 假设存在反无穷可数模型.
