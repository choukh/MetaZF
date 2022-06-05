(** Coq coding by choukh, May 2022 **)

Require Import Basic.

(*** 无穷公理 → 模型不可数 ***)
Section Uncountability.
Context {𝓜 : ZF}.

Hypothesis ord : nat → 𝓜.
Hypothesis ord单射 : ∀ m n, ord m = ord n → m = n.
Definition 有限序数 x := ∃ n, x = ord n.

Hypothesis ω : 𝓜.
Hypothesis 无穷 : 集化 有限序数 ω.
Hypothesis f : nat → 𝓜.
Hypothesis f满射 : ∀ x, ∃ n, f n = x.

Theorem 模型不可数 : False.
Proof.
  (* A = {n ∈ ω | n ∉ f n} *)
  set (ω ∩ₚ (λ x, ∃ n, x = ord n ∧ ord n ∉ f n)) as A.
  pose proof (f满射 A) as [m fm].
  排中 (ord m ∈ A) as [mA|false].
  - apply 分离 in mA as H. destruct H as [_ [m' [eq false]]].
    apply false. apply ord单射 in eq. congruence.
  - apply false. apply 分离. split. apply 无穷. now exists m.
    exists m. split; congruence.
Qed.

End Uncountability.
