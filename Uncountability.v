(** Coq coding by choukh, May 2022 **)

Require Import Basic.

(*** 模型的不可数性 ***)
Section Uncountability.

Context {𝓜} {满足ZF : ZF 𝓜}.

Hypothesis ord : nat → 𝓜.
Hypothesis ord_单射 : ∀ m n, ord m = ord n → m = n.

Definition 有限序数 x := ∃ n, x = ord n.

Hypothesis ω : 𝓜.
Hypothesis 无穷 : 集化 有限序数 ω.

Definition 可数模型 𝓜 := ∃ f : nat → 𝓜, ∀ x, ∃ n, f n = x.

Theorem 𝓜不可数 : ¬ 可数模型 𝓜.
Proof.
  intros [f f满射].
  (* A = {n ∈ ω | n ∉ f n} *)
  set (ω ∩ (λ x, ∃ n, x = ord n ∧ ord n ∉ f n)) as A.
  pose proof (f满射 A) as [m fm].
  排中 (ord m ∈ A) as [mA|false].
  - apply 分离 in mA as H. destruct H as [_ [m' [eq false]]].
    apply false. apply ord_单射 in eq. congruence.
  - apply false. apply 分离. split. apply 无穷. now exists m.
    exists m. split; congruence.
Qed.

End Uncountability.
