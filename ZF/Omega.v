(** Coq coding by choukh, July 2022 **)

Require Import Coq.Logic.ClassicalDescription.
From ZF Require Import Basic Infinity.

Section Omega.
Context {𝓜 : ZF}.
Implicit Type P : 𝓜 → Prop.

Hypothesis inf : Inf.
Definition I := proj1_sig inf.
Definition I是归纳集 := proj2_sig inf.

Definition 自然数 n := ∀ A, 归纳集 A → n ∈ A.
Definition ω := I ∩ₚ 自然数.

Fact ω是最小的归纳集 A : 归纳集 A → ω ⊆ A.
Proof. intros H x Hx. apply 分离 in Hx. firstorder. Qed.

Fact ω里有且仅有自然数 n : n ∈ ω ↔ 自然数 n.
Proof.
  split; intros.
  - now apply 分离 in H.
  - apply 分离. split; auto. apply H. apply I是归纳集.
Qed.

(* 皮亚诺公理1 *)
Lemma 零是自然数 : ∅ ∈ ω.
Proof. apply 分离. split. apply I是归纳集. intros A [H _]. auto. Qed.

Fact ω不为零 : ω ≠ ∅.
Proof. intros H. eapply 空集. rewrite <- H. apply 零是自然数. Qed.

(* 皮亚诺公理2 *)
Lemma ω是归纳集 : 归纳集 ω.
Proof.
  split. apply 零是自然数.
  intros n Hn. apply 分离 in Hn. apply 分离.
  split. now apply I是归纳集. firstorder.
Qed.

Lemma ω归纳 : ∀ n ∈ ω, n⁺ ∈ ω.
Proof. apply ω是归纳集. Qed.

(* 皮亚诺公理3 *)
Fact 零不是任何自然数的后继 : ¬ ∃ n ∈ ω, n⁺ = ∅.
Proof. intros [n [Hn H]]. eapply 后继非空; eauto. Qed.

(* 皮亚诺公理5 *)
Lemma 归纳原理 N : N ⊆ ω → 归纳集 N → N = ω.
Proof.
  intros N子集 N归纳. apply 外延; intros n Hn.
  - apply N子集. apply Hn.
  - apply 分离 in Hn. apply Hn. apply N归纳.
Qed.

Lemma 归纳法 P : P ∅ → (∀ n ∈ ω, P n → P n⁺) → ∀ n ∈ ω, P n.
Proof.
  intros 起始 归纳 n Hn.
  assert (ω ∩ₚ P = ω). {
    apply 归纳原理. apply 分离为子集. split.
    - apply 分离; auto using 零是自然数, ω归纳.
    - intros m Hm. apply 分离 in Hm as [Hm Pm].
      apply 分离; auto using ω归纳.
  }
  rewrite <- H in Hn. apply 分离 in Hn. apply Hn.
Qed.

Ltac 归纳 n Hn :=
  hnf; match goal with
    | |- ∀ n ∈ ω, _ => intros n Hn; pattern n
    | Hn: n ∈ ω |- _ => pattern n
  end;
  match goal with |- ?P n => let IH := fresh "归纳假设" in
    generalize dependent n; apply (@归纳法 P); [|intros n Hn IH]
  end.

Tactic Notation "归纳" simple_intropattern(n) simple_intropattern(Hn) := 归纳 n Hn.
Tactic Notation "归纳" simple_intropattern(n) := 归纳 n ?Hn.
Tactic Notation "归纳" := let n := fresh "n" in let Hn := fresh "Hn" in 归纳 n Hn.

Fact ω是传递集 : ω ∈ₚ 传递.
Proof.
  apply 传递_子集表述. 归纳. zf.
  intros x Hx. apply 后继 in Hx as [->|]; auto.
Qed.

Lemma 自然数是传递集 : ω ⊆ₚ 传递.
Proof.
  归纳; intros p q Hp Hq. zf.
  apply 后继 in Hq as [->|]; apply 后继. auto.
  right. eapply 归纳假设; eauto.
Qed.

(* 皮亚诺公理4 *)
Lemma 后继是单射 : ∀ n m ∈ ω, n⁺ = m⁺ → n = m.
Proof.
  intros n Hn m Hm eq.
  apply 自然数是传递集 in Hn, Hm.
  rewrite 传递_后继表述 in Hn, Hm. congruence.
Qed.

Definition 嵌入 := 迭代 继 ∅.

Lemma 嵌入到ω n : 嵌入 n ∈ ω.
Proof. induction n; simpl. apply 零是自然数. apply ω归纳. apply IHn. Qed.
Hint Immediate 嵌入到ω : core.

Lemma 嵌入单射 n m : 嵌入 n = 嵌入 m → n = m.
Proof.
  revert m. induction n; destruct m; simpl; intros H; cbn in H.
  - (* 0, 0 *) reflexivity.
  - (* 0, S m *) exfalso. eapply 后继非空; eauto.
  - (* S n, 0 *) exfalso. eapply 后继非空; eauto.
  - (* S n, S m *) apply 后继是单射 in H; auto.
Qed.

Lemma 投影存在 : ∀ n ∈ ω, ∃ m : nat, 嵌入 m = n.
Proof.
  归纳.
  - exists 0. reflexivity.
  - destruct 归纳假设 as [k H]. subst. exists (S k). reflexivity.
Qed.

Lemma 投影唯一 : ∀ n ∈ ω, uniqueness (λ m, 嵌入 m = n).
Proof. intros n Hn p q Hp Hq. subst. apply 嵌入单射. auto. Qed.

Definition 投影 := λ n, iota 0 (λ m, 嵌入 m = n).

Lemma 先投影再嵌入 : ∀ n ∈ ω, 嵌入 (投影 n) = n.
Proof.
  intros n Hn. unfold 投影. apply iota_spec.
  rewrite <- unique_existence. split.
  apply 投影存在; auto. apply 投影唯一; auto.
Qed.

Lemma 先嵌入再投影 n : 投影 (嵌入 n) = n.
Proof. apply 嵌入单射. rewrite 先投影再嵌入; auto. Qed.

Fact 投影是单射 : ∀ n m ∈ ω, 投影 n = 投影 m → n = m.
Proof.
  intros n Hn m Hm H.
  assert (嵌入 (投影 n) = 嵌入 (投影 m)). auto.
  do 2 rewrite 先投影再嵌入 in H0; auto.
Qed.

Fact 先嵌入再后继再投影 : ∀ n : nat, S n = 投影 (嵌入 n)⁺.
Proof. intros. rewrite <- (先嵌入再投影 (S n)). reflexivity. Qed.

Fact 先投影再后继再嵌入 : ∀n ∈ ω, n⁺ = 嵌入 (S (投影 n)).
Proof.
  intros n Hn. rewrite 先嵌入再后继再投影.
  do 2 rewrite 先投影再嵌入; auto. now apply ω归纳.
Qed.

Fact Inf_to_Infʷ : Infʷ.
Proof.
  apply Build_Infʷ with 嵌入 ω. apply 嵌入单射.
  intros n. split.
  - intros Hn. exists (投影 n). now rewrite 先投影再嵌入.
  - intros [m ->]; auto.
Qed.

End Omega.

Corollary Infⱽ_to_Infʷ {𝓜 : ZF} : Infⱽ → Infʷ.
Proof. intros. apply Inf_to_Infʷ. now apply Infⱽ_to_Inf. Qed.
