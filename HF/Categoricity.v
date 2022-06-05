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

Lemma 相似完全 x : Σ a, x ≈ a.
Proof.
  hf_ind x.
  - exists ∅. constructor.
  - intros x y [a xa] [b yb].
    exists (a ⨮ b). now constructor.
Qed.

Lemma 存在相似成员 x a y: x ≈ a → y ∈ x → ∃ b, b ∈ a ∧ y ≈ b.
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

Lemma 相似有函数性 x a b : x ≈ a → x ≈ b → a = b.
Proof.
  revert a b. ϵ_ind x.
  intros x IH a b xa xb. 外延 as c ca cb.
  - apply 相似对称 in xa.
    destruct (存在相似成员 xa ca) as [y [yx cy]].
    destruct (存在相似成员 xb yx) as [d [db yd]].
    enough (c = d) by congruence.
    apply IH with y; auto. now apply 相似对称.
  - apply 相似对称 in xb.
    destruct (存在相似成员 xb cb) as [y [yx cy]].
    destruct (存在相似成员 xa yx) as [d [db yd]].
    enough (c = d) by congruence.
    apply IH with y; auto. now apply 相似对称.
Qed.

End Functional.

(** 模型同态 **)
Section Homomorphism.
Context {𝓜 𝓝 : HF}.
Implicit Types x y z : 𝓜.
Implicit Types a b c : 𝓝.

Definition 同态 (f : 𝓜 → 𝓝) := f ∅ = ∅ ∧ ∀ x y, f (x ⨮ y) = f x ⨮ f y.

Fact 同态蕴含相似 f x : 同态 f → x ≈ f x.
Proof.
  intros [f0 fxy]. hf_ind x.
  - rewrite f0. constructor.
  - intros x y xyx yfy. rewrite fxy. now constructor.
Qed.

Fact 同态唯一 f g x : 同态 f → 同态 g → f x = g x.
Proof.
  intros xfx%(同态蕴含相似 x) xgx% (同态蕴含相似 x).
  apply (相似有函数性 xfx xgx).
Qed.

End Homomorphism.

Definition 嵌入 (𝓜 𝓝 : HF) : 𝓜 → 𝓝.
  intros x. destruct (相似完全 x) as [a _]. apply a.
Defined.

(** 模型间嵌入 **)
Section Embedding.
Variable 𝓜 𝓝 : HF.
Implicit Types x y z : 𝓜.
Implicit Types a b c : 𝓝.

Notation f := (@嵌入 𝓜 𝓝).
Notation g := (@嵌入 𝓝 𝓜).

Lemma 嵌入互逆 x : g (f x) = x.
Proof.
  unfold 嵌入.
  destruct (相似完全 x) as [a xa].
  destruct (相似完全 a) as [x' ax'].
  apply 相似对称 in xa. apply (相似有函数性 ax' xa). 
Qed.

Lemma 嵌入同态 : 同态 f.
Proof.
  split.
  - unfold 嵌入. destruct (相似完全 ∅) as [a A]. inversion A; hf.
  - intros x y. unfold 嵌入.
    destruct (相似完全 (x ⨮ y)) as [c xyc].
    destruct (相似完全 x) as [a xa].
    destruct (相似完全 y) as [b yb].
    assert (xyac: 相似 (x ⨮ y) (a ⨮ b)) by now constructor.
    apply (相似有函数性 xyc xyac).
Qed.

End Embedding.

Theorem 范畴性 (𝓜 𝓝 : HF) : Σ (f : 𝓜 → 𝓝) (g : 𝓝 → 𝓜),
  (∀ x, g (f x) = x) ∧ (∀ a, f (g a) = a) ∧ 同态 f ∧ 同态 g.
Proof.
  exists (嵌入 𝓝), (嵌入 𝓜); auto using 嵌入互逆, 嵌入同态.
Qed.
