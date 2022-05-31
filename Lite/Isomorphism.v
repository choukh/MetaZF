(** Coq coding by choukh, May 2022 **)

Require Import Lite.Basic Lite.InnerModel Lite.Hierarchy.

(** 不同模型的集合间的∈-相似关系 **)
Section Bisimilarity.
Context {𝓜 𝓝 : ZF}.
Implicit Type x y : 𝓜.
Implicit Type a b : 𝓝.
Implicit Type R : 𝓜 → 𝓝 → Prop.

Local Definition ϵ左完全 R x a := ∀ y ∈ x, ∃ b ∈ a, R y b.
Local Definition ϵ右完全 R x a := ∀ b ∈ a, ∃ y ∈ x, R y b.

Inductive 相似 x a : Prop := 
  | bis_intro : ϵ左完全 相似 x a → ϵ右完全 相似 x a → 相似 x a.

End Bisimilarity.

Notation "x ≈ a" := (相似 x a) (at level 80) : zf_scope.
Notation "x ▷ a" := (ϵ左完全 相似 x a) (at level 80) : zf_scope.
Notation "x ◁ a" := (ϵ右完全 相似 x a) (at level 80) : zf_scope.

Definition 同构 (𝓜 𝓝 : ZF) := 左完全 (@相似 𝓜 𝓝) ∧ 右完全 (@相似 𝓜 𝓝).
Notation "𝓜 ≅ 𝓝" := (同构 𝓜 𝓝) (at level 80) : zf_scope.

(** 相似关系的对称性 **)
Section Symmetry.
Context {𝓜 𝓝 : ZF}.
Implicit Type x y : 𝓜.
Implicit Type a b : 𝓝.

Definition 定义域 x := ∃ a, x ≈ a.
Definition 值域 a := ∃ x, x ≈ a.

Lemma 左偏相似 x a : x ≈ a → x ▷ a.
Proof. now intros []. Qed.

Lemma 右偏相似 x a : x ≈ a → x ◁ a.
Proof. now intros []. Qed.

Lemma 相似_对称 x a : x ≈ a → a ≈ x.
Proof.
  pose proof (正则 x) as WF. revert a.
  induction WF as [x _ IH].
  intros a [l r]. split.
  - intros b ba. destruct (r b ba) as [y [yx yb]].
    exists y. split; auto.
  - intros y yx. destruct (l y yx) as [b [ba yb]].
    exists b. split; auto.
Qed.

Lemma 相似_函数性 : 函数性 (@相似 𝓜 𝓝).
Proof.
  intros x. induction (正则 x) as [x _ IH].
  intros a b [xa ax] [xb bx].
  apply 外延; intros c C.
  - destruct (ax c C) as [y [yx yc]].
    destruct (xb y yx) as [d [db yd]].
    rewrite (IH y yx c d); auto.
  - destruct (bx c C) as [y [yx yc]].
    destruct (xa y yx) as [d [db yd]].
    rewrite (IH y yx c d); auto.
Qed.

End Symmetry.

Section Symmetry_More.
Context {𝓜 𝓝 : ZF}.
Implicit Type x y : 𝓜.
Implicit Type a b : 𝓝.

Lemma 相似_单射性 : 单射性 (@相似 𝓜 𝓝).
Proof.
  intros x x' y yx%相似_对称 yx'%相似_对称. eapply 相似_函数性; eauto.
Qed.

Lemma 偏相似_对称 x a : x ▷ a ↔ a ◁ x.
Proof.
  split.
  - intros l y yx. destruct (l y yx) as [b [ba yb]].
    exists b. split; auto. now apply 相似_对称.
  - intros r y yx. destruct (r y yx) as [b [ba yb]].
    exists b. split; auto. now apply 相似_对称.
Qed.

Lemma 相似_完全性_对称 : 左完全 (@相似 𝓜 𝓝) ↔ 右完全 (@相似 𝓝 𝓜).
Proof. split; intros H x; destruct (H x) as [a ax%相似_对称]; eauto. Qed.

End Symmetry_More.

(** 相似关系保持结构 **)
Section StructurePreserving_Partial.
Context {𝓜 𝓝 : ZF}.
Implicit Type x y : 𝓜.
Implicit Type a b : 𝓝.

Lemma 相似_保持ϵ_偏 x y a b : x ≈ a → y ≈ b → y ∈ x → b ∈ a.
Proof.
  intros [xa _] yb yx.
  destruct (xa y yx) as [c [ca yc]].
  now rewrite (相似_函数性 yb yc).
Qed.

Lemma 偏相似_保持空集 : 𝓜.(结构).(空) ▷ 𝓝.(结构).(空).
Proof. intros x H. zf. Qed.

Lemma 偏相似_保持并集 x a : x ▷ a → ⋃ x ▷ ⋃ a.
Proof.
  intros H y [z [yz zx]]%并集.
  destruct (H z zx) as [b [ba [zb _]]].
  destruct (zb y yz) as [c [cb yc]].
  exists c. split; auto. apply 并集. now exists b.
Qed.

Lemma 偏相似_保持幂集 x a : x ▷ a → 𝒫 x ▷ 𝒫 a.
Proof.
  intros xa y yx%幂集.
  set (a ∩ₚ (λ c, ∃ z ∈ y, z ≈ c)) as b.
  exists b. split. apply 幂集, 分离为子集. split.
  - intros z zy. destruct (xa z (yx z zy)) as [c [ca zc]].
    exists c. split; auto. apply 分离. split; eauto.
  - intros c cb. now apply 分离 in cb.
Qed.

Definition 嵌入 (R : 𝓜 → 𝓜 → Prop) : 𝓝 → 𝓝 → Prop :=
  λ a b, ∃ x y, x ≈ a ∧ y ≈ b ∧ R x y.

Lemma 嵌入_函数性 R : 函数性 R → 函数性 (嵌入 R).
Proof.
  intros FR a b c [x [y [xa [yb Rxy]]]] [x' [z [x'a [zc Rxz]]]].
  rewrite (相似_单射性 x'a xa) in Rxz.
  rewrite (FR x y z Rxy Rxz) in yb.
  apply (相似_函数性 yb zc).
Qed.

Lemma 左偏相似_保持替代 R x a : 函数性 R →
  R @ x ⊆ₚ 定义域 → x ▷ a → R @ x ▷ 嵌入 R @ a.
Proof.
  intros FR dom xa y yR. destruct (dom y yR) as [b yb].
  exists b. split; auto. apply 替代. now apply 嵌入_函数性.
  apply 替代 in yR as [z [zx Rzy]]; auto.
  destruct (xa z zx) as [c [ca zc]].
  exists c. split; auto. now exists z, y.
Qed.

Fact 右偏相似_保持替代 R x a : 函数性 R →
  R @ x ⊆ₚ 定义域 → x ◁ a → R @ x ◁ 嵌入 R @ a.
Proof.
  intros FR dom xa b br.
  apply 替代 in br as [c [ca [z [y [zc [yb Rzy]]]]]]. 2: now apply 嵌入_函数性.
  exists y. split; auto. apply 替代; auto. exists z. split; auto.
  destruct (xa c ca) as [z' [z'x z'c]]. now rewrite (相似_单射性 zc z'c).
Qed.

End StructurePreserving_Partial.

Section StructurePreserving.
Context {𝓜 𝓝 : ZF}.
Implicit Type x y : 𝓜.
Implicit Type a b : 𝓝.

Lemma 相似_保持ϵ x y a b : x ≈ a → y ≈ b → (y ∈ x ↔ b ∈ a).
Proof.
  intros xa yb. split; intros H.
  - now apply (相似_保持ϵ_偏 xa yb).
  - now apply (相似_保持ϵ_偏 (相似_对称 xa) (相似_对称 yb)).
Qed.

Lemma 相似_保持空集 : 𝓜.(结构).(空) ≈ 𝓝.(结构).(空).
Proof.
  split.
  - apply 偏相似_保持空集.
  - now apply 偏相似_对称, 偏相似_保持空集.
Qed.

Lemma 相似_保持并集 x a : x ≈ a → ⋃ x ≈ ⋃ a.
Proof.
  intros [xa ax]. split.
  - now apply 偏相似_保持并集.
  - now apply 偏相似_对称, 偏相似_保持并集, 偏相似_对称.
Qed.

Lemma 相似_保持幂集 x a : x ≈ a → 𝒫 x ≈ 𝒫 a.
Proof.
  intros [xa ax]. split.
  - now apply 偏相似_保持幂集.
  - now apply 偏相似_对称, 偏相似_保持幂集, 偏相似_对称.
Qed.

Lemma 相似_保持替代 R x a :函数性 R →
  R @ x ⊆ₚ 定义域 → x ≈ a → R @ x ≈ 嵌入 R @ a.
Proof.
  intros FR dom xa. split.
  - now apply 左偏相似_保持替代, xa.
  - now apply 右偏相似_保持替代, xa.
Qed.

End StructurePreserving.

(** 相似关系的定义域 **)
Section Domain.
Context {𝓜 𝓝 : ZF}.
Implicit Type x y : 𝓜.
Implicit Type a b : 𝓝.

Lemma 在定义域 x a : x ≈ a → x ∈ₚ 定义域.
Proof. intros H. now exists a. Qed.

Lemma 在定义域' x a : x ≈ a → a ∈ₚ @定义域 𝓝 𝓜.
Proof. intros H%相似_对称. now exists x. Qed.

Lemma 定义域_传递类 : 传递类 定义域.
Proof.
  intros x y xD [a xa].
  destruct (左偏相似 xa xD) as [b [_ yb]]. now exists b.
Qed.

Lemma 定义域_膨胀类 : 膨胀类 定义域.
Proof.
  intros x y yp%幂集 [a xa%相似_保持幂集].
  destruct (左偏相似 xa yp) as [b [_ J]]. now exists b.
Qed.

Lemma 定义域_并集封闭 x : x ∈ₚ 定义域 → ⋃ x ∈ₚ 定义域.
Proof. intros [a H%相似_保持并集]. now exists (⋃ a). Qed.

End Domain.
