(** Coq coding by choukh, May 2022 **)

Require Import Lite.Basic Lite.InnerModel Lite.Hierarchy Lite.Universe.

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

(** 相似关系的对称性 **)
Section Symmetry.
Context {𝓜 𝓝 : ZF}.
Implicit Type x y : 𝓜.
Implicit Type a b : 𝓝.

Lemma 左偏相似 x a : x ≈ a → x ▷ a.
Proof. now intros []. Qed.

Lemma 右偏相似 x a : x ≈ a → x ◁ a.
Proof. now intros []. Qed.

Lemma 相似对称 x a : x ≈ a → a ≈ x.
Proof.
  pose proof (正则 x) as WF. revert a.
  induction WF as [x _ IH].
  intros a [l r]. split.
  - intros b ba. destruct (r b ba) as [y [yx yb]].
    exists y. split; auto.
  - intros y yx. destruct (l y yx) as [b [ba yb]].
    exists b. split; auto.
Qed.

Lemma 相似有函数性 : 函数性 (@相似 𝓜 𝓝).
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

Lemma 相似单射性 : 单射性 (@相似 𝓜 𝓝).
Proof.
  intros x x' y yx%相似对称 yx'%相似对称. eapply 相似有函数性; eauto.
Qed.

Lemma 偏相似对称 x a : x ▷ a ↔ a ◁ x.
Proof.
  split.
  - intros l y yx. destruct (l y yx) as [b [ba yb]].
    exists b. split; auto. now apply 相似对称.
  - intros r y yx. destruct (r y yx) as [b [ba yb]].
    exists b. split; auto. now apply 相似对称.
Qed.

Lemma 相似完全性对称 : 左完全 (@相似 𝓜 𝓝) ↔ 右完全 (@相似 𝓝 𝓜).
Proof. split; intros H x; destruct (H x) as [a ax%相似对称]; eauto. Qed.

End Symmetry_More.

(** 相似关系保持结构 **)
Section StructurePreserving_Partial.
Context {𝓜 𝓝 : ZF}.
Implicit Type x y : 𝓜.
Implicit Type a b : 𝓝.

Lemma 相似保ϵ_偏 x y a b : x ≈ a → y ≈ b → y ∈ x → b ∈ a.
Proof.
  intros [xa _] yb yx.
  destruct (xa y yx) as [c [ca yc]].
  now rewrite (相似有函数性 yb yc).
Qed.

Lemma 偏相似保空 : 𝓜.(结构).(空) ▷ 𝓝.(结构).(空).
Proof. intros x H. zf. Qed.

Lemma 偏相似保并 x a : x ▷ a → ⋃ x ▷ ⋃ a.
Proof.
  intros H y [z [yz zx]]%并集.
  destruct (H z zx) as [b [ba [zb _]]].
  destruct (zb y yz) as [c [cb yc]].
  exists c. split; auto. apply 并集. now exists b.
Qed.

Lemma 偏相似保幂 x a : x ▷ a → 𝒫 x ▷ 𝒫 a.
Proof.
  intros xa y yx%幂集.
  set (a ∩ₚ (λ c, ∃ z ∈ y, z ≈ c)) as b.
  exists b. split. apply 幂集, 分离为子集. split.
  - intros z zy. destruct (xa z (yx z zy)) as [c [ca zc]].
    exists c. split; auto. apply 分离. split; eauto.
  - intros c cb. now apply 分离 in cb.
Qed.

Definition 定义域 x := ∃ a, x ≈ a.
Definition 值域 a := ∃ x, x ≈ a.

Definition 嵌入 (R : 𝓜 → 𝓜 → Prop) : 𝓝 → 𝓝 → Prop :=
  λ a b, ∃ x y, x ≈ a ∧ y ≈ b ∧ R x y.

Lemma 嵌入有函数性 R : 函数性 R → 函数性 (嵌入 R).
Proof.
  intros FR a b c [x [y [xa [yb Rxy]]]] [x' [z [x'a [zc Rxz]]]].
  rewrite (相似单射性 x'a xa) in Rxz.
  rewrite (FR x y z Rxy Rxz) in yb.
  apply (相似有函数性 yb zc).
Qed.

Lemma 左偏相似保替代 R x a : 函数性 R →
  R @ x ⊆ₚ 定义域 → x ▷ a → R @ x ▷ 嵌入 R @ a.
Proof.
  intros FR dom xa y yR. destruct (dom y yR) as [b yb].
  exists b. split; auto. apply 替代. now apply 嵌入有函数性.
  apply 替代 in yR as [z [zx Rzy]]; auto.
  destruct (xa z zx) as [c [ca zc]].
  exists c. split; auto. now exists z, y.
Qed.

Fact 右偏相似保替代 R x a : 函数性 R →
  R @ x ⊆ₚ 定义域 → x ◁ a → R @ x ◁ 嵌入 R @ a.
Proof.
  intros FR dom xa b br.
  apply 替代 in br as [c [ca [z [y [zc [yb Rzy]]]]]]. 2: now apply 嵌入有函数性.
  exists y. split; auto. apply 替代; auto. exists z. split; auto.
  destruct (xa c ca) as [z' [z'x z'c]]. now rewrite (相似单射性 zc z'c).
Qed.

End StructurePreserving_Partial.

Section StructurePreserving.
Context {𝓜 𝓝 : ZF}.
Implicit Type x y : 𝓜.
Implicit Type a b : 𝓝.

Lemma 相似保ϵ x y a b : x ≈ a → y ≈ b → (y ∈ x ↔ b ∈ a).
Proof.
  intros xa yb. split; intros H.
  - now apply (相似保ϵ_偏 xa yb).
  - now apply (相似保ϵ_偏 (相似对称 xa) (相似对称 yb)).
Qed.

Lemma 相似保空 : 𝓜.(结构).(空) ≈ 𝓝.(结构).(空).
Proof.
  split.
  - apply 偏相似保空.
  - now apply 偏相似对称, 偏相似保空.
Qed.

Lemma 相似保并 x a : x ≈ a → ⋃ x ≈ ⋃ a.
Proof.
  intros [xa ax]. split.
  - now apply 偏相似保并.
  - now apply 偏相似对称, 偏相似保并, 偏相似对称.
Qed.

Lemma 相似保幂 x a : x ≈ a → 𝒫 x ≈ 𝒫 a.
Proof.
  intros [xa ax]. split.
  - now apply 偏相似保幂.
  - now apply 偏相似对称, 偏相似保幂, 偏相似对称.
Qed.

Lemma 相似保替代 R x a : 函数性 R →
  R @ x ⊆ₚ 定义域 → x ≈ a → R @ x ≈ 嵌入 R @ a.
Proof.
  intros FR dom xa. split.
  - now apply 左偏相似保替代, xa.
  - now apply 右偏相似保替代, xa.
Qed.

Lemma 相似保层 x a : x ≈ a → x ∈ₚ 层 → a ∈ₚ 层.
Proof.
  intros xa xS. revert a xa.
  induction xS as [x xS IH|x xS IH].
  - intros b pxb. assert (xpx: x ∈ 𝒫 x). apply 幂集. zf.
    destruct (左偏相似 pxb xpx) as [a [ab xa]].
    assert (bis: 𝒫 x ≈ 𝒫 a) by now apply 相似保幂.
    rewrite <- (相似有函数性 bis pxb). constructor. now apply IH.
  - intros b uxb. assert (xppux: x ∈ 𝒫 𝒫 ⋃ x) by apply 幂集, 幂并.
    assert (bis: 𝒫 𝒫 ⋃ x ≈ 𝒫 𝒫 b) by now apply 相似保幂, 相似保幂.
    destruct (左偏相似 bis xppux) as [a [appb xa]]. apply 相似保并 in xa as uxua.
    rewrite <- (相似有函数性 uxua uxb). constructor. intros c ca. 
    destruct (右偏相似 xa ca) as [y [yx yc]]. eapply IH; eauto.
Qed.

End StructurePreserving.

(** 相似关系的定义域 **)
Section Domain.
Context {𝓜 𝓝 : ZF}.
Implicit Type x y : 𝓜.
Implicit Type a b : 𝓝.
Notation 定义域 := (@定义域 𝓜 𝓝).

Lemma 在定义域 x a : x ≈ a → x ∈ₚ 定义域.
Proof. intros H. now exists a. Qed.

(* 对成员关系封闭 *)
Lemma 定义域是传递类 : 传递类 定义域.
Proof.
  intros x y xD [a xa].
  destruct (左偏相似 xa xD) as [b [_ yb]]. now exists b.
Qed.

(* 对子集关系封闭 *)
Lemma 定义域是膨胀类 : 膨胀类 定义域.
Proof.
  intros x y yp%幂集 [a xa%相似保幂].
  destruct (左偏相似 xa yp) as [b [_ J]]. now exists b.
Qed.

Lemma 定义域是空集封闭类 : ∅ ∈ₚ 定义域.
Proof. exists ∅. apply 相似保空. Qed.

Lemma 定义域是并集封闭类 x : x ∈ₚ 定义域 → ⋃ x ∈ₚ 定义域.
Proof. intros [a H%相似保并]. now exists (⋃ a). Qed.

Lemma 定义域是幂集封闭类 x : x ∈ₚ 定义域 → 𝒫 x ∈ₚ 定义域.
Proof. intros [a H%相似保幂]. now exists (𝒫 a). Qed.

Lemma 定义域是替代封闭类 R x : 函数性 R →
  R @ x ⊆ₚ 定义域 → x ∈ₚ 定义域 → R @ x ∈ₚ 定义域.
Proof.
  intros FR dom [a H%(相似保替代 FR dom)]. eapply 在定义域, H.
Qed.

Lemma 定义域是封闭类 : 封闭类 定义域.
Proof.
  split.
  - intros x y yx xD. eapply 定义域是传递类; eauto.
  - apply 定义域是空集封闭类.
  - intros x xu. now apply 定义域是并集封闭类.
  - intros x xu. now apply 定义域是幂集封闭类.
  - intros R x FR yD xD. apply 定义域是替代封闭类; auto.
    intros y [z [zx Rzy]]%替代; auto. eapply yD; eauto.
Qed.

Lemma 集化定义域是宇宙 : 集化 定义域 ⊑ 宇宙.
Proof.
  intros u s. exists (λ x, x ∈ₚ 定义域). split; auto.
  apply 定义域是封闭类.
Qed.

End Domain.

(** 相似关系保持宇宙性 **)
Section Universe.
Context {𝓜 𝓝 : ZF}.
Implicit Type x y : 𝓜.
Implicit Type a b : 𝓝.

Lemma 相似保传递 x a : x ≈ a → 传递 x → 传递 a.
Proof.
  intros xa xT b c cb ba.
  destruct (右偏相似 xa ba) as [y [yx yb]].
  destruct (右偏相似 yb cb) as [z [zy zc]].
  eapply (@相似保ϵ 𝓜 𝓝); eauto.
Qed.

Lemma 相似保空集封闭 x a : x ≈ a → 空集封闭 x → 空集封闭 a.
Proof. intros xa xU. now apply (相似保ϵ xa 相似保空). Qed.

Lemma 相似保并集封闭 x a : x ≈ a → 并集封闭 x → 并集封闭 a.
Proof.
  intros xa CL b ba. destruct (右偏相似 xa ba) as [y [yx yb]].
  apply 相似保并 in yb. now apply (相似保ϵ xa yb), CL.
Qed.

Lemma 相似保幂集封闭 x a : x ≈ a → 幂集封闭 x → 幂集封闭 a.
Proof.
  intros xa CL b ba. destruct (右偏相似 xa ba) as [y [yx yb]].
  apply 相似保幂 in yb. now apply (相似保ϵ xa yb), CL.
Qed.

Lemma 相似保替代封闭 x a : x ≈ a → 替代封闭 x → 替代封闭 a.
Proof.
  intros xa CL R b FR H ba. destruct (右偏相似 xa ba) as [y [yx yb]].
  apply 相似对称 in xa. apply 相似对称, (相似保替代 FR) in yb as bis.
  - apply (相似保ϵ xa bis), CL; auto. now apply 嵌入有函数性.
    intros z z' [c [c' [cz [c'z' Rcc']]]] zy. apply (相似保ϵ xa c'z').
    apply (H c); auto. now apply (相似保ϵ yb cz).
  - intros c [d [db Rdc]]%替代; auto. apply 定义域是传递类 with a.
    now apply (H d). now exists x.
Qed.

Lemma 相似保宇宙 x a : x ≈ a → 宇宙 x → 宇宙 a.
Proof.
  intros xa xU. exists (λ b, b ∈ a). split. 2: easy. split.
  - now apply 宇宙传递, (相似保传递 xa) in xU.
  - now apply 宇宙对空集封闭, (相似保空集封闭 xa) in xU.
  - now apply 宇宙对并集封闭, (相似保并集封闭 xa) in xU.
  - now apply 宇宙对幂集封闭, (相似保幂集封闭 xa) in xU.
  - now apply 宇宙对替代封闭, (相似保替代封闭 xa) in xU.
Qed.

End Universe.

(** 相似关系与层 **)
Section Hierarchy.
Context {𝓜 𝓝 : ZF}.
Implicit Type x y : 𝓜.
Implicit Type a b : 𝓝.



End Hierarchy.
