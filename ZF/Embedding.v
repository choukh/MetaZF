(** Coq coding by choukh, May 2022 **)

Require Import ZF.Basic Hierarchy Universe.

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

Definition 定义域 {𝓜 𝓝 : ZF} (x : 𝓜) := ∃ a : 𝓝, x ≈ a.
Definition 值域 {𝓜 𝓝 : ZF} (a : 𝓝) := ∃ x : 𝓜, x ≈ a.
Notation 𝕯 := 定义域.
Notation 𝕹 := 值域.

(** 相似关系的对称性 **)
Section Symmetry.
Context {𝓜 𝓝 : ZF}.
Implicit Type x y : 𝓜.
Implicit Type a b : 𝓝.

Lemma 左嵌入 x a : x ≈ a → x ▷ a.
Proof. now intros []. Qed.

Lemma 右嵌入 x a : x ≈ a → x ◁ a.
Proof. now intros []. Qed.

Lemma 相似的对称性 x a : x ≈ a → a ≈ x.
Proof.
  pose proof (正则 x) as WF. revert a.
  induction WF as [x _ IH].
  intros a [l r]. split.
  - intros b ba. destruct (r b ba) as [y [yx yb]].
    exists y. split; auto.
  - intros y yx. destruct (l y yx) as [b [ba yb]].
    exists b. split; auto.
Qed.

Lemma 相似的函数性 : 函数性 (@相似 𝓜 𝓝).
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

Lemma 相似的单射性 : 单射性 (@相似 𝓜 𝓝).
Proof.
  intros x x' y yx%相似的对称性 yx'%相似的对称性. eapply 相似的函数性; eauto.
Qed.

Lemma 相似的完全性性对称 : 右完全 (@相似 𝓜 𝓝) ↔ 左完全 (@相似 𝓝 𝓜).
Proof. split; intros H x; destruct (H x) as [a ax%相似的对称性]; eauto. Qed.

Lemma 嵌入对称 x a : x ▷ a ↔ a ◁ x.
Proof.
  split.
  - intros l y yx. destruct (l y yx) as [b [ba yb]].
    exists b. split; auto. now apply 相似的对称性.
  - intros r y yx. destruct (r y yx) as [b [ba yb]].
    exists b. split; auto. now apply 相似的对称性.
Qed.

Lemma 域对称 x : x ∈ₚ 𝕯 ↔ x ∈ₚ @𝕹 𝓝 𝓜.
Proof. split; intros [a xa]; exists a; now apply 相似的对称性. Qed.

Lemma 域集化对称 x : 集化 (@𝕯 𝓜 𝓝) x ↔ 集化 (@𝕹 𝓝 𝓜) x.
Proof.
  split; intros sd; intros y; split; intros H.
  - apply 域对称, sd, H.
  - apply sd, 域对称, H.
  - apply 域对称, sd, H.
  - apply sd, 域对称, H.
Qed.

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
  now rewrite (相似的函数性 yb yc).
Qed.

Lemma 嵌入保空 : 𝓜.(结构).(空) ▷ 𝓝.(结构).(空).
Proof. intros x H. zf. Qed.

Lemma 嵌入保并 x a : x ▷ a → ⋃ x ▷ ⋃ a.
Proof.
  intros H y [z [yz zx]]%并集.
  destruct (H z zx) as [b [ba [zb _]]].
  destruct (zb y yz) as [c [cb yc]].
  exists c. split; auto. apply 并集. now exists b.
Qed.

Lemma 嵌入保幂 x a : x ▷ a → 𝒫 x ▷ 𝒫 a.
Proof.
  intros xa y yx%幂集.
  set (a ∩ₚ (λ c, ∃ z ∈ y, z ≈ c)) as b.
  exists b. split. apply 幂集, 分离为子集. split.
  - intros z zy. destruct (xa z (yx z zy)) as [c [ca zc]].
    exists c. split; auto. apply 分离. split; eauto.
  - intros c cb. now apply 分离 in cb.
Qed.

Definition 关系嵌入 (R : 𝓜 → 𝓜 → Prop) : 𝓝 → 𝓝 → Prop :=
  λ a b, ∃ x y, x ≈ a ∧ y ≈ b ∧ R x y.
Notation "⌜ R ⌝" := (关系嵌入 R) (format "⌜ R ⌝").

Lemma 关系嵌入的函数性 R : 函数性 R → 函数性 ⌜R⌝.
Proof.
  intros FR a b c [x [y [xa [yb Rxy]]]] [x' [z [x'a [zc Rxz]]]].
  rewrite (相似的单射性 x'a xa) in Rxz.
  rewrite (FR x y z Rxy Rxz) in yb.
  apply (相似的函数性 yb zc).
Qed.

Lemma 左嵌入保替代 R x a : 函数性 R → R @ x ⊆ₚ 𝕯 → x ▷ a → R @ x ▷ ⌜R⌝ @ a.
Proof.
  intros FR dom xa y yR. destruct (dom y yR) as [b yb].
  exists b. split; auto. apply 替代. now apply 关系嵌入的函数性.
  apply 替代 in yR as [z [zx Rzy]]; auto.
  destruct (xa z zx) as [c [ca zc]].
  exists c. split; auto. now exists z, y.
Qed.

Fact 右嵌入保替代 R x a : 函数性 R → R @ x ⊆ₚ 𝕯 → x ◁ a → R @ x ◁ ⌜R⌝ @ a.
Proof.
  intros FR dom xa b br.
  apply 替代 in br as [c [ca [z [y [zc [yb Rzy]]]]]]. 2: now apply 关系嵌入的函数性.
  exists y. split; auto. apply 替代; auto. exists z. split; auto.
  destruct (xa c ca) as [z' [z'x z'c]]. now rewrite (相似的单射性 zc z'c).
Qed.

End StructurePreserving_Partial.

Section StructurePreserving.
Context {𝓜 𝓝 : ZF}.
Implicit Type x y : 𝓜.
Implicit Type a b : 𝓝.
Notation "⌜ R ⌝" := (关系嵌入 R) (format "⌜ R ⌝").

Lemma 相似保ϵ x y a b : x ≈ a → y ≈ b → (y ∈ x ↔ b ∈ a).
Proof.
  intros xa yb. split; intros H.
  - now apply (相似保ϵ_偏 xa yb).
  - now apply (相似保ϵ_偏 (相似的对称性 xa) (相似的对称性 yb)).
Qed.

Lemma 相似保空 : 𝓜.(结构).(空) ≈ 𝓝.(结构).(空).
Proof.
  split.
  - apply 嵌入保空.
  - now apply 嵌入对称, 嵌入保空.
Qed.

Lemma 相似保并 x a : x ≈ a → ⋃ x ≈ ⋃ a.
Proof.
  intros [xa ax]. split.
  - now apply 嵌入保并.
  - now apply 嵌入对称, 嵌入保并, 嵌入对称.
Qed.

Lemma 相似保幂 x a : x ≈ a → 𝒫 x ≈ 𝒫 a.
Proof.
  intros [xa ax]. split.
  - now apply 嵌入保幂.
  - now apply 嵌入对称, 嵌入保幂, 嵌入对称.
Qed.

Lemma 相似保替代 R x a : 函数性 R → R @ x ⊆ₚ 𝕯 → x ≈ a → R @ x ≈ ⌜R⌝ @ a.
Proof.
  intros FR dom xa. split.
  - now apply 左嵌入保替代, xa.
  - now apply 右嵌入保替代, xa.
Qed.

Lemma 相似保层 x a : x ≈ a → x ∈ₚ 层 → a ∈ₚ 层.
Proof.
  intros xa xS. revert a xa.
  induction xS as [x xS IH|x xS IH].
  - intros b pxb. assert (xpx: x ∈ 𝒫 x). apply 幂集. zf.
    destruct (左嵌入 pxb xpx) as [a [ab xa]].
    assert (bis: 𝒫 x ≈ 𝒫 a) by now apply 相似保幂.
    rewrite <- (相似的函数性 bis pxb). constructor. now apply IH.
  - intros b uxb. assert (xppux: x ∈ 𝒫 𝒫 ⋃ x) by apply 幂集, 幂并.
    assert (bis: 𝒫 𝒫 ⋃ x ≈ 𝒫 𝒫 b) by now apply 相似保幂, 相似保幂.
    destruct (左嵌入 bis xppux) as [a [appb xa]]. apply 相似保并 in xa as uxua.
    rewrite <- (相似的函数性 uxua uxb). constructor. intros c ca. 
    destruct (右嵌入 xa ca) as [y [yx yc]]. eapply IH; eauto.
Qed.

End StructurePreserving.

(** 相似关系的定义域 **)
Section Domain.
Context {𝓜 𝓝 : ZF}.
Implicit Type x y : 𝓜.
Implicit Type a b : 𝓝.
Notation 𝕯 := (@𝕯 𝓜 𝓝).
Notation "⌜ R ⌝" := (关系嵌入 R) (format "⌜ R ⌝").

(* 对成员关系封闭 *)
Lemma 定义域是传递类 : 传递类 𝕯.
Proof.
  intros x y xy [a xa].
  destruct (左嵌入 xa xy) as [b [_ yb]]. now exists b.
Qed.

(* 对子集关系封闭 *)
Lemma 定义域是膨胀类 : 膨胀类 𝕯.
Proof.
  intros x y xpy%幂集 [a xa%相似保幂].
  destruct (左嵌入 xa xpy) as [b [_ J]]. now exists b.
Qed.

Lemma 定义域是空集封闭类 : ∅ ∈ₚ 𝕯.
Proof. exists ∅. apply 相似保空. Qed.

Lemma 定义域是并集封闭类 x : x ∈ₚ 𝕯 → ⋃ x ∈ₚ 𝕯.
Proof. intros [a H%相似保并]. now exists (⋃ a). Qed.

Lemma 定义域是幂集封闭类 x : x ∈ₚ 𝕯 → 𝒫 x ∈ₚ 𝕯.
Proof. intros [a H%相似保幂]. now exists (𝒫 a). Qed.

Lemma 定义域是替代封闭类 R x : 函数性 R → R @ x ⊆ₚ 𝕯 → x ∈ₚ 𝕯 → R @ x ∈ₚ 𝕯.
Proof.
  intros FR dom [a H%(相似保替代 FR dom)]. now exists (⌜R⌝ @ a).
Qed.

Lemma 定义域是封闭类 : 封闭类 𝕯.
Proof.
  split.
  - intros x y yx xD. eapply 定义域是传递类; eauto.
  - apply 定义域是空集封闭类.
  - intros x xu. now apply 定义域是并集封闭类.
  - intros x xu. now apply 定义域是幂集封闭类.
  - intros R x FR yD xD. apply 定义域是替代封闭类; auto.
    intros y [z [zx Rzy]]%替代; auto. eapply yD; eauto.
Qed.

Lemma 集化定义域是宇宙 : 集化 𝕯 ⊑ 宇宙.
Proof.
  intros u s. exists (λ x, x ∈ₚ 𝕯). split; auto.
  apply 定义域是封闭类.
Qed.

Lemma 集化值域是宇宙 : 集化 (@𝕹 𝓝 𝓜) ⊑ 宇宙.
Proof. intros u s. apply 域集化对称 in s. apply 集化定义域是宇宙, s. Qed.

End Domain.

(** 相似关系与宇宙 **)
Section Universe.
Context {𝓜 𝓝 : ZF}.
Implicit Type x y : 𝓜.
Implicit Type a b : 𝓝.

Lemma 相似保传递 x a : x ≈ a → 传递 x → 传递 a.
Proof.
  intros xa xT b c cb ba.
  destruct (右嵌入 xa ba) as [y [yx yb]].
  destruct (右嵌入 yb cb) as [z [zy zc]].
  eapply (@相似保ϵ 𝓜 𝓝); eauto.
Qed.

Lemma 相似保空集封闭 x a : x ≈ a → 空集封闭 x → 空集封闭 a.
Proof. intros xa xU. now apply (相似保ϵ xa 相似保空). Qed.

Lemma 相似保并集封闭 x a : x ≈ a → 并集封闭 x → 并集封闭 a.
Proof.
  intros xa CL b ba. destruct (右嵌入 xa ba) as [y [yx yb]].
  apply 相似保并 in yb. now apply (相似保ϵ xa yb), CL.
Qed.

Lemma 相似保幂集封闭 x a : x ≈ a → 幂集封闭 x → 幂集封闭 a.
Proof.
  intros xa CL b ba. destruct (右嵌入 xa ba) as [y [yx yb]].
  apply 相似保幂 in yb. now apply (相似保ϵ xa yb), CL.
Qed.

Lemma 相似保替代封闭 x a : x ≈ a → 替代封闭 x → 替代封闭 a.
Proof.
  intros xa CL R b FR H ba. destruct (右嵌入 xa ba) as [y [yx yb]].
  apply 相似的对称性 in xa. apply 相似的对称性, (相似保替代 FR) in yb as bis.
  - apply (相似保ϵ xa bis), CL; auto. now apply 关系嵌入的函数性.
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

Lemma 相似保宇宙等级 n x a : x ≈ a → ZFₙ n x → ZFₙ n a.
Proof.
  revert x a. induction n; simpl. auto.
  intros x a xa [y [yx [yU zfn]]].
  destruct (左嵌入 xa yx) as [b [ba yb]].
  exists b. split; auto. split.
  now apply (相似保宇宙 yb). now apply (IHn y).
Qed.

End Universe.

(** 相似关系与层 **)
Section Hierarchy.
Context {𝓜 𝓝 : ZF}.
Implicit Type x y : 𝓜.
Implicit Type a b : 𝓝.
Arguments 相似 : clear implicits.

(* 定义域外的最低层可嵌入到值域外的任意层 *)
Lemma 外层嵌入 x a :
  x ∈ₚ 最小 (λ x, x ∈ₚ 层 ∧ x ∉ₚ @𝕯 𝓜 𝓝) →
  a ∈ₚ 层 → a ∉ₚ @𝕯 𝓝 𝓜 → x ▷ a.
Proof.
  intros [[xS xD] min] aS aR.
  induction xS as [x xS IH|x xS IH].
  - exfalso. 排中 (x ∈ₚ 𝕯).
    + now apply xD, 定义域是幂集封闭类.
    + now apply 幂集在上 with x, min.
  - destruct (层二歧_引理 xS) as [suc|lim]. apply IH; auto.
    intros y [z [yz zx]]%并集. 排中 (z ∈ₚ 𝕯) as [[c zc]|].
    + assert (cS : c ∈ₚ 层). apply 相似保层 with z; auto.
      destruct (层ϵ线序 aS cS) as [ac|ca].
      * exfalso. apply aR, 定义域是膨胀类 with c.
        apply ac. exists z. now apply 相似的对称性.
      * destruct (左嵌入 zc yz) as [b [ba yb]].
        exists b. split; auto. eapply 层传递; eauto.
    + exfalso. apply 无循环1 with z. apply min; auto.
Qed.

Lemma 存在外层 : ¬ 左完全 (相似 𝓜 𝓝) → ∃ x ∈ₚ 层, x ∉ₚ 𝕯.
Proof.
  intros H. 反证. apply H.
  intros y. 反证. apply 反设.
  destruct (全可及 y) as [z [yz zS]].
  exists z. split; auto. intros [a za].
  destruct (左嵌入 za yz) as [b [ba yb]].
  apply 反设0. now exists b.
Qed.

Lemma 外层包含定义域 x : 左完全 (相似 𝓝 𝓜) → x ∈ₚ 层 → x ∉ₚ 𝕯 → 𝕯 ⊆ₛ x.
Proof.
  intros sur xS ndx y [a ya].
  destruct (全可及 a) as [b [ab bS]].
  destruct (sur b) as [z bz].
  assert (zS : z ∈ₚ 层). eapply 相似保层; eauto. apply 相似的对称性 in bz.
  assert (yz : y ∈ z). eapply 相似保ϵ; eauto.
  destruct (层ϵ线序 zS xS); auto. contradict ndx.
  apply 定义域是传递类 with z; auto. now exists b.
Qed.

Lemma 定义域集化 : ¬ 左完全 (相似 𝓜 𝓝) → 左完全 (相似 𝓝 𝓜) → 可集化 (@𝕯 𝓜 𝓝).
Proof.
  intros H1 H2. apply 存在外层 in H1 as [x [xS ndx]].
  apply 集的子类可集化 with x, 外层包含定义域; auto.
Qed.

Lemma 值域域集化 : ¬ 左完全 (相似 𝓜 𝓝) → 左完全 (相似 𝓝 𝓜) → 可集化 (@𝕹 𝓝 𝓜).
Proof.
  intros H1 H2. pose proof (定义域集化 H1 H2) as [x s].
  apply 域集化对称 in s. now exists x.
Qed.

End Hierarchy.

(** 相似的完全性 **)
Section Totality.
Variable 𝓜 𝓝 : ZF.
Implicit Type x y : 𝓜.
Implicit Type a b : 𝓝.
Arguments 𝕯 : clear implicits.
Arguments 𝕹 : clear implicits.
Arguments 相似 : clear implicits.

(* 定义域外的最低层与值域外的最低层相似 *)
Lemma 外层相似 x a :
  x ∈ₚ 最小 (λ x, x ∈ₚ 层 ∧ x ∉ₚ 𝕯 𝓜 𝓝) →
  a ∈ₚ 最小 (λ a, a ∈ₚ 层 ∧ a ∉ₚ 𝕯 𝓝 𝓜) → x ≈ a.
Proof.
  intros H1 H2. split.
  - apply 外层嵌入. apply H1. apply H2. apply H2.
  - apply 嵌入对称, 外层嵌入. apply H2. apply H1. apply H1.
Qed.

Lemma 相似对层的完全性 : 层 ⊑ 𝕯 𝓜 𝓝 ∨ 层 ⊑ 𝕯 𝓝 𝓜.
Proof.
  反证. apply not_or_and in 反设 as [H1 H2].
  apply 非子类 in H1 as [x [xS ndx]].
  apply 非子类 in H2 as [a [aS nda]].
  destruct (层良基 (P:=(λ x, x ∉ₚ 𝕯 𝓜 𝓝)) xS ndx) as [y my].
  destruct (层良基 (P:=(λ a, a ∉ₚ 𝕯 𝓝 𝓜)) aS nda) as [b mb].
  apply my. exists b. now apply 外层相似.
Qed.

Theorem 相似的完全性 : 左完全 (相似 𝓜 𝓝) ∨ 右完全 (相似 𝓜 𝓝).
Proof.
  反证. apply not_or_and in 反设 as [H1 H2].
  rewrite 相似的完全性性对称 in H2.
  apply 存在外层 in H1 as [x [xS ndx]].
  apply 存在外层 in H2 as [a [aS nda]].
  destruct 相似对层的完全性; auto.
Qed.

Theorem 相似的完全性三歧 :
  (左完全 (相似 𝓜 𝓝) ∧ 右完全 (相似 𝓜 𝓝)) ∨
  (左完全 (相似 𝓜 𝓝) ∧ 可集化 (𝕹 𝓜 𝓝)) ∨
  (右完全 (相似 𝓜 𝓝) ∧ 可集化 (𝕯 𝓜 𝓝)).
Proof.
  排中 (左完全 (相似 𝓜 𝓝)) as [l|nl];
  排中 (右完全 (相似 𝓜 𝓝)) as [r|nr].
  - now left.
  - right. left. split. apply l.
    rewrite 相似的完全性性对称 in nr.
    now apply 值域域集化.
  - right. right. split. apply r.
    rewrite 相似的完全性性对称 in r.
    now apply 定义域集化.
  - destruct 相似的完全性; easy.
Qed.

End Totality.

(** 模型间嵌入 **)
Section Embedding.
Variable 𝓜 𝓝 : ZF.
Implicit Type x y : 𝓜.
Implicit Type a b : 𝓝.
Notation 𝕯 := (@𝕯 𝓜 𝓝).
Notation 𝕹 := (@𝕹 𝓜 𝓝).
Arguments 相似 : clear implicits.

Definition i x := δ (λ a, x ≈ a).
Definition j a := δ (λ x, x ≈ a).

Lemma i规范 x : x ∈ₚ 𝕯 → x ≈ i x.
Proof.
  intros [a xa]. unfold i. apply δ规范 with a; auto.
  intros b c xb xc. apply (相似的函数性 xb xc).
Qed.

Lemma j规范 a : a ∈ₚ 𝕹 → j a ≈ a.
Proof.
  intros [x xa]. unfold j. apply δ规范 with x; auto.
  intros y z ya za. apply (相似的单射性 ya za).
Qed.

Lemma ij a : a ∈ₚ 𝕹 → i (j a) = a.
Proof.
  intros aR. apply δ求值.
  - apply j规范, aR.
  - hnf. apply 相似的函数性.
Qed.

Lemma ji x : x ∈ₚ 𝕯 → j (i x) = x.
Proof.
  intros aR. apply δ求值.
  - apply i规范, aR.
  - hnf. intros. eapply 相似的单射性; eauto.
Qed.

Lemma j定义域 a : 右完全 (相似 𝓜 𝓝) → j a ∈ₚ 𝕯.
Proof. intros. exists a. apply j规范, H. Qed.

Lemma i值域 x : 左完全 (相似 𝓜 𝓝) → i x ∈ₚ 𝕹.
Proof. intros. exists x. apply i规范, H. Qed.

End Embedding.
