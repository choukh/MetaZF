(** Coq coding by choukh, May 2022 **)

From ZF Require Import Basic.

(*** 累积层级 ***)
Section CumulativeHierarchy.

(* 𝓜 ⊨ ZF *)
Context {𝓜 : ZF}.
Implicit Type A a b x y z : 𝓜.
Implicit Type P Q : 𝓜 → Prop.
Implicit Type R : 𝓜 → 𝓜 → Prop.

(* 层 = {V_α | α ∈ Ord} *)
Inductive 层 : 𝓜 → Prop :=
  | 幂层 x : x ∈ₚ 层 → 𝒫 x ∈ₚ 层
  | 并层 x : x ⊆ₚ 层 → ⋃ x ∈ₚ 层.

Lemma 空集层 : ∅ ∈ₚ 层.
Proof. rewrite <- 并空. constructor. zf. Qed.

(* 对成员关系封闭 *)
Lemma 层传递 : 层 ⊑ 传递.
Proof. induction 1. now apply 幂传递. now apply 并传递. Qed.

(* 对子集关系封闭 *)
Lemma 层膨胀 : 层 ⊑ 膨胀.
Proof.
  induction 1 as [x _ _|x _ IH]; intros y z.
  - intros yz zx%幂集. apply 幂集. zf.
  - intros yz [a [za ax]]%并集. apply 并集.
    exists a. split; auto. eapply IH; eauto.
Qed.

(** 线序 **)

Lemma 层对关系的归纳法 R :
  (∀ x y, R x y → R y x → R (𝒫 x) y) →
  (∀ x y, (∀ z, z ∈ x → R z y) → R (⋃ x) y) →
  ∀ x y ∈ₚ 层, R x y.
Proof.
  intros H1 H2 x xS y. revert y.
  induction xS as [x _ IHx|x xS IHx]; intros y yS.
  - apply H1. apply IHx. apply yS.
    induction yS as [y yS IHy|y _ IHy].
    + apply H1. apply IHy. apply IHx. apply yS.
    + apply H2. apply IHy.
  - apply H2. intros z zx. now apply IHx.
Qed.

Lemma 层线序_引理 : ∀ x y ∈ₚ 层, x ⊆ y ∨ 𝒫 y ⊆ x.
Proof.
  apply 层对关系的归纳法.
  - intros x y [xy|pyx] [yx|pxy]; auto.
    + right. rewrite (外延 xy yx). zf.
    + right. now apply 幂单调.
  - intros x y H. 排中 (∃ z ∈ x, z ⊈ y) as [[z [zx zny]]|false].
    + right. destruct (H z zx) as [zy|pzy]. easy.
      enough (z ⊆ ⋃ x). zf. now apply 并得父集.
    + left. apply 并得子集. intros z zx. 反证.
      apply false. now exists z.
Qed.

Lemma 层弱线序 x y : x ∈ₚ 层 → y ∈ₚ 层 → x ⊆ y ∨ y ⊆ x.
Proof.
  intros xS yS. destruct (层线序_引理 xS yS); auto.
  right. enough (y ⊆ 𝒫 y). zf. apply 传递_子集表述. apply 层传递.
  now constructor. now apply 幂集.
Qed.

Lemma 层线序 x y : x ∈ₚ 层 → y ∈ₚ 层 → x ⊆ y ∨ y ∈ x.
Proof.
  intros xS yS. destruct (层线序_引理 xS yS); auto.
  right. apply H. now apply 幂集.
Qed.

Lemma 层三歧 x y : x ∈ₚ 层 → y ∈ₚ 层 → x = y ∨ x ∈ y ∨ y ∈ x.
Proof.
  intros xS yS. destruct (层线序 xS yS); auto.
  destruct (层线序 yS xS); auto. left. now apply 外延.
Qed.

(** 良基 **)

(* 层与任意类的非空交有⊆最小元 *)
Lemma 层良基 P x : x ∈ₚ 层 ⊓ P → ex (最小 (层 ⊓ P)).
Proof.
  intros [xS xP]. induction (正则 x) as [x _ IH].
  排中 (∃ y ∈ x, y ∈ₚ 层 ∧ y ∈ₚ P) as [[y [yx [yS yP]]]|].
  - now apply (IH y).
  - exists x. repeat split; auto. intros y [yS yP].
    destruct (层线序 xS yS). auto.
    contradict H. now exists y.
Qed.

(** rank **)

Definition 秩关系 x y := x ⊆ y ∧ x ∉ y ∧ y ∈ₚ 层.

Lemma 秩关系的函数性 : 函数性 秩关系.
Proof.
  intros x a b [xsa [xa aS]] [xsb [xb bS]].
  destruct (层三歧 aS bS) as [|[]]; auto; exfalso.
  - apply xb. apply 层膨胀 with a; auto.
  - apply xa. apply 层膨胀 with b; auto.
Qed.

Definition ρ x := δ (秩关系 x).
Definition ρ' x := ⋃ (𝒫[ρ[x]]).

Lemma ρ规范_引理 x y : 秩关系 x y → 秩关系 x (ρ x).
Proof.
  intros H. unfold ρ. eapply δ规范. apply H.
  hnf. apply 秩关系的函数性.
Qed.

Lemma ρ'规范 x : 秩关系 x (ρ' x).
Proof.
  induction (正则 x) as [x _ IH]. repeat split.
  - intros y yx. apply 并集. exists (𝒫 (ρ y)). split.
    + apply 幂集. eapply ρ规范_引理. apply IH. apply yx.
    + now apply 函数式替代2I.
  - intros [y[xy yp]]%并集.
    apply 函数式替代2E in yp as [a [ax ->]]. apply 幂集 in xy.
    enough (秩关系 a (ρ a)). apply H, xy, ax.
    eapply ρ规范_引理. now apply IH.
  - constructor. intros y [a [ax ->]]%函数式替代2E.
    constructor. eapply ρ规范_引理. now apply IH.
Qed.

Lemma ρ规范 x : 秩关系 x (ρ x).
Proof. eapply ρ规范_引理. apply ρ'规范. Qed.

Fact ρ_0 : ρ ∅ = ∅.
Proof. eapply 秩关系的函数性. apply ρ规范. repeat split; zf. apply 空集层. Qed.

Remark ρ等于ρ' x : ρ x = ρ' x.
Proof. apply δ求值. apply ρ'规范. hnf. apply 秩关系的函数性. Qed.

Definition 可及 x := ∃ y, x ∈ y ∧ y ∈ₚ 层.

(* V = WF *)
Theorem 全可及 x : 可及 x.
Proof.
  exists (𝒫 (ρ x)). split.
  - apply 幂集. apply ρ规范.
  - constructor. apply ρ规范.
Qed.

Lemma 并_等秩 x y : x ∈ y → y ∈ₚ 层 → ⋃ x ∈ y.
Proof.
  intros xy. induction 1 as [y yS _|y yS IH].
  - apply 幂集 in xy. apply 幂集.
    intros a [b [ab bx%xy]]%并集. eapply 层传递; eauto.
  - apply 并集 in xy as [a [xa ax]].
    apply 并集. exists a. split; auto.
Qed.

Lemma 分离_等秩 x y P : x ∈ y → y ∈ₚ 层 → x ∩ₚ P ∈ y.
Proof. intros xy yS. eapply 层膨胀; eauto. apply 分离为子集. Qed.

Lemma 幂_升秩 x y : x ∈ y → y ∈ₚ 层 → 𝒫 x ∈ 𝒫 y.
Proof.
  intros xy. destruct 1 as [y _|y yS].
  - apply 幂集 in xy. apply 幂集. now apply 幂单调.
  - apply 并集 in xy as [a [xa ay]]. apply 幂集.
    intros b bx%幂集. apply 并集. exists a.
    split; auto. eapply 层膨胀; eauto.
Qed.

Lemma 配对_升秩 a b x : a ∈ x → b ∈ x → {a, b} ∈ 𝒫 x.
Proof. intros ax bx. apply 幂集. intros c [ca|cb]%配对; now subst. Qed.

Lemma 后继_升秩 x y : x ∈ y → y ∈ₚ 层 → x⁺ ∈ 𝒫 y.
Proof.
  intros xy yS. apply 幂集. intros z zx.
  apply 后继 in zx as [->|]. trivial. apply 层传递 with x; auto.
Qed.

(** 后继层与极限层 **)

Definition 后继层 x := ∃ y ∈ₚ 层, x = 𝒫 y.
Definition 极限层 x := x ∈ₚ 层 ∧ x ⊆ ⋃ x.

Remark 极限层等价定义 x : 极限层 x ↔ x ∈ₚ 层 ∧ x = ⋃ x.
Proof.
  split.
  - intros [xS sub]. split. auto.
    apply 外延. auto. apply 并得子集. firstorder using 层传递.
  - intros [xS eq]. split. auto. rewrite eq at 1. zf.
Qed.

Lemma 层之集二分 x : x ⊆ₚ 层 → ⋃ x ∈ x ∨ x ⊆ ⋃ x.
Proof.
  intros sub. 排中 (x ⊆ ⋃ x); auto. left.
  apply 非子集 in H as [y[yx yns]].
  replace (⋃ x) with y; auto. symmetry.
  apply 并即上确界. split; auto.
  intros z zx. destruct (层线序 (sub z zx) (sub y yx)); auto.
  exfalso. apply yns. apply 并集. now exists z.
Qed.

Fact 层二分 x : x ∈ₚ 层 → x ∈ₚ 后继层 ∨ x ∈ₚ 极限层.
Proof.
  induction 1 as [x xS _|x xS IH].
  - left. exists x. auto.
  - destruct (层之集二分 xS).
    + apply IH, H.
    + right. split. now constructor.
      intros y [z [yz zx]]%并集.
      apply 并集. exists z. auto.
Qed.

(** 封闭性 **)

Definition 秩封闭 x := ∀ y ∈ x, ∃ z ∈ₚ 层, y ∈ z ∧ z ∈ x.

Lemma 极限层对秩封闭 : 极限层 ⊑ 秩封闭.
Proof.
  intros x [xS sub]. induction xS as [x _ _|x xS IH].
  - rewrite 并幂 in sub. now apply 幂集在上 in sub.
  - destruct (层之集二分 xS). now apply IH.
    intros y [z [yz zx]]%并集. exists z. auto.
Qed.

Lemma 非空层对空集封闭 x : x ∈ₚ 层 → 非空 x → 空集封闭 x.
Proof.
  intros xS [y yx].
  destruct (层线序 xS 空集层); auto. apply H in yx. zf.
Qed.

Lemma 极限层对并集封闭 : 极限层 ⊑ 并集封闭.
Proof. intros x [xS _] y yx. now apply 并_等秩. Qed.

Lemma 极限层对幂集封闭 : 极限层 ⊑ 幂集封闭.
Proof.
  intros x xL y yx.
  destruct (极限层对秩封闭 xL yx) as [z [zS [yz zx]]].
  destruct xL as [xS _]. destruct (层线序 (幂层 zS) xS).
  - apply (幂_升秩 yz) in zS as pypz. auto.
  - exfalso. apply 幂集 in H. specialize (H z zx).
    now apply 无循环1 in H.
Qed.

Fact 极限层对配对封闭 : 极限层 ⊑ 配对封闭.
Proof.
  intros x xL a ax b bx.
  destruct (极限层对秩封闭 xL ax) as [y [yS [ay yx]]].
  destruct (极限层对秩封闭 xL bx) as [z [zS [bz zx]]].
  destruct (层弱线序 yS zS).
  - apply 层传递 with (z:=𝒫 z). apply xL.
    + apply 配对_升秩; auto.
    + now apply 极限层对幂集封闭.
  - apply 层传递 with (z:=𝒫 y). apply xL.
    + apply 配对_升秩; auto.
    + now apply 极限层对幂集封闭.
Qed.

Fact 极限层对分离封闭 : 极限层 ⊑ 分离封闭.
Proof. intros x [xL _] P y yx. now apply 分离_等秩. Qed.

End CumulativeHierarchy.
