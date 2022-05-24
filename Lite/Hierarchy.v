(** Coq coding by choukh, May 2022 **)

Require Import Lite.Basic Lite.InnerModel.

(*** 累积分层 ***)
Section CumulativeHierarchy.

(* 𝓜 ⊨ ZF *)
Variable 𝓜 : ZF.
Implicit Type A B C X Y Z a b c x y z : 𝓜.
Implicit Type P Q : 𝓜 → Prop.
Implicit Type R : 𝓜 → 𝓜 → Prop.

Inductive 层 : 𝓜 → Prop :=
  | 升 x : x ∈ₚ 层 → 层 (𝒫 x)
  | 降 x : x ⊆ₚ 层 → 层 (⋃ x).

Lemma 空集层 : ∅ ∈ₚ 层.
Proof. rewrite <- 并空. constructor. zf. Qed.

Lemma 层传递 : 层 ⊑ 传递.
Proof. induction 1. now apply 幂传递. now apply 并传递. Qed.

Lemma 层膨胀 : 层 ⊑ 膨胀.
Proof.
  induction 1 as [x _ _|x _ IH]; intros a b.
  - intros ax%幂集 ba. apply 幂集. zf.
  - intros [c [ac cx]]%并集 ba. apply 并集.
    exists c. split; auto. eapply IH; eauto.
Qed.

Lemma 并_不升 x y : x ∈ y → y ∈ₚ 层 → ⋃ x ∈ y.
Proof.
  intros xa. induction 1 as [a aS _|a aS IH].
  - apply 幂集 in xa. apply 幂集.
    intros b [c [bc ca%xa]]%并集. eapply 层传递; eauto.
  - apply 并集 in xa as [b [xb ba]].
    apply 并集. exists b. split; auto.
Qed.

Lemma 分离_不升 x y P : x ∈ y → y ∈ₚ 层 → x ∩ₚ P ∈ y.
Proof. intros xy yS. eapply 层膨胀; eauto. apply 分离为子集. Qed.

Lemma 幂_升 x y : x ∈ y → y ∈ₚ 层 → 𝒫 x ∈ 𝒫 y.
Proof.
  intros xa. destruct 1 as [a _|a aS].
  - apply 幂集 in xa. apply 幂集. now apply 幂单调.
  - apply 并集 in xa as [b [xb ba]]. apply 幂集.
    intros c cx%幂集. apply 并集. exists b.
    split; auto. eapply 层膨胀; eauto.
Qed.

Lemma 配对_升 a b x : a ∈ x → b ∈ x → [a, b] ∈ 𝒫 x.
Proof. intros ax bx. apply 幂集. intros c [ca|cb]%配对; now subst. Qed.

(** 线序 **)

Lemma 层递归原理 R :
  (∀ x y, R x y → R y x → R (𝒫 x) y) →
  (∀ x y, (∀ z, z ∈ x → R z y) → R (⋃ x) y) →
  ∀ x y, x ∈ₚ 层 → y ∈ₚ 层 → R x y.
Proof.
  intros H1 H2 x y xS. revert y.
  induction xS as [x xS IHx|x xS IHx]; intros y yS.
  - apply H1. apply IHx. apply yS.
    induction yS as [y yS IHy|y yS IHy].
    + apply H1. apply IHy. apply IHx. apply yS.
    + apply H2. apply IHy.
  - apply H2. intros z zx. now apply IHx.
Qed.

Lemma 层_线序_引理 : ∀ x y, x ∈ₚ 层 → y ∈ₚ 层 → x ⊆ y ∨ 𝒫 y ⊆ x.
Proof.
  apply 层递归原理.
  - intros x y [xy|pyx] [yx|pxy]; auto.
    + right. rewrite (外延 xy yx). zf.
    + right. now apply 幂单调.
  - intros x y H. 排中 (∃ z ∈ x, z ⊈ y) as [[z [zx zny]]|false].
    + right. destruct (H z zx) as [zy|pzy]. easy.
      enough (z ⊆ ⋃ x). zf. now apply 并得父集.
    + left. apply 并得子集. intros z zx. 反证.
      apply false. now exists z.
Qed.

Lemma 层_线序 x y : x ∈ₚ 层 → y ∈ₚ 层 → x ⊆ y ∨ y ⊆ x.
Proof.
  intros xS yS. destruct (层_线序_引理 xS yS); auto.
  right. enough (y ⊆ 𝒫 y). zf. apply 层传递.
  now constructor. now apply 幂集.
Qed.

Lemma 层_ϵ线序 x y : x ∈ₚ 层 → y ∈ₚ 层 → x ⊆ y ∨ y ∈ x.
Proof.
  intros xS yS. destruct (层_线序_引理 xS yS); auto.
  right. apply H. now apply 幂集.
Qed.

Lemma 层_三歧 x y : x ∈ₚ 层 → y ∈ₚ 层 → x ∈ y ∨ x = y ∨ y ∈ x.
Proof.
  intros xS yS. destruct (层_ϵ线序 xS yS); auto.
  destruct (层_ϵ线序 yS xS); auto. right. left. now apply 外延.
Qed.



End CumulativeHierarchy.
