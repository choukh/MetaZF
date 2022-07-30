(** Coq coding by choukh, July 2022 **)

From ZF Require Import Basic AdjunctionFacts Hierarchy.

(** 遗传有限集 **)
Section HereditarilyFinite.
Context {𝓜 : ZF}.

Inductive 有限集 : 𝓜 → Prop :=
  | 有限集_空 : 有限集 ∅
  | 有限集_并 x y : 有限集 y → 有限集 (x ⨮ y).

Inductive 遗传有限集 : 𝓜 → Prop :=
  | 遗传有限集引入 x : 有限集 x → (∀ y ∈ x, 遗传有限集 y) → 遗传有限集 x.

(* 遗传有限集之类 *)
Notation HF := 遗传有限集.

Lemma HF集是有限集 x : HF x → 有限集 x.
Proof. now intros []. Qed.

Lemma HF是成员封闭类 : 传递类 HF.
Proof. destruct 2. now apply H1. Qed.

Lemma HF是空集封闭类 : ∅ ∈ₚ HF.
Proof. constructor. constructor. constructor; zf. Qed.

Lemma 二元并对有限集封闭 a b : 有限集 a → 有限集 b → 有限集 (a ∪ b).
Proof.
  intros H. revert b. induction H as [|x z H IH].
  - intros b Fb. now rewrite 左并空.
  - intros b Fb. rewrite 并入二元并结合律.
    constructor. now apply IH.
Qed.

Lemma HF是并集封闭类 a : HF a → HF ⋃ a.
Proof.
  intros [x Fx sub]. constructor.
  - induction Fx as [|x y Fin].
    + rewrite 并空. constructor.
    + rewrite 并入之并. apply 二元并对有限集封闭.
      * apply HF集是有限集, sub, 并入. auto.
      * apply IHFin. intros z zy.
        apply sub, 并入. auto.
  - intros y [z [yz zx]]%并集. apply sub in zx.
    destruct zx as [z]. now apply H0.
Qed.

Lemma 子集对有限集封闭 a b : b ⊆ a → 有限集 a → 有限集 b.
Proof.
  intros sub Fa. generalize dependent b.
  induction Fa as [|x y Fy IH]; intros b sub.
  - apply 空集的子集 in sub as ->. constructor.
  - 排中 (x ∈ b) as [X|X].
    + rewrite <- (分离掉再并回去 X). constructor.
      apply IH. intros a [ab neq]%分离. apply sub in ab.
      apply 并入 in ab as []; easy.
    + apply IH. intros a ab. apply sub in ab as axy.
      apply 并入 in axy as []; congruence.
Qed.

Lemma 替代对有限集封闭 R a : 函数性 R → 有限集 a → 有限集 (R @ a).
Proof.
  intros Fun Fa. induction Fa as [|x y H IH].
  - rewrite 替代空. constructor. trivial.
  - eapply 子集对有限集封闭. apply 并入之替代. trivial. now constructor.
Qed.

Corollary 函数式替代对有限集封闭 F a : 有限集 a → 有限集 F[a].
Proof. intros H. apply 替代对有限集封闭; congruence. Qed.

Lemma HF是替代封闭类 R a : 函数性 R →
  (∀ x y : 𝓜, R x y → x ∈ a → HF y) → HF a → HF (R @ a).
Proof.
  intros Fun H1 H2. split.
  - apply 替代对有限集封闭. trivial. now apply HF集是有限集.
  - intros y [x [xa Rxy]] % 替代; trivial. eapply H1; eauto.
Qed.

Lemma 幂集对有限集封闭 a : 有限集 a → 有限集 (𝒫 a).
Proof.
  induction 1 as [|x y H IH].
  - rewrite 幂空. repeat constructor.
  - rewrite 并入之幂. apply 二元并对有限集封闭; trivial.
    now apply 函数式替代对有限集封闭.
Qed.

Lemma HF是幂集封闭类 a : HF a → HF 𝒫 a.
Proof.
  intros [x Fa sub]. split.
  - now apply 幂集对有限集封闭.
  - intros y Y%幂集. constructor. eapply 子集对有限集封闭; eauto. auto.
Qed.

Fact HF是封闭类 : 封闭类 HF.
Proof.
  split.
  - apply HF是成员封闭类.
  - apply HF是空集封闭类.
  - apply HF是并集封闭类.
  - apply HF是幂集封闭类.
  - apply HF是替代封闭类.
Qed.

End HereditarilyFinite.
