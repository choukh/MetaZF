(** Coq coding by choukh, May 2022 **)

Require Import Basic.

(*** 内模型 ***)
Section InnerModel.

Context {𝓜} {满足ZF : ZF 𝓜}.

(* 𝓜上的类 *)
Variable P : 𝓜 → Prop.

Class 对ZF封闭 : Prop := {
  传递类 : ∀ x y, x ∈ y → y ∈ₚ P → x ∈ₚ P;
  含空集 : P ∅;
  并封闭 : ∀ x, P x → P (⋃ x);
  幂封闭 : ∀ x, P x → P (𝒫 x);
  替代封闭 : ∀ R A, 函数性 R → 
    (∀ x y, R x y → x ∈ A → P y) → P A → P (R @ A)
}.

Hypothesis P对ZF封闭 : 对ZF封闭.

(* 类的类型化 *)
Definition 𝐏 : Type := {x | P x}.

(* 类P中关系R到𝓜的嵌入 *)
Definition 嵌入 (R : 𝐏 → 𝐏 → Prop) : 𝓜 → 𝓜 → Prop :=
  λ x y, ∃ (Px : P x) (Py : P y), R (exist P x Px) (exist P y Py).

Lemma 函数性R嵌入 R : 函数性 R → 函数性 (嵌入 R).
Proof.
  intros Fun x y z [Px [Py RXY]] [Px'[Pz RXZ]].
  eapply eq_sig_fst. eapply Fun. apply RXY.
  erewrite subset_eq_compat. apply RXZ. easy.
Qed.

(* ⋃ {x ∊ {{(嵌入 R) x | x ∊ A}} | 函数性 R} *)
Definition 替代嵌入 R A := ⋃ ([嵌入 R @ A] ∩ (λ _, 函数性 R)).

Lemma 替代嵌入_函数性 R A : 函数性 R → 替代嵌入 R A = 嵌入 R @ A.
Proof. intros Fun. unfold 替代嵌入. now rewrite 全分离, 并单. Qed.

Lemma 替代嵌入_非函数性 R A : ¬ 函数性 R → 替代嵌入 R A = ∅.
Proof. intros nFun. unfold 替代嵌入. now rewrite 未分离, 并空. Qed.

Definition 内模型 : ZF结构.
  apply (Build_ZF结构) with (集 := 𝐏).
  - intros [x _] [y _]. apply (x ∈ y).
  - exists ∅. apply 含空集.
  - intros [x Px]. exists (⋃ x). now apply 并封闭.
  - intros [x Px]. exists (𝒫 x). now apply 幂封闭.
  - intros R [A PA]. exists (替代嵌入 R A). 排中 (函数性 R).
    + rewrite 替代嵌入_函数性; auto.
      apply 替代封闭; auto. apply 函数性R嵌入; auto.
      now intros x y [_ [Py _]] _.
  + rewrite 替代嵌入_非函数性; auto. now apply 含空集.
Defined.

(* 内模型 ⊨ ZF *)
Theorem 内模型_ZF : ZF 内模型.
Proof.
  split.
  - intros [x Px] [y Py] XY YX.
    enough (x = y). subst y. erewrite subset_eq_compat; reflexivity.
    apply 外延; intros z Hz.
    + exact (XY (exist P z (传递类 Hz Px)) Hz).
    + exact (YX (exist P z (传递类 Hz Py)) Hz).
  - intros [] H. eapply 空集. apply H.
  - intros [x Px] [A PA]. split; intros H.
    + apply (并集 x A) in H as [y [xy yA]]. now exists (exist P y (传递类 yA PA)).
    + apply (并集 x A). destruct H as [[y Py] Y]. now exists y.
  - intros [x Px] [A PA]. split; intros H.
    + apply (幂集 x A) in H. intros [y Py] YX. apply H, YX.
    + apply (幂集 x A). intros y yx.
      exact (H (exist P y (传递类 yx Px)) yx).
  - intros R [A PA] Fun [y Py]. split; intros H.
    + apply 并集 in H. rewrite 全分离 in H; auto.
      apply 并集 in H. rewrite 并单 in H.
      apply 替代 in H as [x[xA[Px[Py' RXY]]]]. 2: now apply 函数性R嵌入.
      exists (exist P x (传递类 xA PA)).
      replace (传递类 xA PA) with Px. replace Py with Py'. now split.
      apply proof_irrelevance. apply proof_irrelevance.
    + apply 并集. rewrite 全分离; auto.
      apply 并集. rewrite 并单. destruct H as [[x Px][XY RXY]].
      apply 替代. now apply 函数性R嵌入. exists x. split. apply XY.
      exists Px, Py. apply RXY.
  - intros [x Px]. induction (正则 x) as [x _ H].
    constructor. intros [y Py] Y. apply H. apply Y.
Qed.

End InnerModel.
