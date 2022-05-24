(** Coq coding by choukh, May 2022 **)

Require Import Lite.Basic.

(*** 内模型 ***)
Section InnerModel.

(* 𝓜 ⊨ ZF *)
Variable 𝓜 : ZF.

(* 𝓜上的类 *)
Variable P : 𝓜 → Prop.

Class 封闭传递类 : Prop := {
  传递类 : ∀ x y, x ∈ y → y ∈ₚ P → x ∈ₚ P;
  空集封闭 : ∅ ∈ₚ P;
  并集封闭 : ∀ x, x ∈ₚ P → ⋃ x ∈ₚ P;
  幂集封闭 : ∀ x, x ∈ₚ P → 𝒫 x ∈ₚ P;
  替代封闭 : ∀ R A, 函数性 R → 
    (∀ x y, R x y → x ∈ A → y ∈ₚ P) → A ∈ₚ P → R @ A ∈ₚ P
}.

Hypothesis P为封闭传递类 : 封闭传递类.

(* 类的类型化 *)
Definition ℙ : Type := {x | x ∈ₚ P}.

(* 类P中关系R到𝓜的嵌入 *)
Definition 嵌入 (R : ℙ → ℙ → Prop) : 𝓜 → 𝓜 → Prop :=
  λ x y, ∃ (xP : x ∈ₚ P) (yP : y ∈ₚ P), R (exist P x xP) (exist P y yP).

Lemma 函数性嵌入 R : 函数性 R → 函数性 (嵌入 R).
Proof.
  intros Fun x y z [xP [yP RXY]] [xP'[Pz RXZ]].
  eapply eq_sig_fst. eapply Fun. apply RXY.
  erewrite subset_eq_compat. apply RXZ. easy.
Qed.

(* ⋃ {x ∊ { ⌜R⌝ @ A } | 函数性 R} *)
Definition 替代嵌入 R A := ⋃ ([嵌入 R @ A] ∩ₚ (λ _, 函数性 R)).

Lemma 替代嵌入_函数性 R A : 函数性 R → 替代嵌入 R A = 嵌入 R @ A.
Proof. intros Fun. unfold 替代嵌入. now rewrite 全分离, 并单. Qed.

Lemma 替代嵌入_非函数性 R A : ¬ 函数性 R → 替代嵌入 R A = ∅.
Proof. intros nFun. unfold 替代嵌入. now rewrite 未分离, 并空. Qed.

Definition 子结构 : ZF结构.
  apply (Build_ZF结构) with (集 := ℙ).
  - intros [x _] [y _]. apply (x ∈ y).
  - exists ∅. apply 空集封闭.
  - intros [x xP]. exists (⋃ x). now apply 并集封闭.
  - intros [x xP]. exists (𝒫 x). now apply 幂集封闭.
  - intros R [A AP]. exists (替代嵌入 R A). 排中 (函数性 R).
    + rewrite 替代嵌入_函数性; auto.
      apply 替代封闭; auto. apply 函数性嵌入; auto.
      now intros x y [_ [yP _]] _.
    + rewrite 替代嵌入_非函数性; auto. now apply 空集封闭.
Defined.

(* 内模型 ⊨ ZF *)
Theorem 内模型 : ZF.
Proof.
  apply (Build_ZF) with (结构 := 子结构).
  - intros [x xP] [y yP] XY YX.
    enough (x = y). subst y. erewrite subset_eq_compat; reflexivity.
    apply 外延.
    + intros z zx. exact (XY (exist P z (传递类 zx xP)) zx).
    + intros z zy. exact (YX (exist P z (传递类 zy yP)) zy).
  - intros [x xP] X0. eapply 空集. apply X0.
  - intros [x xP] [a aP]. split; intros H.
    + apply (并集 x a) in H as [y [xy ya]]. now exists (exist P y (传递类 ya aP)).
    + apply (并集 x a). destruct H as [[y yP] XYA]. now exists y.
  - intros [x xP] [a aP]. split; intros H.
    + apply (幂集 x a) in H. intros [y yP] YX. apply H, YX.
    + apply (幂集 x a). intros y yx. exact (H (exist P y (传递类 yx xP)) yx).
  - intros R [a aP] Fun [y yP]. split; intros H.
    + apply 并集 in H. rewrite 全分离 in H; auto.
      apply 并集 in H. rewrite 并单 in H.
      apply 替代 in H as [x[xa[xP[yP' RXY]]]]. 2: now apply 函数性嵌入.
      exists (exist P x (传递类 xa aP)).
      replace (传递类 xa aP) with xP. replace yP with yP'. now split.
      apply proof_irrelevance. apply proof_irrelevance.
    + apply 并集. rewrite 全分离; auto.
      apply 并集. rewrite 并单. destruct H as [[x xP][XA RXY]].
      apply 替代. now apply 函数性嵌入. exists x.
      split. apply XA. exists xP, yP. apply RXY.
  - intros [x xP]. induction (正则 x) as [x _ IH].
    constructor. intros [y yP] Y. apply IH. apply Y.
Qed.

End InnerModel.
