(** Coq coding by choukh, May 2022 **)

Require Import Lite.Basic.

(*** 内模型 ***)
Section InnerModel.

(* 𝓜 ⊨ ZF *)
Context {𝓜 : ZF}.

(* 𝓜上的类 *)
Variable P : 𝓜 → Prop.

Hypothesis P为封闭类 : 封闭类 P.

(* 类的类型化 *)
Definition ℙ : Type := {x | x ∈ₚ P}.

(* 类P中关系R到𝓜的嵌入 *)
Definition 嵌入 (R : ℙ → ℙ → Prop) : 𝓜 → 𝓜 → Prop :=
  λ x y, ∃ (xP : x ∈ₚ P) (yP : y ∈ₚ P), R (exist P x xP) (exist P y yP).
Notation "⌜ R ⌝" := (嵌入 R) (format "⌜ R ⌝").

(* 𝓜中关系R到类P的投影 *)
Definition 投影 (R : 𝓜 → 𝓜 → Prop) : ℙ → ℙ → Prop :=
  λ X Y : {x | P x}, R (proj1_sig X) (proj1_sig Y).

Lemma 嵌入有函数性 R : 函数性 R → 函数性 ⌜R⌝.
Proof.
  intros FR x y z [xP [yP RXY]] [xP'[Pz RXZ]].
  eapply eq_sig_fst. eapply FR. apply RXY.
  erewrite subset_eq_compat. apply RXZ. easy.
Qed.

Lemma 函数性投影 R : 函数性 R → 函数性 (投影 R).
Proof.
  intros FR [x xP] [y yP] [z zP] RXY RYZ.
  unfold 投影 in *; simpl in *.
  apply subset_eq_compat. eapply FR; eauto.
Qed.

(* ⋃ {x ∊ { ⌜R⌝ @ A } | 函数性 R} *)
Definition 替代嵌入 R A := ⋃ ([⌜R⌝ @ A] ∩ₚ (λ _, 函数性 R)).
Notation "R ⌜@⌝ A" := (替代嵌入 R A) (at level 70).

Lemma 替代嵌入_函数性 R A : 函数性 R → R ⌜@⌝ A = ⌜R⌝ @ A.
Proof. intros FR. unfold 替代嵌入. now rewrite 全分离, 并单. Qed.

Lemma 替代嵌入_非函数性 R A : ¬ 函数性 R → R ⌜@⌝ A = ∅.
Proof. intros nFR. unfold 替代嵌入. now rewrite 未分离, 并空. Qed.

Definition 子结构 : ZF结构.
  apply (Build_ZF结构) with (集 := ℙ).
  - intros [x _] [y _]. apply (x ∈ y).
  - exists ∅. apply 空集封闭类.
  - intros [x xP]. exists (⋃ x). now apply 并集封闭类.
  - intros [x xP]. exists (𝒫 x). now apply 幂集封闭类.
  - intros R [A AP]. exists (R ⌜@⌝ A). 排中 (函数性 R).
    + rewrite 替代嵌入_函数性; auto.
      apply 替代封闭类; auto. apply 嵌入有函数性; auto.
      now intros x y [_ [yP _]] _.
    + rewrite 替代嵌入_非函数性; auto. now apply 空集封闭类.
Defined.

(* 内模型 ⊨ ZF *)
Definition 内模型 : ZF.
Proof.
  apply (Build_ZF) with (结构 := 子结构).
  - intros [x xP] [y yP] XY YX.
    enough (x = y). subst y. erewrite subset_eq_compat; reflexivity.
    apply 外延.
    + intros z zx. exact (XY (exist P z (成员封闭类 zx xP)) zx).
    + intros z zy. exact (YX (exist P z (成员封闭类 zy yP)) zy).
  - intros [x xP] X0. eapply 空集. apply X0.
  - intros [x xP] [a aP]. split; intros H.
    + apply (并集 x a) in H as [y [xy ya]]. now exists (exist P y (成员封闭类 ya aP)).
    + apply (并集 x a). destruct H as [[y yP] XYA]. now exists y.
  - intros [x xP] [a aP]. split; intros H.
    + apply (幂集 x a) in H. intros [y yP] YX. apply H, YX.
    + apply (幂集 x a). intros y yx. exact (H (exist P y (成员封闭类 yx xP)) yx).
  - intros R [a aP] FR [y yP]. split; intros H.
    + apply 并集 in H. rewrite 全分离 in H; auto.
      apply 并集 in H. rewrite 并单 in H.
      apply 替代 in H as [x[xa[xP[yP' RXY]]]]. 2: now apply 嵌入有函数性.
      exists (exist P x (成员封闭类 xa aP)).
      replace (成员封闭类 xa aP) with xP. replace yP with yP'. now split.
      apply proof_irrelevance. apply proof_irrelevance.
    + apply 并集. rewrite 全分离; auto.
      apply 并集. rewrite 并单. destruct H as [[x xP][XA RXY]].
      apply 替代. now apply 嵌入有函数性. exists x.
      split. apply XA. exists xP, yP. apply RXY.
  - intros [x xP]. induction (正则 x) as [x _ IH].
    constructor. intros [y yP] Y. apply IH. apply Y.
Defined.

End InnerModel.

Notation "R ⌜@⌝ A" := (替代嵌入 R A) (at level 70) : zf_scope.
