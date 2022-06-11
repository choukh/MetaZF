(** Coq coding by choukh, May 2022 **)

Require Import ZF.Basic Hierarchy.
Require Import Universe InnerModel.

(** 极小模型 **)

Lemma 内模型的宇宙是原模型的宇宙 {𝓜 : ZF} {P : 𝓜 → Prop} {PC : 封闭类 P}
  (U : 内模型 PC) : 宇宙 U → 宇宙 (proj1_sig U).
Proof.
  intros UU. destruct U as [u uP]. set (exist P u uP : 内模型 PC) as U.
  exists (λ x, x ∈ u). split. 2:easy. split.
  - intros x y xy yu.
    assert (yP: y ∈ₚ P). eapply 成员封闭类; eauto.
    assert (xP: x ∈ₚ P). eapply 成员封闭类; eauto.
    set (exist P x xP : 内模型 PC) as X.
    set (exist P y yP : 内模型 PC) as Y.
    assert (XY: X ∈ Y). apply xy.
    assert (YU: Y ∈ U). apply yu.
    assert (XU: X ∈ U). eapply 宇宙传递; eauto. apply XU.
  - assert (∅ ∈ U). apply (宇宙对空集封闭 UU). apply H.
  - intros x xu.
    assert (xP: x ∈ₚ P). eapply 成员封闭类; eauto.
    set (exist P x xP : 内模型 PC) as X.
    assert (⋃ X ∈ U). now apply 宇宙对并集封闭. apply H.
  - intros x xu.
    assert (xP: x ∈ₚ P). eapply 成员封闭类; eauto.
    set (exist P x xP : 内模型 PC) as X.
    assert (𝒫 X ∈ U). now apply 宇宙对幂集封闭. apply H.
  - intros r a Fr rc au.
    set (@投影 𝓜 P r : 内模型 PC → 内模型 PC → Prop) as R.
    assert (FR: 函数性 R). now apply 函数性投影.
    enough (r @ a = 替代嵌入 R a) as ->.
    + assert (aP: a ∈ₚ P). eapply 成员封闭类; eauto.
      set (exist P a aP : 内模型 PC) as A.
      enough (R @ A ∈ U). apply H. apply 宇宙对替代封闭; auto.
      intros [x xP] [y yP] RXY XA. eapply rc. apply RXY. apply XA.
    + rewrite 替代嵌入_函数性; auto.
      apply 外延; intros y [x [xa rxy]]%替代; auto. 3: now apply 嵌入的函数性.
      * apply 替代. apply 嵌入的函数性; auto. exists x. split; auto.
        assert (aP: a ∈ₚ P). eapply 成员封闭类; eauto.
        assert (xP: x ∈ₚ P). eapply 成员封闭类; eauto.
        assert (yP: y ∈ₚ P). eapply 成员封闭类; eauto.
        exists xP, yP. apply rxy.
      * apply 替代. auto. exists x. split; auto.
        destruct rxy as [xP [yP RXY]]. apply RXY.
Qed.

Theorem 任意模型存在极小内模型 (𝓜 : ZF) :
  ∃ (P : 𝓜 → Prop) (PC : 封闭类 P), ZF₀ (内模型 PC).
Proof.
  排中 (∃ u, 宇宙 u) as [[u uU]|H].
  - apply 宇宙是层 in uU as uS.
    destruct (层良基 uS uU) as [v [[vS [p [pc s]]] min]]. exists p, pc.
    intros [[x xp] XU]. apply 内模型的宇宙是原模型的宇宙 in XU.
    apply (无循环1 (x:=x)). apply min; auto using 宇宙是层. now apply s.
  - exists (λ _, True). assert (c : 封闭类 (λ _, True)) by firstorder.
    exists c. intros [[u true] U]. apply H. exists u.
    apply 内模型的宇宙是原模型的宇宙 in U. apply U.
Qed.
