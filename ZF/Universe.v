(** Coq coding by choukh, May 2022 **)

From ZF Require Import Basic Hierarchy.

(** 宇宙 **)
Section Universe.

(* 𝓜 ⊨ ZF *)
Context {𝓜 : ZF}.
Implicit Type A a b x y z : 𝓜.
Implicit Type P Q : 𝓜 → Prop.
Implicit Type R : 𝓜 → 𝓜 → Prop.

Definition 宇宙 u := ∃ P, 封闭类 P ∧ 集化 P u.

Lemma 宇宙对空集封闭 : 宇宙 ⊑ 空集封闭.
Proof. intros u [P [C S]]. apply S. apply C. Qed.

Lemma 宇宙对并集封闭 : 宇宙 ⊑ 并集封闭.
Proof. intros u [P [C S]] x xu. apply S in xu. apply S. now apply C. Qed.

Lemma 宇宙对幂集封闭 : 宇宙 ⊑ 幂集封闭.
Proof. intros u [P [C S]] x xu. apply S in xu. apply S. now apply C. Qed.

Lemma 宇宙对替代封闭 : 宇宙 ⊑ 替代封闭.
Proof.
  intros u [P [C S]] R x FR H xu. apply S in xu. apply S.
  apply C; auto. intros a b Rab ax. apply S. eapply H; eauto.
Qed.

(* 对成员关系封闭 *)
Lemma 宇宙传递 : 宇宙 ⊑ 传递.
Proof.
  intros u [P [C S]] x y xy yu. apply S in yu.
  apply S. eapply C; eauto.
Qed.

(* 对子集关系封闭 *)
Lemma 宇宙膨胀 : 宇宙 ⊑ 膨胀.
Proof.
  intros u U x y xy yu. apply (宇宙传递 U) with (z := 𝒫 y).
  - now apply 幂集.
  - now apply 宇宙对幂集封闭.
Qed.

Remark 宇宙类化 u : 宇宙 u → 封闭类 (λ x, x ∈ u).
Proof.
  intros U. split.
  - intros x y xy yu. eapply 宇宙传递; eauto.
  - now apply 宇宙对空集封闭.
  - now apply 宇宙对并集封闭.
  - now apply 宇宙对幂集封闭.
  - intros R A FR. now apply 宇宙对替代封闭.
Qed.

Lemma 宇宙对秩封闭 x u : 宇宙 u → x ∈ u → ρ x ∈ u.
Proof.
  intros U xu. induction (正则 x) as [x _ IH].
  rewrite ρ等于ρ'. apply 宇宙对并集封闭; auto.
  repeat apply 宇宙对替代封闭; auto; try congruence.
  - intros a b <- [y [yx <-]]%函数式替代.
    apply 宇宙对幂集封闭; auto.
    apply IH; auto. eapply 宇宙传递; eauto.
  - intros a b <- ax. apply IH; auto. eapply 宇宙传递; eauto.
Qed.

Lemma 宇宙是层 : 宇宙 ⊑ 层.
Proof.
  intros u U. enough (⋃ (u ∩ₚ 层) = u) as <-.
  { constructor. now intros x H%分离. }
  apply 外延.
  - intros x [y [xy [yu _]%分离]]%并集. eapply 宇宙传递; eauto.
  - intros x xu. apply 并集. exists (𝒫 (ρ x)). split.
    + apply 幂集, ρ规范.
    + apply 分离. split.
      * now apply 宇宙对幂集封闭, 宇宙对秩封闭.
      * constructor. apply ρ规范.
Qed.

Theorem 宇宙等价于对替代封闭的非空极限层 u : 宇宙 u ↔ (替代封闭 u ∧ 非空 u ∧ 极限层 u).
Proof.
  split; intros H.
  - repeat split.
    + now apply 宇宙对替代封闭.
    + exists ∅. now apply 宇宙对空集封闭.
    + now apply 宇宙是层.
    + intros x xu%宇宙对秩封闭; auto.
      apply 并集. exists (𝒫 (ρ x)). split.
      * apply 幂集, ρ规范.
      * now apply 宇宙对幂集封闭.
  - destruct H as [rc [ne [uS sub]]].
    exists (λ x, x ∈ u). split. 2:easy. split.
    + intros x y xy yu. eapply 层传递; eauto.
    + now apply 非空层对空集封闭.
    + now apply 极限层对并集封闭.
    + now apply 极限层对幂集封闭.
    + apply rc.
Qed.

End Universe.

(** 宇宙等级 **)
Section UniverseLevel.
Implicit Type 𝓜 : ZF.

(* x中至少有n个宇宙 *)
Fixpoint 等级 {𝓜} n x := match n with
  | O => True
  | S n => ∃ u ∈ x, 宇宙 u ∧ 等级 n u
end.

(* 模型中正好有n个宇宙 *)
Definition ZFₙ n 𝓜 := (∃ x, 等级 n x) ∧ (¬ ∃ x, 等级 (S n) x).

(* 模型中至少有ω个宇宙 *)
Definition ZFω 𝓜 := ∀ n, ∃ x, 等级 n x.

Lemma 等级O {𝓜} : ∃ x, 等级 0 x.
Proof. now exists ∅. Qed.

Lemma 等级S {𝓜} n : (∃ u ∈ₚ 宇宙, 等级 n u) ↔ (∃ x, 等级 (S n) x).
Proof.
  split.
  - intros [u [U H]]. exists {u,}. exists u. split. now apply 单集. easy.
  - intros [x [u [ux [U H]]]]. eauto.
Qed.

Lemma ZFₙO 𝓜 : ZFₙ 0 𝓜 ↔ ¬ ∃ u, 宇宙 u.
Proof.
  split.
  - intros [_ H] [u U]. apply H. apply 等级S. now exists u.
  - intros H. split. apply 等级O. intros H1%等级S. firstorder.
Qed.

Lemma ZFₙS 𝓜 n : ZFₙ (S n) 𝓜 ↔ ∃ u ∈ₚ 宇宙, 等级 n u ∧ ¬ ∃ x, 等级 (S (S n)) x.
Proof.
  split.
  - intros [[u [uU Hu]]%等级S HSS]. eauto.
  - intros [u [uU [Hu HS]]].
    split; trivial. apply 等级S. eauto.
Qed.

End UniverseLevel.
