(** Coq coding by choukh, July 2022 **)

From ZF Require Import Basic Hierarchy Universe Finiteness.

Section 宇宙蕴含无穷.
Context {𝓜 : ZF}.

(* 存在宇宙 *)
Definition Univ := ∃ u, 宇宙 u.

Fixpoint Vₙ n :=
  match n with
  | O => ∅
  | S m => 𝒫 (Vₙ m)
  end.

(* V_<ω 类 *)
Definition 有穷层 x := ∃ n, x = Vₙ n.
(* 无穷公理变体: V_<ω 是集合 *)
Definition Infⱽ := 可集化 有穷层.

Lemma 宇宙蕴含无穷 : Univ → Infⱽ.
Proof.
  intros [u U]. exists (u ∩ₚ 有穷层).
  intros x. split; intros H.
  - now apply 分离 in H.
  - destruct H as [n ->]. apply 分离. split. 2:now exists n.
    induction n. now apply 宇宙对空集封闭. now apply 宇宙对幂集封闭.
Qed.

End 宇宙蕴含无穷.

Section 无穷蕴含宇宙.
Context {𝓜 : ZF}.

Hypothesis inf : Infⱽ.
Definition Vltω := proj1_sig (集化大消除 inf).
(* Vltω =ₚ 有穷层 *)
Definition 无穷 := proj2_sig (集化大消除 inf).
Definition Vω := ⋃ Vltω.

Lemma Vω成员属某Vn x : x ∈ Vω → ∃ n, x ∈ Vₙ n.
Proof.
  intros [y [xy yV]] % 并集.
  apply 无穷 in yV as [n ->]. now exists n.
Qed.

Lemma Vn是层 n : Vₙ n ∈ₚ 层.
Proof. induction n. apply 空集层. now constructor. Qed.

(* sidetrack *)
Section Omega.

Definition 归纳集 A := ∅ ∈ A ∧ ∀ a ∈ A, a⁺ ∈ A.
Definition 自然数 n := ∀ A, 归纳集 A → n ∈ A.
Definition ω := Vω ∩ₚ 自然数.

Lemma Vω是归纳集 : 归纳集 Vω.
Proof.
  split.
  - apply 并集. exists (Vₙ 1). split.
    + now apply 幂集.
    + apply 无穷. now exists 1.
  - intros. apply Vω成员属某Vn in H as [n an].
    apply 并集. exists (Vₙ (S n)). split.
    + simpl. apply 幂集. intros x xa. apply 后继 in xa as [].
      * congruence.
      * apply 层传递 with a; auto. apply Vn是层.
    + apply 无穷. now exists (S n).
Qed.

Fact ω里有且仅有自然数 : ∀ n, n ∈ ω ↔ 自然数 n.
Proof.
  split; intros.
  - now apply 分离 in H.
  - apply 分离. split; auto. apply H. apply Vω是归纳集.
Qed.

End Omega.

Lemma Vn属Vω n : Vₙ n ∈ Vω.
Proof.
  apply 并集. exists (Vₙ (S n)). split.
  - now apply 幂集.
  - apply 无穷. now exists (S n).
Qed.

Lemma Vω对空集封闭 : ∅ ∈ Vω.
Proof. replace ∅ with (Vₙ 0) by reflexivity. apply Vn属Vω. Qed.

Lemma Vω是层 : Vω ∈ₚ 层.
Proof.
  constructor. intros y Y.
  apply 无穷 in Y as [n ->]. apply Vn是层.
Qed.

Lemma Vω之并 : Vω ⊆ ⋃ Vω.
Proof.
  intros x X. apply Vω成员属某Vn in X as [n X].
  apply 并集. exists (Vₙ n). split; trivial. apply Vn属Vω.
Qed.

Lemma Vω是极限层 : Vω ∈ₚ 极限层.
Proof. split. apply Vω是层. apply Vω之并. Qed.

(** Vω集化HF **)

Notation HF := 遗传有穷集.

Lemma Vn是遗传有穷集 n : HF (Vₙ n).
Proof.
  induction n as [|n IH].
  - apply HF是空集封闭类.
  - apply HF是幂集封闭类. apply IH.
Qed.

Lemma 非空有穷链封闭 x : 非空 x → 有穷集 x → 链 x → ⋃ x ∈ x.
Proof.
  induction 2 as [|x y Fx IH]. destruct H. zf.
  intros Ch. 排中 (非空 y) as [NEy| ->%非非空].
  - assert (IH': ⋃ y ∈ y). {
      apply IH; trivial. eapply 链传递. 2:apply Ch.
      intros z zy. apply 并入. auto.
    }
    assert (X: x ∈ x ⨮ y). apply 并入. auto.
    assert (Y: ⋃ y ∈ x ⨮ y). apply 并入. auto.
    destruct (Ch _ X _ Y) as [XY|YX]; apply 并入.
    + right. replace (⋃ (x ⨮ y)) with (⋃ y). trivial. apply 外延.
      * apply 并得父集, 并入. auto.
      * apply 并得子集. intros z [->|Z]%并入. zf. now apply 并得父集.
    + left. apply 外延.
      * apply 并得子集. intros z [->|Z]%并入. zf.
        intros w wz. apply YX, 并集. eauto.
      * apply 并得父集. apply 并入. auto.
  - apply 并入. left. now rewrite 并入空, 并单.
Qed.

Lemma 遗传有穷集的秩层在Vω里 x : HF x → ρ x ∈ Vω.
Proof.
  induction 1 as [x Fx sub IH].
  排中 (非空 x) as [[y yx]| ->%非非空].
  - assert (ρ x ∈ 𝒫[ρ[x]]). {
      rewrite ρ等于ρ'. apply 非空有穷链封闭.
      + exists (𝒫 (ρ y)). now apply 函数式替代2I.
      + now repeat apply 有穷集对函数式替代封闭.
      + intros a [a' [A ->]]%函数式替代2E b [b' [B ->]]%函数式替代2E.
        apply 层线序; constructor; apply ρ规范.
    }
    apply 函数式替代2E in H as [z [zx ->]].
    apply 极限层对幂集封闭. apply Vω是极限层. now apply IH.
  - replace (ρ ∅) with ∅. apply Vω对空集封闭. now rewrite ρ_0.
Qed.

Lemma Vω集化HF : Vω =ₚ HF.
Proof.
  intros x. split; intros H.
  - apply Vω成员属某Vn in H as [n H].
    destruct (Vn是遗传有穷集 n) as [y _ sub]. now apply sub.
  - apply 层膨胀 with (ρ x). apply Vω是层.
    apply ρ规范. now apply 遗传有穷集的秩层在Vω里.
Qed.

(** Vω是宇宙 **)

Lemma Vω对替代封闭 : 替代封闭 Vω.
Proof.
  intros R a Fun H A. apply Vω集化HF. apply HF是替代封闭类.
  trivial. 2: now apply Vω集化HF.
  intros x y Rxy xa. apply Vω集化HF. eapply H; eauto.
Qed.

Lemma Vω是宇宙 : Vω ∈ₚ 宇宙.
Proof.
  apply 宇宙等价于对替代封闭的非空极限层. split3.
  apply Vω对替代封闭. exists ∅. apply Vω对空集封闭. apply Vω是极限层.
Qed.

Lemma 无穷蕴含宇宙 : Univ.
Proof. exists Vω. apply Vω是宇宙. Qed.

(** 极小宇宙 **)

Lemma Vω不属于Vltω : Vω ∉ Vltω.
Proof.
  intros H. apply 无穷 in H as [n H].
  apply (无循环1 (x:=Vₙ n)).
  rewrite <- H at 2. apply Vn属Vω.
Qed.

Lemma Vltω非空 : 非空 Vltω.
Proof. exists ∅. apply 无穷. now exists 0. Qed.

Lemma Vltω是链 : 链 Vltω.
Proof.
  intros x [n ->]%无穷 y [m ->]%无穷.
  apply 层线序; apply Vn是层.
Qed.

Lemma Vltω是无穷集 : ¬ 有穷集 Vltω.
Proof.
  intros H. apply 非空有穷链封闭 in H.
  - now apply Vω不属于Vltω.
  - apply Vltω非空.
  - apply Vltω是链.
Qed.

Lemma 非空极限层不低于Vltω x : 非空 x → 极限层 x → Vltω ⊆ x.
Proof.
  intros H1 H2 y Y. apply 无穷 in Y as [n ->].
  induction n as [|n IH].
  - apply 非空层对空集封闭; firstorder.
  - apply 极限层对幂集封闭; trivial.
Qed.

Lemma 非空极限层是无穷集 x : 非空 x → 极限层 x → ¬ 有穷集 x.
Proof.
  intros H1 H2 H3. apply Vltω是无穷集.
  apply 有穷集对子集封闭 with x; trivial.
  apply 非空极限层不低于Vltω; trivial.
Qed.

Lemma Vn是有穷集 n : 有穷集 (Vₙ n).
Proof. induction n. constructor. now apply 有穷集对幂集封闭. Qed.

Lemma Vω只含有穷集 : Vω ⊆ₚ 有穷集.
Proof.
  intros x [n X]%Vω成员属某Vn. destruct n. simpl in X. zf.
  eapply 有穷集对子集封闭 with (Vₙ n). now apply 幂集. apply Vn是有穷集.
Qed.

Lemma 非空极限层不低于Vω x : 非空 x → 极限层 x → Vω ⊆ x.
Proof.
  intros H1 H2.
  destruct (层ϵ线序 Vω是层 (proj1 H2)); trivial.
  exfalso. eapply 非空极限层是无穷集; eauto. now apply Vω只含有穷集.
Qed.

Fact Vω是极小宇宙 u : 宇宙 u → Vω ⊆ u.
Proof. intros H%宇宙是非空极限层. apply 非空极限层不低于Vω; firstorder. Qed.

End 无穷蕴含宇宙.

Theorem 无穷公理等价于存在宇宙 (𝓜 : ZF) : Infⱽ ↔ Univ.
Proof. split. apply 无穷蕴含宇宙. apply 宇宙蕴含无穷. Qed.
