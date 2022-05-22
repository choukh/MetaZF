(** Coq coding by choukh, May 2022 **)

Require Export Meta.

(*** 基本部件 ***)
Section Basic.

Context {𝓜} {满足ZF : ZF 𝓜}.
Implicit Type A B C X Y Z a b c x y z : 𝓜.
Implicit Type P : 𝓜 → Prop.

(** 空集 **)

Lemma 空集是子集 x : ∅ ⊆ x.
Proof. intros y Hy. zf. Qed.
Hint Resolve 空集是子集 : zf.

Lemma 空集唯一 x : (∀ y, y ∉ x) → x = ∅.
Proof.
  intros H. apply 外延.
  - intros y yx. firstorder.
  - apply 空集是子集.
Qed.

Definition 非空 x := ∃ y, y ∈ x.

Lemma 非非空 x : ¬ 非空 x ↔ x = ∅.
Proof.
  split.
  - intros. apply 空集唯一. firstorder.
  - intros -> [y H]. zf.
Qed.

(** 配对 **)

Local Definition R a b := λ x y, (x = ∅ ∧ y = a) ∨ (x = 𝒫 ∅ ∧ y = b).
Definition 偶 a b := R a b @ 𝒫 𝒫 ∅.
Notation "[ a , b ]" := (偶 a b).

Definition 单 a := [a, a].
Notation "[ a ]" := (单 a).

Local Lemma 函数性R a b : 函数性 (R a b).
Proof.
  intros x y z [[]|[]] [[]|[]]; subst; auto.
  - symmetry in H1.
    apply 非非空 in H1. contradict H1. exists ∅. now apply 幂集.
  - apply 非非空 in H1. contradict H1. exists ∅. now apply 幂集.
Qed.

Lemma 配对 a b x : x ∈ [a, b] ↔ x = a ∨ x = b.
Proof.
  split; intros H.
  - apply 替代 in H as [y [_ [[_ A]|[_ A]]]]; auto. apply 函数性R.
  - apply 替代. apply 函数性R. destruct H; subst.
    + exists ∅. split. apply 幂集. zf. unfold R. now left.
    + exists (𝒫 ∅). split. apply 幂集. zf. unfold R. now right.
Qed.

Lemma 单集 x a : x ∈ [a] ↔ x = a.
Proof. unfold 单. rewrite 配对. firstorder. Qed.

(** 并集 **)

Notation 上界 A U := (∀ x ∈ A, x ⊆ U).
Notation 上确界 A U := (上界 A U ∧ ∀ V, 上界 A V → U ⊆ V).

Lemma 并得父集 x A : x ∈ A → x ⊆ ⋃ A.
Proof. intros xy z zx. apply 并集. eauto. Qed.

Lemma 并得子集 A U : 上界 A U → ⋃ A ⊆ U.
Proof. intros upb x [y [xy yA]] % 并集. now apply (upb y). Qed.

Hint Resolve 并得父集 并得子集 : zf.

Lemma 并即上确界 A U : ⋃ A = U ↔ 上确界 A U.
Proof.
  split.
  - intros <-. split.
    + intros x. apply 并得父集.
    + apply 并得子集.
  - intros [upb H]. apply 外延.
    + apply 并得子集, upb.
    + apply H. intros x. apply 并得父集.
Qed.

Lemma 并空 : ⋃ ∅ = ∅.
Proof. apply 并即上确界. zf. Qed.

Lemma 并单 x : ⋃ [x] = x.
Proof.
  apply 外延; intros y H.
  - apply 并集 in H as [z [zy yx%单集]]. congruence.
  - apply 并集. exists x. split. apply H. now apply 单集.
Qed.

Lemma 并传递 x : x ⊆ₚ 传递 → 传递 (⋃ x).
Proof.
  intros tr a [b [ab bx]]%并集 y ya. apply 并集.
  exists b. split; auto. eapply tr; eauto.
Qed.

(** 幂集 **)

Lemma 幂传递 x : x ∈ₚ 传递 → 传递 (𝒫 x).
Proof.
  intros tr y yp z zy.
  apply 幂集. apply 幂集 in yp. auto.
Qed.

Lemma 幂单调 x y : x ⊆ y → 𝒫 x ⊆ 𝒫 y.
Proof. intros xy z zp. apply 幂集. apply 幂集 in zp. zf. Qed.

(** 分离 **)

Definition 分 A P := (λ x y, P x ∧ x = y) @ A.
Notation "A ∩ P" := (分 A P) (at level 60).

Lemma 分离 P A x : x ∈ A ∩ P ↔ x ∈ A ∧ P x.
Proof.
  intros. unfold 分. rewrite 替代.
  - split.
    + intros [y [yA [Py <-]]]. auto.
    + intros [xA Px]. eauto.
  - cbv. intuition congruence.
Qed.

Lemma 分离为子集 A P : A ∩ P ⊆ A.
Proof. now intros y [yA _]%分离. Qed.

Lemma 全分离 P A : (∀ x, P x) → A ∩ P = A.
Proof.
  intros H. apply 外延. apply 分离为子集.
  intros y yA. apply 分离. now split.
Qed.

Lemma 未分离 P A : (∀ x, ¬ P x) → A ∩ P = ∅.
Proof.
  intros H. apply 空集唯一.
  intros y [_ Py]%分离. apply (H y Py).
Qed.

(** 替代 **)

Definition F替 F A := (λ x y, F x = y) @ A.
Notation "F [ A ]" := (F替 F A) (at level 7, format "F [ A ]").

Lemma 函数式替代 F A y : y ∈ F[A] ↔ ∃ x ∈ A, F x = y.
Proof.
  unfold F替. rewrite 替代. reflexivity.
  cbv. congruence.
Qed.

End Basic.

Notation "[ a , b ]" := (偶 a b) : zf_scope.
Notation "[ a ]" := (单 a) : zf_scope.
Notation "F [ A ]" := (F替 F A) (at level 7, format "F [ A ]") : zf_scope.
Notation "A ∩ P" := (分 A P) (at level 60) : zf_scope.

Global Hint Resolve 空集是子集 : zf.
