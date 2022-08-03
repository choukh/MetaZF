(** Coq coding by choukh, May 2022 **)

Require Export Classical ProofIrrelevance.
From ZF Require Export ZF.

(** 经典逻辑 **)

Tactic Notation "排中" constr(P) :=
  destruct (classic P).
Tactic Notation "排中" constr(P) "as" simple_intropattern(L) :=
  destruct (classic P) as L.

Ltac 反证 := match goal with
  |- ?G => destruct (classic G) as [?正设|?反设]; [assumption|exfalso]
end.

(*** 基本部件 ***)
Section Basic.
Context {𝓜 : ZF}.
Implicit Type A a b c x y z : 𝓜.
Implicit Type P Q : 𝓜 → Prop.

(** 子集 **)

Lemma 非子类 P Q : P ⋢ Q → ∃ x ∈ₚ P, x ∉ₚ Q.
Proof.
  intros ns. 反证. apply ns. intros z zx.
  反证. apply 反设. now exists z.
Qed.

Lemma 非子集 x y : x ⊈ y → ∃ z, z ∈ x ∧ z ∉ y.
Proof.
  intros ns. 反证. apply ns. intros z zx.
  反证. apply 反设. now exists z.
Qed.

(** ⊆链 **)

Definition 链 A := ∀ x y ∈ A, x ⊆ y ∨ y ⊆ x.

Lemma 链传递 x y : x ⊆ y → 链 y → 链 x.
Proof. firstorder. Qed.

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

Lemma 空集的子集 x : x ⊆ ∅ → x = ∅.
Proof. intros H. apply 空集唯一. intros y yx % H. zf. Qed.

Notation 非空 x := (∃ y, y ∈ x).

Lemma 非非空 x : ¬ 非空 x ↔ x = ∅.
Proof.
  split.
  - intros. apply 空集唯一. firstorder.
  - intros -> [y H]. zf.
Qed.

(** 配对 **)

Local Definition R a b := λ x y, (x = ∅ ∧ y = a) ∨ (x = 𝒫 ∅ ∧ y = b).
Definition 偶 a b := R a b @ 𝒫 𝒫 ∅.
Notation "{ a , b }" := (偶 a b).

Definition 单 a := {a, a}.
Notation "{ a , }" := (单 a) (format "{ a , }").

Local Lemma 函数性R a b : 函数性 (R a b).
Proof.
  intros x y z [[]|[]] [[]|[]]; subst; auto.
  - symmetry in H1.
    apply 非非空 in H1. contradict H1. exists ∅. now apply 幂集.
  - apply 非非空 in H1. contradict H1. exists ∅. now apply 幂集.
Qed.

Lemma 配对 a b x : x ∈ {a, b} ↔ x = a ∨ x = b.
Proof.
  split; intros H.
  - apply 替代 in H as [y [_ [[_ A]|[_ A]]]]; auto. apply 函数性R.
  - apply 替代. apply 函数性R. destruct H; subst.
    + exists ∅. split. apply 幂集. zf. unfold R. now left.
    + exists (𝒫 ∅). split. apply 幂集. zf. unfold R. now right.
Qed.

Lemma 单集 x a : x ∈ {a,} ↔ x = a.
Proof. unfold 单. rewrite 配对. firstorder. Qed.

Lemma 单集I x : x ∈ {x,}.
Proof. now apply 单集. Qed.
Hint Resolve 单集I : zf.

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

Lemma 并单 x : ⋃ {x,} = x.
Proof.
  apply 外延; intros y H.
  - apply 并集 in H as [z [zy yx%单集]]. congruence.
  - apply 并集. exists x. split. apply H. zf.
Qed.

Lemma 并幂 x : ⋃ (𝒫 x) = x.
Proof.
  apply 并即上确界. split.
  - now intros y yx%幂集.
  - intros y ubd. now apply ubd, 幂集.
Qed.

(** 二元并 **)

Definition 偶并 := λ A B, ⋃ {A, B}.
Notation "A ∪ B" := (偶并 A B) (at level 50).

Lemma 二元并 : ∀ x A B, x ∈ A ∪ B ↔ x ∈ A ∨ x ∈ B.
Proof.
  split; intros.
  - apply 并集 in H as [a [Ha Hx]].
    apply 配对 in Hx as []; subst; auto.
  - destruct H; eapply 并集.
    + exists A. split; auto. apply 配对. now left.
    + exists B. split; auto. apply 配对. now right.
Qed.

Lemma 左并空 x : ∅ ∪ x = x.
Proof.
  apply 外延; intros y yu.
  - apply 二元并 in yu as []; zf.
  - apply 二元并. auto.
Qed.

Lemma 二元并交换律 a b : a ∪ b = b ∪ a.
Proof.
  intros. apply 外延; intros x X;
  apply 二元并 in X as []; apply 二元并; auto.
Qed.

Lemma 二元并结合律 a b c : (a ∪ b) ∪ c = a ∪ (b ∪ c).
Proof.
  apply 外延; intros x X; apply 二元并; apply 二元并 in X as [].
  - apply 二元并 in H as []. auto. right. apply 二元并. auto.
  - right. apply 二元并. auto.
  - left. apply 二元并. auto.
  - apply 二元并 in H as []. left. apply 二元并. auto. auto.
Qed.

Lemma 并集分配律 a b : ⋃ (a ∪ b) = (⋃ a) ∪ (⋃ b).
Proof.
  intros. apply 外延; intros x X.
  - apply 并集 in X as [y [xy Y]]. apply 二元并 in Y as [];
    apply 二元并; [left|right]; eapply 并集; eauto.
  - apply 二元并 in X as []; apply 并集 in H as [y [H1 H2]];
    eapply 并集; exists y; split; auto; apply 二元并; auto.
Qed.

Definition 入 x y := {x,} ∪ y.
Notation "x ⨮ y" := (入 x y) (at level 65, right associativity).

Lemma 并入 x y z : x ∈ y ⨮ z ↔ x = y ∨ x ∈ z.
Proof.
  split; intros H.
  - apply 二元并 in H as []; auto. apply 单集 in H as ->. now left.
  - destruct H as [->|]; apply 二元并. left; zf. now right.
Qed.

Lemma 并入空 x : x ⨮ ∅ = {x,}.
Proof.
  apply 外延; intros y Y.
  - apply 并入 in Y as [->|]; zf.
  - apply 单集 in Y as ->. apply 并入. auto.
Qed.

Definition 继 := λ a, a ⨮ a.
Notation "a ⁺" := (继 a) (at level 6, format "a ⁺").

Lemma 后继 a x : x ∈ a⁺ ↔ x = a ∨ x ∈ a.
Proof. apply 并入. Qed.

Lemma 后继非空 a : a⁺ ≠ ∅.
Proof. intros H. eapply 空集. rewrite <- H. apply 后继. auto. Qed.

(** 幂集 **)

Lemma 幂单调 x y : x ⊆ y → 𝒫 x ⊆ 𝒫 y.
Proof. intros xy z zp. apply 幂集. apply 幂集 in zp. zf. Qed.

Lemma 幂并 x : x ⊆ 𝒫 ⋃ x.
Proof. intros y Hy. apply 幂集. now apply 并得父集. Qed.

(** 分离 **)

Definition 分 A P := (λ x y, P x ∧ x = y) @ A.
Notation "A ∩ₚ P" := (分 A P) (at level 60).

Lemma 分离 P A x : x ∈ A ∩ₚ P ↔ x ∈ A ∧ P x.
Proof.
  intros. unfold 分. rewrite 替代.
  - split.
    + intros [y [yA [yP <-]]]. auto.
    + intros [xA xP]. eauto.
  - cbv. intuition congruence.
Qed.

Lemma 分离为子集 A P : A ∩ₚ P ⊆ A.
Proof. now intros y [yA _]%分离. Qed.

Lemma 全分离 P A : (∀ x, P x) → A ∩ₚ P = A.
Proof.
  intros H. apply 外延. apply 分离为子集.
  intros y yA. apply 分离. now split.
Qed.

Lemma 未分离 P A : (∀ x, ¬ P x) → A ∩ₚ P = ∅.
Proof.
  intros H. apply 空集唯一.
  intros y [_ yP]%分离. apply (H y yP).
Qed.

Lemma 集的子类可集化 P x : P ⊆ₛ x → setLike P.
Proof.
  intros H. exists (x ∩ₚ P). intros z.
  rewrite 分离. intuition.
Qed.

(** 罗素集 **)

Definition 罗素 x := x ∩ₚ (λ y, y ∉ y).

Lemma 罗素集 x : 罗素 x ∉ x.
Proof.
  intros Rx. set (罗素 x ∈ 罗素 x) as RinR.
  assert (H1 : RinR → ¬ RinR). {
    unfold RinR. intros. apply 分离 in H. apply H.
  }
  assert (H2: ¬ ¬ RinR). {
    unfold RinR. intros H. apply H. now apply 分离.
  }
  auto.
Qed.

Lemma 幂集在上 x : 𝒫 x ⊈ x.
Proof.
  intros false.
  assert (罗素 x ∈ 𝒫 x). apply 幂集. apply 分离为子集.
  apply false in H. eapply 罗素集; eauto.
Qed.

(** 替代 **)

Lemma 替代空 R : 函数性 R → R @ ∅ = ∅.
Proof.
  intros H. apply 空集的子集.
  intros x [y [y0 _]] % 替代. zf. trivial.
Qed.

Definition 𝓕 R := λ x, ⋃ (R @ {x,}).

Lemma 函数化 R a b : 函数性 R → R a b → 𝓕 R a = b.
Proof.
  intros Fun Rab. apply 并即上确界. split.
  - intros x [y [->%单集 Ray]]%替代; trivial.
    enough (b = x) by congruence. eapply Fun; eauto.
  - intros x ubd. apply ubd. apply 替代; trivial.
    exists a. split; auto. apply 单集; auto.
Qed.

Definition F替 F A := (λ x y, F x = y) @ A.
Notation "F [ A ]" := (F替 F A) (at level 7, format "F [ A ]").

Lemma 函数式替代 F A y : y ∈ F[A] ↔ ∃ x ∈ A, F x = y.
Proof.
  unfold F替. rewrite 替代. reflexivity.
  cbv. congruence.
Qed.

Lemma 函数式替代2I {F G} x A : x ∈ A → F (G x) ∈ F[G[A]].
Proof.
  intros xA. apply 函数式替代. exists (G x). split; auto.
  apply 函数式替代. now exists x.
Qed.

Lemma 函数式替代2E {F G} y A : y ∈ F[G[A]] → ∃ x ∈ A, y = F (G x).
Proof. intros [z [[x [xA <-]]%函数式替代 <-]]%函数式替代. eauto. Qed.

(** 描述算子 (唯一选择) **)

Definition δ P := 𝓕 (λ _ y, P y) ∅.

Lemma δ求值 P x : P x → uniqueness P → δ P = x.
Proof. intros xP uq. apply 函数化; trivial. firstorder. Qed.

Lemma δ规范 P x : P x → uniqueness P → P (δ P).
Proof. intros xP uq. now rewrite (δ求值 xP uq). Qed.

Lemma 集化唯一 P : uniqueness (λ A, A =ₚ P).
Proof.
  intros a b H1 H2. apply 外延; intros x.
  - now intros H3 % H1 % H2.
  - now intros H3 % H2 % H1.
Qed.

Lemma 集化大消除 P : (∃ A, A =ₚ P) → Σ A, A =ₚ P.
Proof.
  intros. assert (δ (λ A, A =ₚ P) =ₚ P). {
    destruct H. eapply δ规范. eauto. apply 集化唯一.
  }
  intros. now exists (δ (λ A, A =ₚ P)).
Qed.

(** 正则 **)

Lemma 无循环1 x : x ∉ x.
Proof. intros H. induction (正则 x) as [x _ IH]. eauto. Qed.

Lemma 无循环2 x y : x ∈ y → y ∈ x → False.
Proof. revert x. induction (正则 y) as [y _ IH]. eauto. Qed.

Lemma 无循环3 x y z : x ∈ y → y ∈ z → z ∈ x → False.
Proof. revert x y. induction (正则 z) as [z _ IH]. eauto. Qed.

(** 封闭性 **)

Definition 配对封闭 x := ∀ a b ∈ x, {a, b} ∈ x.
Definition 分离封闭 x := ∀ P, ∀ y ∈ x, y ∩ₚ P ∈ x.

(** 传递集 **)

Definition 传递ₛ x := ∀ y ∈ x, y ⊆ x.
Definition 传递ᵤ x := ⋃ x ⊆ x.
Definition 传递ₚ x := x ⊆ 𝒫 x.

Lemma 传递_子集表述 x : 传递 x ↔ 传递ₛ x.
Proof. split; firstorder. Qed.

Lemma 传递_并集表述 x : 传递 x ↔ 传递ᵤ x.
Proof.
  split.
  - intros tr y Y. apply 并集 in Y as [z [yz zx]]. eapply tr; eauto.
  - intros sub y z yz zx. apply sub. apply 并集. eauto.
Qed.

Lemma 传递_幂集表述 x : 传递 x ↔ 传递ₚ x.
Proof.
  split.
  - intros tr y yx. apply 幂集. intros z zy. eapply tr; eauto.
  - intros sub y z yz zx. apply sub in zx. eapply 幂集; eauto.
Qed.

Lemma 传递_后继表述 x : 传递 x ↔ ⋃ x⁺ = x.
Proof.
  rewrite 传递_并集表述.
  unfold 继, 入. rewrite 并集分配律, 并单. split; intros.
  - apply 外延; intros y yx.
    + apply 二元并 in yx as []; auto.
    + apply 二元并; auto.
  - intros y yx. rewrite <- H. apply 二元并. auto.
Qed.

(* 传递集族之并是传递集 *)
Lemma 并传递 x : x ⊆ₚ 传递 → ⋃ x ∈ₚ 传递.
Proof.
  intros tr a y ya [b [ab bx]]%并集. apply 并集.
  exists b. split; auto. eapply tr; eauto.
Qed.

(* 传递集的幂集仍是传递集 *)
Lemma 幂传递 x : x ∈ₚ 传递 → 𝒫 x ∈ₚ 传递.
Proof.
  intros tr y z zy yp. apply 幂集. apply 传递_子集表述. auto.
  apply 幂集 in yp. auto.
Qed.

End Basic.

Notation 非空 x := (∃ y, y ∈ x).
Notation "{ a , b }" := (偶 a b) : zf_scope.
Notation "{ a , }" := (单 a) (format "{ a , }") : zf_scope.
Notation "A ∪ B" := (偶并 A B) (at level 50) : zf_scope.
Notation "x ⨮ y" := (入 x y) (at level 65, right associativity) : zf_scope.
Notation "a ⁺" := (继 a) (at level 6, format "a ⁺") : zf_scope.
Notation "F [ A ]" := (F替 F A) (at level 7, format "F [ A ]") : zf_scope.
Notation "'𝒫[' A ]" := (幂[A]) (format "𝒫[ A ]") : zf_scope.
Notation "A ∩ₚ P" := (分 A P) (at level 60) : zf_scope.

Global Hint Resolve 空集是子集 : zf.
Global Hint Resolve 单集I : zf.
