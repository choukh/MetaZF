(** Coq coding by choukh, June 2022 **)

From HF Require Export Meta.

Reserved Notation "x ⨮ y" (at level 65, right associativity).
Reserved Notation "x ∈ y" (at level 70).

(** 遗传有穷结构 **)
Class HF := {
  集 : Type;
  空 : 集;
  并 : 集 → 集 → 集
    where "x ⨮ y" := (并 x y) (* {x} ∪ y *)
    and "x ∈ y" := (x ⨮ y = y);
  栖 x y : x ⨮ y ≠ 空;
  入 x y : x ∈ x ⨮ y;
  易 x y z : x ⨮ y ⨮ z = y ⨮ x ⨮ z;
  属 x y z : x ∈ y ⨮ z → x = y ∨ x ∈ z;
  强归纳 (P : 集 → Type) : P 空 → (∀ x y, P x → P y → P (x ⨮ y)) → ∀ x, P x;
}.

Coercion 集 : HF >-> Sortclass.
Arguments 空 {_}.

Notation "∅" := 空 : hf_scope.
Notation "x ⨮ y" := (并 x y) : hf_scope.
Notation "x ∈ y" := (x ⨮ y = y) : hf_scope.
Notation "x ∉ y" := (x ⨮ y ≠ y) (at level 70) : hf_scope.
Notation "x ⊆ y" := (∀ z, z ∈ x → z ∈ y) (at level 70) : hf_scope.
Notation "x ⊈ y" := (¬ x ⊆ y) (at level 70) : hf_scope.
Notation "x ⁺" := (x ⨮ x) (at level 50) : hf_scope.
Notation "{ x , }" := (x ⨮ ∅) (format "{ x , }") : hf_scope.
Notation "{ x , y }" := (x ⨮ {y,}) : hf_scope.
Notation 栖居 x := (∃ y, y ∈ x).

Notation "∀ x .. y ∈ A , P" :=
  (∀ x, x ∈ A → (.. (∀ y, y ∈ A → P) ..))
  (only parsing, at level 200, x binder, right associativity) : hf_scope.

Notation "∃ x .. y ∈ A , P" :=
  (∃ x, x ∈ A ∧ (.. (∃ y, y ∈ A ∧ P) ..))
  (only parsing, at level 200, x binder, right associativity) : hf_scope.

Ltac hf_ind x := pattern x; revert x; apply 强归纳.

(* 基本事实 *)
Section Basic.
Context {𝓜 : HF}.
Implicit Types x y z : 𝓜.

Theorem 空集定理 x : x ∉ ∅.
Proof. intros []%栖. Qed.

Example 并运算测试 : {{∅,},} ≠ {∅,}.
Proof.
  intros H. assert (H' := H). rewrite <- 入, H in H'.
  apply 属 in H' as [H'|H']; now apply 空集定理 in H'.
Qed.

Theorem 并运算规范 x y z : z ∈ x ⨮ y ↔ z = x ∨ z ∈ y.
Proof.
  split.
  - apply 属.
  - intros [-> | H].
    + apply 入.
    + now rewrite 易, H.
Qed.

Fact 并作子集 x y z : x ⨮ y ⊆ z ↔ x ∈ z ∧ y ⊆ z. 
Proof.
  split.
  - intros H. split.
    + apply H, 入.
    + intros a ay. apply H, 并运算规范. now right.
  - intros [H1 H2] a [->|]%并运算规范; auto.
Qed.

Fact 空集的子集 x : x ⊆ ∅ → x = ∅.
Proof.
  hf_ind x.
  - auto.
  - intros x y _ _ H.
    assert (x0: x ∈ ∅) by apply H, 入.
    contradict (空集定理 x0).
Qed.

Fact 空集可判定 x : x = ∅ ∨ 栖居 x.
Proof.
  hf_ind x.
  - now left.
  - intros x y _ _. right. exists x. apply 入.
Qed.

Fact 非空即栖居 x : x ≠ ∅ ↔ 栖居 x.
Proof.
  destruct (空集可判定 x) as [->|[y yx]]; split.
  - easy.
  - intros [x x0]. contradict (空集定理 x0).
  - eauto.
  - intros _ ->. contradict (空集定理 yx).
Qed.

Definition 传递 x := ∀ y z, y ∈ z → z ∈ x → y ∈ x.

End Basic.

(** 自动化 **)

Lemma 全称等价左 T P Q : (∀ x : T, P x ↔ Q x) → ∀ x, P x → Q x.
Proof. firstorder. Qed.

Lemma 全称等价右 T P Q : (∀ x : T, P x ↔ Q x) → ∀ x, Q x → P x.
Proof. firstorder. Qed.

Ltac 非前提 P := match goal with
  |[_ : P |- _] => fail 1
  | _ => idtac
end.
Ltac 加前提 H := let T := type of H in 非前提 T; generalize H; intro.

Ltac 引入 := match goal with
  |[ |- _ → _ ] => intro
  |[ |- _ ∧ _ ] => split
  |[ |- _ ↔ _] => split
  |[ |- ¬ _ ] => intro
  |[ |- ∀ _, _ ] => intro
  |[ |- _ ∈ _ ⨮ _] => apply 并运算规范
  |[ |- 栖居 _] => apply 非空即栖居
  |[ |- 传递 _] => hnf
end.

Ltac 消去 := match goal with
  |[H: Σ _, _ |- _ ] => destruct H
  |[H: ∃ _, _ |- _ ] => destruct H
  |[H: _ ∧ _ |- _ ] => destruct H
  |[H: _ * _ |- _] => destruct H
  |[H: ∀ _, _ ↔ _  |- _] => 加前提 (全称等价左 H); 加前提 (全称等价右 H); clear H
  |[H: ?P ∨ ?Q |- _] => 非前提 P; 非前提 Q; destruct H 
  |[H: ?P + ?Q |- _] => 非前提 P; 非前提 Q; destruct H 
  |[H: _ ⨮ _ = ∅ |- _] => destruct (栖 H)
  |[H: ∅ = _ ⨮ _ |- _] => destruct (栖 (eq_sym H))
  |[H: _ ∈ ∅ |- _] => destruct (空集定理 H)
  |[H: ?z ∈ ?x ⨮ _ |- _] => apply 并运算规范 in H as [|]
  |[H: _ ⨮ _ ⊆ _ |- _ ] => apply 并作子集 in H as []
  |[H: _ ⊆ ∅ |- _] => apply 空集的子集 in H as ->
  |[H: 传递 ?x, H': _ ∈ ?x |- _] => 加前提 (H _ H')
end.

Ltac hf n := repeat progress (reflexivity || subst || 引入 || 消去);
  try tauto; match n with
  | O => idtac
  | S ?n => match goal with
    |[ |- _ ∨ _] => solve [left; hf n | right; hf n]
    |[ |- _ + _] => solve [left; hf n | right; hf n]
    |[ |- 可判定 _] => solve [left; hf n | right; hf n]
    |[ |- ?x ⨮ ?y ⨮ ?z = ?y ⨮ ?x ⨮ ?z ] => apply 易
    |[ |- ?x ∈ ?x ⨮ ?y ] => apply 入
    |[ |- ?x ⨮ ?y = ?x ⨮ ?x ⨮ ?y ] => now rewrite 入
    |[H: ?X |- ∃ x : ?X, _ ] => exists H; hf n
    |[H: ∀ x,  x ∈ ?z → _, H': ?X ∈ ?z |- _ ] => 加前提 (H X H'); clear H; hf n
    |[H: ∀ x, _ → x ∈ ?z |- _ ∈ ?z] => apply H; hf n
    |[H: ?x ⊆ _, H': ?z ∈ ?x |- _ ] => 加前提 (H z H'); clear H; hf n
  end
end.

Tactic Notation "hf" := cbn; solve [hf 7].
