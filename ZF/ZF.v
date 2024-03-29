(** Coq coding by choukh, May 2022 **)

From ZF Require Export Meta.

(** ZF模型的定义 **)

Class ZF结构 := {
  集 : Type;
  属 : 集 → 集 → Prop;
  空 : 集;
  并 : 集 → 集;
  幂 : 集 → 集;
  替 : (集 → 集 → Prop) → 集 → 集
}.

Coercion 集 : ZF结构 >-> Sortclass.

Declare Scope zf_scope.
Delimit Scope zf_scope with zf.
Open Scope zf_scope.

Notation "x ∈ y" := (  属 x y) (at level 70) : zf_scope.
Notation "x ∉ y" := (¬ 属 x y) (at level 70) : zf_scope.

Notation "∀ x .. y ∈ A , P" :=
  (∀ x, x ∈ A → (.. (∀ y, y ∈ A → P) ..))
  (only parsing, at level 200, x binder, right associativity) : zf_scope.

Notation "∃ x .. y ∈ A , P" :=
  (∃ x, x ∈ A ∧ (.. (∃ y, y ∈ A ∧ P) ..))
  (only parsing, at level 200, x binder, right associativity) : zf_scope.

Definition 包含关系 {𝓜 : ZF结构} (A B : 𝓜) := ∀ x, x ∈ A → x ∈ B.
Notation "A ⊆ B" := (  包含关系 A B) (at level 70) : zf_scope.
Notation "A ⊈ B" := (¬ 包含关系 A B) (at level 70) : zf_scope.
Notation "p ⊂ q" := (p ⊆ q ∧ q ⊈ p) (at level 70) : zf_scope.

Notation "∅" := 空 : zf_scope.
Notation "⋃ A" := (并 A) (at level 8, right associativity, format "⋃  A") : zf_scope.
Notation "'𝒫' A" := (幂 A) (at level 9, right associativity, format "'𝒫'  A") : zf_scope.
Notation "R @ A" := (替 R A) (at level 60) : zf_scope.

Inductive 良基 {𝓜 : ZF结构} (A : 𝓜) : Prop :=
  | 良基I : (∀ x ∈ A, 良基 x) → 良基 A.

Class ZF := {
  结构 :> ZF结构;
  外延 : ∀ x y, x ⊆ y → y ⊆ x → x = y;
  空集 : ∀ x, x ∉ ∅;
  并集 : ∀ x A, x ∈ ⋃ A ↔ ∃ y, x ∈ y ∧ y ∈ A;
  幂集 : ∀ x A, x ∈ 𝒫 A ↔ x ⊆ A;
  替代 : ∀ R A, 函数性 R → ∀ y, y ∈ R @ A ↔ ∃ x ∈ A, R x y;
  正则 : ∀ x, 良基 x
}.

Coercion 结构 : ZF >-> ZF结构.
Arguments 正则 {_} _.

(** 涉及类的记法 **)

Notation "x ∈ₚ P" := (P x) (only parsing, at level 70) : zf_scope.
Notation "x ∉ₚ P" := (¬ P x) (only parsing, at level 70) : zf_scope.
Notation "P ⊑ Q" := (∀ x, x ∈ₚ P → x ∈ₚ Q) (at level 70) : zf_scope.
Notation "P ⋢ Q" := (¬ ∀ x, x ∈ₚ P → x ∈ₚ Q) (at level 70) : zf_scope.
Notation "P ⊓ Q" := (λ x, x ∈ₚ P ∧ x ∈ₚ Q) (at level 60) : zf_scope.
Notation "A '⊆ₚ' P" := (∀ x, x ∈ A → x ∈ₚ P) (at level 70) : zf_scope.
Notation "P '⊆ₛ' A" := (∀ x, x ∈ₚ P → x ∈ A) (at level 70) : zf_scope.
Notation "A =ₚ P" := (∀ x, x ∈ A ↔ x ∈ₚ P) (at level 70) : zf_scope.
Notation "'setLike' P" := (∃ A, A =ₚ P) (only parsing, at level 10) : zf_scope.

Notation "∀ x .. y ∈ₚ A , P" :=
  (∀ x, x ∈ₚ A → (.. (∀ y, y ∈ₚ A → P) ..))
  (only parsing, at level 200, x binder, right associativity) : zf_scope.

Notation "∃ x .. y ∈ₚ A , P" :=
  (∃ x, x ∈ₚ A ∧ (.. (∃ y, y ∈ₚ A ∧ P) ..))
  (only parsing, at level 200, x binder, right associativity) : zf_scope.

(** 封闭性 **)
Section Closure.
Context {𝓜 : ZF}.
Implicit Type A a b x y : 𝓜.
Implicit Type P : 𝓜 → Prop.

Definition 传递 x := ∀ y z, y ∈ z → z ∈ x → y ∈ x.
Definition 膨胀 x := ∀ y z, y ⊆ z → z ∈ x → y ∈ x.

Definition 传递类 P := ∀ x y, x ∈ y → y ∈ₚ P → x ∈ₚ P.
Definition 膨胀类 P := ∀ x y, x ⊆ y → y ∈ₚ P → x ∈ₚ P.

Definition 空集封闭 x := ∅ ∈ x.
Definition 并集封闭 x := ∀ y ∈ x, ⋃ y ∈ x.
Definition 幂集封闭 x := ∀ y ∈ x, 𝒫 y ∈ x.

Definition 替代封闭 x := ∀ R y, 函数性 R → (∀ a b, R a b → a ∈ y → b ∈ x) → y ∈ x → R @ y ∈ x.
Definition 替代封闭' x := ∀ R y, 函数性 R → R @ y ⊆ x → y ∈ x → R @ y ∈ x.

Fact 替代封闭_等价表述 x : 替代封闭 x ↔ 替代封闭' x.
Proof.
  split; intros C R A FR H1 H2; apply C; auto.
  - intros a b Rab aA. apply H1.
    apply 替代. auto. now exists a.
  - intros z [y [yA Ryz]]%替代; auto. eapply H1; eauto.
Qed.

Class 封闭类 P : Prop := {
  成员封闭类 : 传递类 P;
  空集封闭类 : ∅ ∈ₚ P;
  并集封闭类 x : x ∈ₚ P → ⋃ x ∈ₚ P;
  幂集封闭类 x : x ∈ₚ P → 𝒫 x ∈ₚ P;
  替代封闭类 R A : 函数性 R → 
    (∀ x y, R x y → x ∈ A → y ∈ₚ P) → A ∈ₚ P → R @ A ∈ₚ P
}.

End Closure.

(* 构造化无穷公理 *)
Class Infʷ {𝓜 : ZF} := {
  嵌入 : nat → 𝓜;
  嵌入单射 : ∀ m n, 嵌入 m = 嵌入 n → m = n;
  有穷序数 x := ∃ n, x = 嵌入 n;
  ω : 𝓜;
  无穷 : ω =ₚ 有穷序数
}.

(** 自动化设置 **)

Create HintDb zf discriminated.
Global Hint Constants Transparent : zf.
Global Hint Variables Transparent : zf.

Tactic Notation "zf" := auto with zf.
Tactic Notation "ezf" := eauto with zf.

Global Hint Unfold 包含关系 : zf.
Global Hint Unfold 函数性 : zf.

Global Hint Extern 4 => 
match goal with 
  | [ H : _ ∈ ∅ |- _ ] => exfalso; eapply (空集 H)
end : zf.
