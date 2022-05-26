(** Coq coding by choukh, May 2022 **)

Require Export Utf8_core Classical ProofIrrelevance.
Global Set Implicit Arguments. 
Global Unset Strict Implicit.
Global Unset Printing Implicit Defensive.

(** 经典逻辑 **)

Tactic Notation "排中" constr(P) :=
  destruct (classic P).
Tactic Notation "排中" constr(P) "as" simple_intropattern(L) :=
  destruct (classic P) as L.

Ltac 反证 := match goal with
  |- ?G => destruct (classic G) as [?正设|?反设]; [assumption|exfalso]
end.

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

Implicit Types 𝓜 : ZF结构.

Definition 包含关系 {𝓜} (A B : 𝓜) := ∀ x, x ∈ A → x ∈ B.
Notation "A ⊆ B" := (  包含关系 A B) (at level 70) : zf_scope.
Notation "A ⊈ B" := (¬ 包含关系 A B) (at level 70) : zf_scope.

Definition 传递 {𝓜} x := ∀ y, y ∈ x → y ⊆ x.
Definition 膨胀 {𝓜} x := ∀ y z, y ∈ x → z ⊆ y → z ∈ x.

Notation "∅" := 空 : zf_scope.
Notation "⋃ A" := (并 A) (at level 8, right associativity, format "⋃  A") : zf_scope.
Notation "'𝒫' A" := (幂 A) (at level 9, right associativity, format "'𝒫'  A") : zf_scope.
Notation "R @ A" := (替 R A) (at level 60) : zf_scope.

Definition 函数性 {X Y} (R : X → Y → Prop) :=
  ∀ x y y', R x y → R x y' → y = y'.

Inductive 良基 {𝓜} (A : 𝓜) : Prop :=
  | wf_intro : (∀ x ∈ A, 良基 x) → 良基 A.

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

(** 关于类 **)

Definition 集化 {𝓜} (P : 𝓜 → Prop) (A : 𝓜) := ∀ x, x ∈ A ↔ P x.

Notation "x ∈ₚ P" := (P x) (only parsing, at level 70) : zf_scope.
Notation "P ⊑ Q" := (∀ x, x ∈ₚ P → x ∈ₚ Q) (at level 70) : zf_scope.
Notation "A '⊆ₚ' P" := (∀ x, x ∈ A → x ∈ₚ P) (at level 70) : zf_scope.
Notation "P '⊆ₛ' A" := (∀ x, x ∈ₚ P → x ∈ A) (at level 70) : zf_scope.

Notation "∀ x .. y ∈ₚ A , P" :=
  (∀ x, x ∈ₚ A → (.. (∀ y, y ∈ₚ A → P) ..))
  (only parsing, at level 200, x binder, right associativity) : zf_scope.

Notation "∃ x .. y ∈ₚ A , P" :=
  (∃ x, x ∈ₚ A ∧ (.. (∃ y, y ∈ₚ A ∧ P) ..))
  (only parsing, at level 200, x binder, right associativity) : zf_scope.

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
