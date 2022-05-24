(** Coq coding by choukh, May 2022 **)

Require Export Full.Meta Full.Relation.

(*** 结构 ***)

Class 集结构 := {
  集 : Type;
  成员关系 : 集 → 集 → Prop
}.

Coercion 集 : 集结构 >-> Sortclass.

Class Z结构 := {
  Z集 :> 集结构;
  空 : Z集;
  偶 : Z集 → Z集 → Z集;
  并 : Z集 → Z集;
  幂 : Z集 → Z集;
  分 : (Z集 → Prop) → Z集 → Z集
}.

Coercion Z集 : Z结构 >-> 集结构.

Class ZF'结构 := { 
  弱ZF集 :> Z结构;
  替 : (弱ZF集 → 弱ZF集) → 弱ZF集 → 弱ZF集
}.

Coercion 弱ZF集 : ZF'结构 >-> Z结构.

Class ZF结构 := { 
  ZF集 :> ZF'结构;
  描述 : (ZF集 → Prop) → ZF集
}.

Coercion ZF集 : ZF结构 >-> ZF'结构.

Notation "x ∈ y" := (  成员关系 x y) (at level 70) : zf_scope.
Notation "x ∉ y" := (¬ 成员关系 x y) (at level 70) : zf_scope.

Definition 包含关系 {𝓜 : 集结构} (A B : 𝓜) := ∀ x, x ∈ A → x ∈ B.
Notation "A ⊆ B" := (  包含关系 A B) (at level 70) : zf_scope.
Notation "A ⊈ B" := (¬ 包含关系 A B) (at level 70) : zf_scope.

Definition 集等价 {𝓜 : 集结构} (A B : 𝓜) := A ⊆ B ∧ B ⊆ A.
Notation "x == y" := (集等价 x y) (at level 70) : zf_scope.

Notation "∅" := 空 : zf_scope.
Notation "[ a , b ]" := (偶 a b) : zf_scope.
Notation "⋃ A" := (并 A) (at level 8, right associativity, format "⋃  A") : zf_scope.
Notation "'𝒫' A" := (幂 A) (at level 9, right associativity, format "'𝒫'  A") : zf_scope.
Notation "P ∩ A" := (分 P A) (at level 60) : zf_scope.
Notation "F @ A" := (替 F A) (at level 60) : zf_scope.

(* x ∈ A → x ∈ P *)
Notation "A ⊑ P" := (∀ x, x ∈ A → P x) (at level 70) : zf_scope.

(** 内涵ZF结构 **)

Class iZ₀ (𝓜 : Z结构) : Prop := {
  形变 : ∀ x y A, x == y → x ∈ A → y ∈ A;
  空集 : ∀ x, x ∉ ∅;
  配对 : ∀ x a b, x ∈ [a, b] ↔ x == a ∨ x == b;
  并集 : ∀ x y, x ∈ ⋃ y ↔ ∃ w, w ∈ x ∧ x ∈ y;
  幂集 : ∀ x y, x ∈ 𝒫 y ↔ x ⊆ y;
  分离 : ∀ P x A, 谓词尊重 集等价 P → x ∈ P ∩ A ↔ x ∈ A ∧ P x
}.

Inductive 良基 {𝓜 : 集结构} (A : 𝓜) : Prop :=
  | WF : (∀ x, x ∈ A → 良基 x) → 良基 A.

Class iZ (𝓜 : Z结构) : Prop := {
  iZ实装 :> iZ₀ 𝓜;
  正则 : ∀ x, 良基 x
}.

Class iZF' (𝓜 : ZF'结构) : Prop := {
  iZF'实装 :> iZ 𝓜;
  替代 : ∀ F y A, 函数尊重 集等价 F → y ∈ F @ A ↔ ∃ x, x ∈ A ∧ y == F x
}.

Definition 为集等价类 {𝓜 : 集结构} (P : 𝓜 → Prop) := ∃ x, ∀ y, P y ↔ x == y.

Class iZF (𝓜 : ZF结构) : Prop := {
  iZF实装 :> iZF' 𝓜;
  描述1 : ∀ P, 为集等价类 P → P (描述 P);
  描述2 : ∀ P Q, (∀ x, P x ↔ Q x) → 描述 P = 描述 Q
}.

(** 外延ZF结构 **)

Class Z (𝓜 : Z结构) : Prop := {
  Z实装 :> iZ 𝓜;
  Z外延 : ∀ x y, x == y ↔ x = y
}.

Class ZF' (𝓜 : ZF'结构) : Prop := {
  ZF'实装 :> iZF' 𝓜;
  ZF'外延 : ∀ x y, x == y ↔ x = y
}.

Class ZF (𝓜 : ZF结构) : Prop := {
  ZF实装 :> iZF 𝓜;
  外延 : ∀ x y, x == y ↔ x = y
}.

Class ZF₀ (𝓜 : ZF结构) : Prop := {
  ZF₀实装 :> iZ₀ 𝓜;
  ZF₀外延 : ∀ x y, x == y ↔ x = y;
  ZF₀替代 : ∀ F y A, 函数尊重 集等价 F → y ∈ F @ A ↔ ∃ x, x ∈ A ∧ y == F x;
  ZF₀描述1 : ∀ P, 为集等价类 P → P (描述 P);
  ZF₀描述2 : ∀ P Q, (∀ x, P x ↔ Q x) → 描述 P = 描述 Q
}.
