(** Coq coding by choukh, May 2022 **)

From ZF Require Import Basic.

(*** 序数 ***)
Section Ordinal.
Context {𝓜 : ZF}.
Implicit Type P : 𝓜 → Prop.
Implicit Type R : 𝓜 → 𝓜 → Prop.

Inductive Ord : 𝓜 → Prop :=
  | Ord_S x : x ∈ₚ Ord → x⁺ ∈ₚ Ord
  | Ord_U x : x ⊆ₚ Ord → ⋃ x ∈ₚ Ord.

Lemma 空集是序数 : ∅ ∈ₚ Ord.
Proof. rewrite <- 并空. constructor. zf. Qed.

Lemma Ord传递 : Ord ⊑ 传递.
Proof. induction 1. now apply 后继传递. now apply 并传递. Qed.

Lemma Ord传递类 : 传递类 Ord.
Proof.
  intros α β αβ βO. induction βO as [β βO IH|β βO IH].
  - apply 后继 in αβ as [->|]; auto.
  - apply 并集 in αβ as [γ []]. eapply IH; eauto.
Qed.

(** 整体良序 **)

Lemma Ord对关系的归纳法 R :
  (∀ x y, R x y → R y x → R x⁺ y) →
  (∀ x y, (∀ z, z ∈ x → R z y) → R (⋃ x) y) →
  ∀ x y ∈ₚ Ord, R x y.
Proof.
  intros H1 H2 x xO y. revert y.
  induction xO as [x _ IHx|x xO IHx]; intros y yO.
  - apply H1. apply IHx. apply yO.
    induction yO as [y yO IHy|y _ IHy].
    + apply H1. apply IHy. apply IHx. apply yO.
    + apply H2. apply IHy.
  - apply H2. intros z zx. now apply IHx.
Qed.

Lemma Ord弱线序_引理 : ∀ x y ∈ₚ Ord, x ⊆ y ∨ y⁺ ⊆ x.
Proof.
  apply Ord对关系的归纳法.
  - intros x y [xy|pyx] [yx|pxy]; auto.
    + right. rewrite (外延 xy yx). zf.
    + right. enough (x ⊆ x⁺) by firstorder. zf.
  - intros x y H. 排中 (∃ z ∈ x, z ⊈ y) as [[z [zx zny]]|false].
    + right. destruct (H z zx) as [zy|pzy]. easy.
      enough (z ⊆ ⋃ x). zf. now apply 并得父集.
    + left. apply 并得子集. intros z zx. 反证.
      apply false. now exists z.
Qed.

Lemma Ord弱线序 x y : x ∈ₚ Ord → y ∈ₚ Ord → x ⊆ y ∨ y ⊆ x.
Proof. intros xO yO. destruct (Ord弱线序_引理 xO yO); zf. Qed.

Lemma Ord线序 x y : x ∈ₚ Ord → y ∈ₚ Ord → x ⊆ y ∨ y ∈ x.
Proof. intros xO yO. destruct (Ord弱线序_引理 xO yO); zf. Qed.

Lemma Ord三歧 x y : x ∈ₚ Ord → y ∈ₚ Ord → x = y ∨ x ∈ y ∨ y ∈ x.
Proof.
  intros xO yO. destruct (Ord线序 xO yO); auto.
  destruct (Ord线序 yO xO); auto. left. now apply 外延.
Qed.

(* Ord与任意类的非空交有⊆最小元 *)
Lemma Ord良基 P x : x ∈ₚ Ord ⊓ P → ex (最小 (Ord ⊓ P)).
Proof.
  intros [xO xP]. induction (正则 x) as [x _ IH].
  排中 (∃ y ∈ x, y ∈ₚ Ord ∧ y ∈ₚ P) as [[y [yx [yO yP]]]|].
  - now apply (IH y).
  - exists x. repeat split; auto. intros y [yO yP].
    destruct (Ord线序 xO yO). auto.
    contradict H. now exists y.
Qed.

(** 内部良序 **)

Definition ϵ反自反 A := ∀ a ∈ A, a ∉ a.
Definition ϵ传递 A := ∀ a b c ∈ A, a ∈ b → b ∈ c → a ∈ c.
Definition ϵ偏序 A := ϵ反自反 A ∧ ϵ传递 A.

Definition ϵ三歧 A := ∀ a b ∈ A, a = b ∨ a ∈ b ∨ b ∈ a.
Definition ϵ线序 A := ϵ偏序 A ∧ ϵ三歧 A.

Definition ϵ最小 := λ A m, m ∈ A ∧ ∀ x ∈ A, m ⊆ x.
Definition ϵ良基 A := ∀ B, 非空 B → B ⊆ A → ex (ϵ最小 B).
Definition ϵ良序 A := ϵ线序 A ∧ ϵ良基 A.

Lemma Ord_ϵ反自反 : Ord ⊑ ϵ反自反.
Proof. intros _ _ x _. apply 无循环1. Qed.

Lemma Ord_ϵ传递 : Ord ⊑ ϵ传递.
Proof.
  induction 1 as [α _ IH|A HA IH].
  - intros x [->|]%后继 y [->|]%后继 z [->|]%后继 xy yz; trivial.
    + exfalso. eapply 无循环2; eauto.
    + exfalso. eapply 无循环3; eauto.
    + exfalso. eapply 无循环2; eauto.
    + eapply IH. 4:apply xy. all: trivial.
  - intros x [α [xα αA]]%并集 y [β [yβ βA]]%并集 z [γ [zγ γA]]%并集 xy yz.
    assert (tr: γ ∈ₚ 传递). apply Ord传递, HA, γA.
    assert (yγ: y ∈ γ). eapply tr; eauto.
    assert (xγ: x ∈ γ). eapply tr; eauto.
    assert (ϵtr: γ ∈ₚ ϵ传递). apply IH, γA.
    eapply ϵtr. 4:apply xy. all: trivial.
Qed.

Lemma Ord_ϵ三歧 : Ord ⊑ ϵ三歧.
Proof.
  induction 1 as [α _ IH|A HA IH].
  - intros x [->|]%后继 y [->|]%后继; firstorder.
  - intros x [α [xα αA]]%并集 y [β [yβ βA]]%并集.
    destruct (@Ord弱线序 α β). 1-2:apply HA; trivial.
    + apply H in xα. apply IH in βA. apply βA; trivial.
    + apply H in yβ. apply IH in αA. apply αA; trivial.
Qed.

Lemma Ord_ϵ良基 : Ord ⊑ ϵ良基.
Proof with zf; eauto.
  destruct 1 as [α αO|A HA].
  - intros A [β βA] sub.
    destruct (@Ord良基 (λ x, x ∈ A) β) as [μ [[μO μB] min]]. split...
    + apply sub in βA as [->|]%后继... apply Ord传递类 with α...
    + exists μ. split... intros x xA. apply min. split...
      apply sub in xA as [->|]%后继... apply Ord传递类 with α...
  - intros B [β βB] sub.
    destruct (@Ord良基 (λ x, x ∈ B) β) as [μ [[μO μB] min]]. split...
    + apply sub in βB as [γ [βγ γA]]%并集. apply Ord传递类 with γ...
    + exists μ. split... intros x xB. apply min. split...
      apply sub in xB as [γ [βγ γA]]%并集. apply Ord传递类 with γ...
Qed.

(** 等价于ϵ良序传递集之类 **)

Lemma ϵ线序集对子集封闭 A B : B ⊆ A → ϵ线序 A → ϵ线序 B.
Proof with auto.
  intros ub lin. repeat split.
  - intros x Hx. apply lin...
  - intros x Hx y Hy z Hz. apply lin...
  - intros x Hx y Hy. apply lin...
Qed.

Lemma ϵ良基集对子集封闭 A B : B ⊆ A → ϵ良基 A → ϵ良基 B.
Proof. intros BA wf C ne CB. apply wf; auto. firstorder. Qed.

Lemma ϵ良序集对子集封闭 A B : B ⊆ A → ϵ良序 A → ϵ良序 B.
Proof with auto.
  intros sub [lin wf]. split.
  - apply ϵ线序集对子集封闭 with A...
  - apply ϵ良基集对子集封闭 with A...
Qed.

Definition ϵ良序传递 A := ϵ良序 A ∧ 传递 A.

Lemma ϵ良序传递_传递类 : 传递类 ϵ良序传递.
Proof with auto.
  intros β α Hβα [wo tr]. split.
  - apply ϵ良序集对子集封闭 with α... apply 传递_子集表述...
  - intros δ γ Hδγ Hγβ.
    assert (Hγα: γ ∈ α). apply tr with β...
    assert (Hδα: δ ∈ α). apply tr with γ...
    apply wo with γ...
Qed.

Lemma ϵ良序传递_反自反 α : ϵ良序传递 α → α ∉ α.
Proof. intros αO 反设. cut (α ∉ α); auto. apply αO; auto. Qed.

Lemma ϵ良序传递_传递 α β γ : ϵ良序传递 γ → α ∈ β → β ∈ γ → α ∈ γ.
Proof. intros. eapply H; eauto. Qed.

Lemma ϵ良序传递_强序等价 α β : ϵ良序传递 α → ϵ良序传递 β → α ∈ β ↔ α ⊂ β.
Proof with auto.
  intros αO βO. split.
  - split. apply 传递_子集表述... apply βO.
    intros sub. apply ϵ良序传递_反自反 with α...
  - intros [αβ βα]. set (β ∩ₚ (λ x, x ∉ α)) as δ.
    assert (wf: ϵ良基 β) by apply βO.
    destruct (wf δ) as [μ [[μβ μα]%分离 min]].
    + apply 非子集 in βα as [γ Hγ]. exists γ. apply 分离...
    + intros x []%分离...
    + assert (μO: ϵ良序传递 μ). apply ϵ良序传递_传递类 with β...
      replace α with μ... apply 外延; intros x Hx; 反证.
      * assert (xδ: x ∈ δ). apply 分离. split... apply βO with μ...
        apply min in xδ. apply xδ in Hx. apply 无循环1 with x...
      * apply αβ in Hx as xβ. assert (tri: ϵ三歧 β) by apply βO.
        destruct (tri x xβ μ μβ) as [->|[]]...
        apply μα. apply αO with x...
Qed.

Notation "a ⋸ b" := (a = b ∨ a ∈ b) (at level 70).

Lemma ϵ良序传递_弱序等价 α β : ϵ良序传递 α → ϵ良序传递 β → α ⊆ β ↔ α ⋸ β.
Proof with zf.
  intros αO βO. split.
  - intros. 排中 (β ⊆ α). left. apply 外延... right. apply ϵ良序传递_强序等价...
  - intros [->|]... apply ϵ良序传递_强序等价...
Qed.

Lemma ϵ良序传递_对二元交封闭 α β : ϵ良序传递 α → ϵ良序传递 β → ϵ良序传递 (α ∩ₚ (λ x, x ∈ β)).
Proof with eauto.
  intros [woα trα] [woβ trβ]. split.
  - apply ϵ良序集对子集封闭 with α... intros x []%分离...
  - intros δ γ δγ [γα γβ]%分离.
    apply 分离. split. eapply trα... eapply trβ...
Qed.

Lemma ϵ良序传递_三歧 α β : ϵ良序传递 α → ϵ良序传递 β → α = β ∨ α ∈ β ∨ β ∈ α.
Proof with auto.
  intros αO βO.
  assert (iO: ϵ良序传递 (α ∩ₚ (λ x, x ∈ β))). apply ϵ良序传递_对二元交封闭...
  assert (H1: α ∩ₚ (λ x, x ∈ β) ⊆ α). intros x []%分离...
  assert (H2: α ∩ₚ (λ x, x ∈ β) ⊆ β). intros x []%分离...
  apply ϵ良序传递_弱序等价 in H1 as [H1|H1], H2 as [H2|H2]...
  - left. congruence.
  - right. left. congruence.
  - right. right. congruence.
  - exfalso. apply ϵ良序传递_反自反 with (α ∩ₚ (λ x, x ∈ β))... apply 分离...
Qed.

Lemma ϵ良序传递_弱线序 α β : ϵ良序传递 α → ϵ良序传递 β → α ⊆ β ∨ β ⊆ α.
Proof.
  intros αO βO. destruct (ϵ良序传递_三歧 αO βO) as [->|[]]; zf.
  - left. apply ϵ良序传递_弱序等价; auto.
  - right. apply ϵ良序传递_弱序等价; auto.
Qed.

Lemma ϵ良序传递_线序 α β : ϵ良序传递 α → ϵ良序传递 β → α ⊆ β ∨ β ∈ α.
Proof.
  intros αO βO. destruct (ϵ良序传递_三歧 αO βO) as [->|[]]; zf.
  left. apply ϵ良序传递_弱序等价; auto.
Qed.

Lemma ϵ良序传递_良基 P x : x ∈ₚ ϵ良序传递 ⊓ P → ex (最小 (ϵ良序传递 ⊓ P)).
Proof with eauto.
  intros [xO xP]. 排中 (最小 (ϵ良序传递 ⊓ P) x). exists x...
  assert (wf: ϵ良基 x). apply xO.
  destruct (wf (x ∩ₚ P)) as [μ [[μx μP]%分离 min]]...
  - apply 非空I. intros H0. apply H. split...
    intros y [yO yP]. destruct (@ϵ良序传递_线序 x y)...
    exfalso. eapply 空集. rewrite <- H0. apply 分离...
  - intros y []%分离...
  - assert (μO: ϵ良序传递 μ). apply ϵ良序传递_传递类 with x...
    exists μ. split... intros y [yO yP]. destruct (@ϵ良序传递_线序 μ y)...
    apply min, 分离. split... apply xO with μ...
Qed.

Lemma ϵ良序传递集之集_ϵ良序 A : A ⊆ₚ ϵ良序传递 → ϵ良序 A.
Proof with auto.
  intros. repeat split; intros α Hα.
  - apply ϵ良序传递_反自反...
  - intros β _ γ Hγ. apply ϵ良序传递_传递...
  - intros β Hβ. apply ϵ良序传递_三歧...
  - intros sub. destruct Hα as [β βα].
    destruct (@ϵ良序传递_良基 (λ x, x ∈ α) β) as [μ [[μO μα] min]]...
    exists μ. split...
Qed.

Lemma ϵ良序传递集之传递集 A : A ⊆ₚ ϵ良序传递 → 传递 A → ϵ良序传递 A.
Proof. intros sub tr. split; trivial. apply ϵ良序传递集之集_ϵ良序; auto. Qed.

Lemma ϵ良序传递_后继 α : ϵ良序传递 α → ϵ良序传递 α⁺.
Proof.
  intros αO. apply ϵ良序传递集之传递集.
  - intros x Hx. apply 后继 in Hx as [->|]; trivial.
    eapply ϵ良序传递_传递类; eauto.
  - apply 后继传递, αO.
Qed.

Lemma ϵ良序传递_二分 α : α ∈ₚ ϵ良序传递 → (∃ β, α = β⁺) ∨ α = ⋃ α.
Proof with zf.
  intros Hα. 排中 (α = ⋃ α) as [|neq]... left.
  assert (sub: α ⊈ ⋃ α). {
    intros sub. apply neq. apply 外延...
    apply 并得子集, 传递_子集表述, Hα.
  }
  apply 非子集 in sub as [β [Hβ Hβ']].
  exists β. 反证. destruct (@ϵ良序传递_三歧 β⁺ α) as [|[]]...
  - apply ϵ良序传递_后继, ϵ良序传递_传递类 with α...
  - apply Hβ'. apply 并集. exists β⁺...
  - apply 后继 in H as [->|].
    eapply 无循环1; eauto. eapply 无循环2; eauto.
Qed.

Theorem Ord_ϵ良序传递 α : α ∈ₚ Ord ↔ α ∈ₚ ϵ良序传递.
Proof with zf. split.
  - intros αO. split. 2:apply Ord传递... repeat split.
    apply Ord_ϵ反自反... apply Ord_ϵ传递... apply Ord_ϵ三歧... apply Ord_ϵ良基...
  - intros H. induction (正则 α) as [α _ IH].
    destruct (ϵ良序传递_二分 H) as [[β ->]| ->]; constructor.
    + apply IH. zf. apply ϵ良序传递_传递类 with β⁺...
    + intros β βα. apply IH... apply ϵ良序传递_传递类 with α...
Qed.

End Ordinal.
