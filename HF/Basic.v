(** Coq coding by choukh, June 2022 **)

Require Export HF.HF Extensionality.

(** 单集与配对 **)
Section SingPair.
Context {𝓜 : HF}.
Implicit Types x y a b : 𝓜.

Lemma 单集 x a : x ∈ {a,} ↔ x = a.
Proof. hf. Qed.

Lemma 单集单射 x y : {x,} = {y,} → x = y.
Proof. intros eq. apply 单集. rewrite <- eq. hf. Qed.

Lemma 配对 x a b : x ∈ {a, b} ↔ x = a ∨ x = b.
Proof. hf. Qed.

Lemma 配对单射 x y a b : {x, y} = {a, b} → x = a ∧ y = b ∨ x = b ∧ y = a.
Proof.
  intros A.
  assert (B: x = a ∨ x = b). apply 配对. rewrite <- A. hf.
  assert (C: y = a ∨ y = b). apply 配对. rewrite <- A. hf.
  assert (D: a = x ∨ a = y). apply 配对. rewrite A. hf.
  assert (E: b = x ∨ b = y). apply 配对. rewrite A. hf.
  firstorder.
Qed.

End SingPair.

(** 二元并 *)
Section BinaryUnion.
Context {𝓜 : HF}.
Implicit Types x y z u : 𝓜.

Lemma 二元并强存在 x y : Σ u, ∀ z, z ∈ u ↔ z ∈ x ∨ z ∈ y.
Proof.
  hf_ind x.
  - exists y. hf.
  - intros x x' _ [u IH]. exists (x ⨮ u). hf.
Qed.

Definition 并 x y := projT1 (二元并强存在 x y).

Fact 二元并 x y z : z ∈ 并 x y ↔ z ∈ x ∨ z ∈ y.
Proof. unfold 并. destruct (二元并强存在 x y); auto. Qed.

End BinaryUnion.
Notation "A ∪ B" := (二元并 A B) (at level 50) : hf_scope.

(** 分离 *)
Section Separation.
Context {𝓜 : HF}.
Implicit Types x y z : 𝓜.
Variable P : 可判定谓词 𝓜.

Lemma 分离强存在 x : Σ y, ∀ z, z ∈ y ↔ z ∈ x ∧ P z.
Proof.
  hf_ind x. 
  - exists ∅. hf.
  - intros x x' _ [y IH]. destruct (谓词判定 P x).
    + exists (x ⨮ y). hf.
    + exists y. hf.
Qed.

Definition 分 x := projT1 (分离强存在 x).

Lemma 分离 x y : y ∈ 分 x ↔ y ∈ x ∧ P y.
Proof. unfold 分. destruct (分离强存在 x); auto. Qed.

End Separation.
Notation "A ∩ₚ P" := (分 A P) (at level 60) : hf_scope.

(** 替代 *)
Section Replacement.
Context {𝓜 : HF}.
Implicit Types x y a b : 𝓜.
Variable f : 𝓜 → 𝓜.

Lemma 替代强存在 a : Σ b, ∀ y, y ∈ b ↔ ∃ x, x ∈ a ∧ f x = y.
Proof.
  hf_ind a. 
  - exists ∅. hf.
  - intros x x' _ [b IH]. exists (f x ⨮ b). hf.
Qed.

Definition 替 x := projT1 (替代强存在 x).

Lemma 替代 a y : y ∈ 替 a ↔ ∃ x, x ∈ a ∧ f x = y.
Proof. unfold 替. destruct (替代强存在 a); auto. Qed.

End Replacement.
Notation "f [ a ]" := (替 f a) (at level 7, format "f [ a ]") : hf_scope.
