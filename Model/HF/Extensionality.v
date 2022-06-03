(** Coq coding by choukh, June 2022 **)

Require Import HF.

Section Decidability.
Context {𝓜 : HF}.
Implicit Types x y z : 𝓜.

Instance 判定为空 x : 可判定 (∅ = x).
Proof. hf_ind x; hf. Qed.

Instance 判定有空 x : 可判定 (∅ ∈ x).
Proof.
  hf_ind x; [hf|].
  intros x y _ [|]; 判定 (∅ = x) as [->|]; hf.
Qed.

Instance 判定含于空 x : 可判定 (x ⊆ ∅).
Proof. hf_ind x; hf. Qed.

Lemma 判定子集扩张 x y z :
  可判定 (x ∈ z) → 可判定 (y ⊆ z) → 可判定 (x ▸ y ⊆ z).
Proof. intros [] []; hf. Qed.

Lemma 判定成员扩张 x y z :
  可判定 (x = y) → 可判定 (x ∈ z) → 可判定 (x ∈ y ▸ z).
Proof. intros [] []; hf. Qed.

Lemma 差分存在 x y :
  (∀ z, 可判定 (x ∈ z)) →
  (∀ z, 可判定 (x = z)) →
  x ∈ y → ∃ a, x ▸ a = y ∧ x ∉ a.
Proof.
  intros H1 H2. hf_ind y.
  - hf. 
  - intros y z _ IH H. 判定 (x ∈ z) as [xz|xz].
    + destruct (IH xz) as [a [<- xa]].
      assert (y ∈ y ▸ x ▸ a) by hf. 
      判定 (x = y) as [<-|xy].
      * exists a. hf.
      * exists (y ▸ a). split. hf. contradict xy. hf.
    + exists z. hf.
Qed.

Lemma 判定外延 x y:
  可判定 (x ⊆ y) ∧ 可判定 (y ⊆ x) ∧
  可判定 (x ∈ y) ∧ 可判定 (y ∈ x) ∧
  (x ⊆ y → y ⊆ x → x = y) ∧ 可判定 (x = y).
Proof.
  revert y. hf_ind x.
  - intuition; hf.
  - intros a x IHa IHx y. hf_ind y.
    + intuition; hf.
    + intros b y IHb IHy.
      assert (H1: 可判定 (a ▸ x ⊆ b ▸ y)). apply 判定子集扩张. apply IHa. apply IHx.
      assert (H2: 可判定 (b ▸ y ⊆ a ▸ x)). apply 判定子集扩张. apply IHb. apply IHy.
      assert (H3: a ▸ x ⊆ b ▸ y → b ▸ y ⊆ a ▸ x → a ▸ x = b ▸ y). {
        intros A B.
        assert (可判定 (a ∈ x)) as [ax|nax] by apply IHa.
        - rewrite ax in *. now apply IHx.
        - destruct (@差分存在 a (b ▸ y)) as [c [eq nau]].
          apply IHa. apply IHa. apply A; hf.
          rewrite <- eq in *. f_equal. apply IHx; hf.
      }
      repeat split. 
      * apply H1.
      * apply H2.
      * apply 判定成员扩张. apply IHb. apply IHy.
      * apply 判定成员扩张. apply 判定相等对称, IHa. apply IHx.
      * apply H3.
      * { destruct H1 as [H1|H1].
          - destruct H2 as [H2|H2].
            + left. now apply H3.
            + right. intros eq. apply H2. congruence.
          - right. intros eq. apply H1. congruence. }
Qed.

End Decidability.
