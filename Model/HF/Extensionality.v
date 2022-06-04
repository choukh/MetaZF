(** Coq coding by choukh, June 2022 **)

Require Import HF.

(** 外延定理 **)
Section Extensionality.
Context {𝓜 : HF}.
Implicit Types x y z : 𝓜.

Instance 为空可判定 x : 可判定 (∅ = x).
Proof. hf_ind x; hf. Qed.

Instance 有空可判定 x : 可判定 (∅ ∈ x).
Proof.
  hf_ind x; [hf|].
  intros x y _ [|]; 判定 (∅ = x) as [->|]; hf.
Qed.

Instance 含于空可判定 x : 可判定 (x ⊆ ∅).
Proof. hf_ind x; hf. Qed.

Lemma 子集扩张可判定 x y z :
  可判定 (x ∈ z) → 可判定 (y ⊆ z) → 可判定 (x ⨮ y ⊆ z).
Proof. intros [] []; hf. Qed.

Lemma 成员扩张可判定 x y z :
  可判定 (x = y) → 可判定 (x ∈ z) → 可判定 (x ∈ y ⨮ z).
Proof. intros [] []; hf. Qed.

Lemma 差分强存在 x y :
  (∀ z, 可判定 (x ∈ z)) →
  (∀ z, 可判定 (x = z)) →
  x ∈ y → Σ a, y = x ⨮ a ∧ x ∉ a.
Proof.
  intros H1 H2. hf_ind y.
  - hf. 
  - intros y z _ IH H. 判定 (x ∈ z) as [xz|xz].
    + destruct (IH xz) as [a [-> xa]].
      assert (y ∈ y ⨮ x ⨮ a) by hf. 
      判定 (x = y) as [<-|xy].
      * exists a. hf.
      * exists (y ⨮ a). split. hf. contradict xy. hf.
    + exists z. hf.
Qed.

Lemma 外延可判定 x y:
  可判定 (x ⊆ y) * 可判定 (y ⊆ x) *
  可判定 (x ∈ y) * 可判定 (y ∈ x) *
  (x ⊆ y → y ⊆ x → x = y) * 可判定 (x = y).
Proof.
  revert y. hf_ind x.
  - intuition; hf.
  - intros a x IHa IHx y. hf_ind y.
    + intuition; hf.
    + intros b y IHb IHy.
      assert (H1: 可判定 (a ⨮ x ⊆ b ⨮ y)). apply 子集扩张可判定. apply IHa. apply IHx.
      assert (H2: 可判定 (b ⨮ y ⊆ a ⨮ x)). apply 子集扩张可判定. apply IHb. apply IHy.
      assert (H3: a ⨮ x ⊆ b ⨮ y → b ⨮ y ⊆ a ⨮ x → a ⨮ x = b ⨮ y). {
        intros A B.
        assert (可判定 (a ∈ x)) as [ax|nax] by apply IHa.
        - rewrite ax in *. now apply IHx.
        - destruct (@差分强存在 a (b ⨮ y)) as [c [eq nau]].
          apply IHa. apply IHa. apply A; hf.
          rewrite eq in *. f_equal. apply IHx; hf.
      }
      repeat split. 
      * apply H1.
      * apply H2.
      * apply 成员扩张可判定. apply IHb. apply IHy.
      * apply 成员扩张可判定. apply 相等可判定_对称, IHa. apply IHx.
      * apply H3.
      * { destruct H1 as [H1|H1].
          - destruct H2 as [H2|H2].
            + left. now apply H3.
            + right. intros eq. apply H2. congruence.
          - right. intros eq. apply H1. congruence. }
Qed.

Theorem 外延 x y : (∀ z, z ∈ x ↔ z ∈ y) → x = y.
Proof. intros H. apply 外延可判定; hf.  Qed.

Global Instance HF可识别 : 可识别 𝓜.
Proof. intros x y. apply 外延可判定. Qed.

Global Instance 子集关系可判定 x y : 可判定 (x ⊆ y).
Proof. apply 外延可判定. Qed.

Fact 成员关系可判定 x y : 可判定 (x ∈ y).
Proof. apply 外延可判定. Qed.

Lemma 差分 x y : x ∈ y → Σ z, y = x ⨮ z ∧ x ∉ z.
Proof. apply 差分强存在; auto. Qed.

Global Instance 谓词见证可判定 x P :
  (∀ x, 可判定 (P x)) → 可判定 (∃ z ∈ x, P z).
Proof.
  intros H. hf_ind x.
  - right. intros [z [z0 _]]. hf.
  - intros x y _ [IH|IH].
    + left. destruct IH as [z [zy Pz]]. exists z. hf.
    + 判定 (P x) as [Px|nPx].
      * left. exists x. hf. 
      * right. intros [z [zxy Pz]]. apply IH. hf.
Qed.

Global Instance 谓词全称可判定 x P :
  (∀ x, 可判定 (P x)) → 可判定 (∀ z ∈ x, P z).
Proof.
  intros H. hf_ind x.
  - left. intros z z0. hf.
  - intros x y _ [IH|IH].
    + 判定 (P x) as [Px|nPx].
      * left. intros z zxy. hf.
      * right. intros A. apply nPx, A. hf.
    + right. intros A. apply IH. intros z zy. apply A. hf.
Qed.

Theorem ϵ归纳 (P : 𝓜 → Type) : (∀ x, (∀ z ∈ x, P z) → P x) → ∀ x, P x.
Proof.
  intros A x. apply A. hf_ind x. hf.
  intros x y IHx IHy z zxy.
  判定 (z = x) as [->|nq]. auto. apply IHy. hf.
Qed.

Ltac ϵ_ind x := pattern x; revert x; apply ϵ归纳.

Lemma ϵ反自反 x : x ∉ x.
Proof. ϵ_ind x. intros x A xx. apply (A x xx xx). Qed.

Fact 无大全集 x : ¬ ∀ y, y ∈ x.
Proof. intros A. specialize (A x). revert A. apply ϵ反自反. Qed.

Lemma ϵ非对称 x y : x ∈ y → y ∉ x.
Proof.
  revert y. ϵ_ind x.
  intros x IH y xy yx. revert xy. now apply IH.
Qed.

Lemma 并单射 x y : x ⨮ x = y ⨮ y → x = y.
Proof.
  intros eq.
  assert (xyy: x ∈ y ⨮ y) by (rewrite <- eq; hf).
  assert (yxx: y ∈ x ⨮ x) by (rewrite eq; hf).
  apply 属 in xyy as [->|xyy]. reflexivity.
  apply 属 in yxx as [->|yxx]. reflexivity.
  contradict (ϵ非对称 xyy yxx).
Qed.

End Extensionality.

Tactic Notation "外延" "as" simple_intropattern(i) := apply 外延; intros i.
Ltac ϵ_ind x := pattern x; revert x; apply ϵ归纳.
