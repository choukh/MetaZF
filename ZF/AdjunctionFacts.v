(** Coq coding by choukh, May 2022 **)

From ZF Require Export Basic.

(** 关于并入的引理 **)
Section AdjunctionFacts.
Context {𝓜 : ZF}.
Implicit Type a b x y z : 𝓜.

Lemma 并入之并 a b : ⋃ (a ⨮ b) = a ∪ ⋃b.
Proof.
  apply 外延; intros x xu.
  - apply 并集 in xu as [y [xy yu]].
    apply 并入 in yu as [->|].
    apply 二元并. auto.
    apply 二元并. right. apply 并集. eauto.
  - apply 二元并 in xu as []; apply 并集.
    + exists a. split. auto. apply 并入. auto.
    + apply 并集 in H as [y [xy yb]].
      exists y. split. auto. apply 并入. auto.
Qed.

Lemma 分离掉再并回去 a b : a ∈ b → a ⨮ b ∩ₚ (λ x, x ≠ a) = b.
Proof.
  intros ab. apply 外延; intros x X.
  - apply 并入 in X as [->|[xb neq]%分离]; auto.
  - 排中 (x = a) as [->|]; apply 并入. auto. right. now apply 分离.
Qed.

Lemma 并入之幂 a b : 𝒫 (a ⨮ b) = (λ x, a ⨮ x)[𝒫 b] ∪ 𝒫 b.
Proof.
  apply 外延; intros x X.
  - apply 幂集 in X. 排中 (a ∈ x).
    + apply 二元并. left. apply 函数式替代.
      exists (x ∩ₚ (λ x, x ≠ a)). split.
      * apply 幂集. intros y [yx neq]%分离.
        apply X, 并入 in yx as []; congruence.
      * now apply 分离掉再并回去.
    + apply 二元并. right. apply 幂集.
      intros y yx. apply X in yx as yu.
      apply 并入 in yu as [->|]; congruence.
  - apply 幂集. intros y yx. apply 二元并 in X as [X|X].
    + apply 函数式替代 in X as [z [zb%幂集 <-]].
      apply 并入 in yx as [->|]; apply 并入; auto.
    + apply 幂集 in X. apply 并入. auto.
Qed.

(* a在R中没定义的时候 (𝓕 R a) 还是一个集合, 所以反向不成立 *)
Lemma 并入之替代 R a b : 函数性 R → R @ (a ⨮ b) ⊆ (𝓕 R a) ⨮ (R @ b).
Proof.
  intros Fun y Y.
  apply 替代 in Y as [x [[->|xb]%并入 Rxy]]; trivial; apply 并入.
  - left. apply 函数化 in Rxy; auto.
  - right. apply 替代; trivial. now exists x.
Qed.

End AdjunctionFacts.
