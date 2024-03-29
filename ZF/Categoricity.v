(** Coq coding by choukh, May 2022 **)

From ZF Require Import Basic Embedding Universe.

(*** 范畴性 ***)

(** 等势模型 **)
Section Equipotent.
Variable 𝓜 𝓝 : ZF.
Notation i := (i 𝓝).
Notation j := (j 𝓜).

Variable f : 𝓜 → 𝓝.
Variable g : 𝓝 → 𝓜.
Variable fg : ∀ a, f (g a) = a.
Variable gf : ∀ x, g (f x) = x.

Theorem 等势模型同构 : 𝓜 ≅ 𝓝.
Proof.
  destruct (相似的完全性三歧 𝓜 𝓝) as [H|[[l[a s]]|[r[x s]]]].
  - apply H.
  - exfalso.
    set (a ∩ₚ (λ b, b ∉ f (j b))) as b.
    set (i (g b)) as c.
    assert (ca: c ∈ a) by apply s, i值域, l.
    assert (H: c ∈ b ↔ c ∈ a ∧ c ∉ f (j c)). unfold b. now rewrite 分离.
    unfold c in H at 4. rewrite ji, fg in H. 2:apply l.
    intuition.
  - exfalso.
    set (x ∩ₚ (λ y, y ∉ g (i y))) as y.
    set (j (f y)) as z.
    assert (zx: z ∈ x) by apply s, j定义域, r.
    assert (H: z ∈ y ↔ z ∈ x ∧ z ∉ g (i z)). unfold y. now rewrite 分离.
    unfold z in H at 4. rewrite ij, gf in H. 2:apply r.
    intuition.
Qed.

End Equipotent.

(** 极小模型 **)
Section Minimal.
Variable 𝓜 𝓝 : ZF.
Arguments 𝕯 : clear implicits.
Arguments 𝕹 : clear implicits.

Theorem 极小模型同构 : ZFₙ 0 𝓜 → ZFₙ 0 𝓝 → 𝓜 ≅ 𝓝.
Proof.
  intros minM%ZFₙO minN%ZFₙO.
  destruct (相似的完全性三歧 𝓜 𝓝) as [H|[[l[a s]]|[r[x s]]]].
  - apply H.
  - exfalso. apply minN. exists a.
    apply (@集化值域是宇宙 𝓝 𝓜), s.
  - exfalso. apply minM. exists x.
    apply 集化定义域是宇宙, s.
Qed.

End Minimal.

(** 有穷序数宇宙模型 **)
Section ZFsn.
Variable 𝓜 𝓝 : ZF.
Notation i := (i 𝓝).
Notation j := (j 𝓜).

Theorem 有穷序数宇宙模型同构 n : ZFₙ n 𝓜 → ZFₙ n 𝓝 → 𝓜 ≅ 𝓝.
Proof.
  intros Mn Nn. destruct n. apply 极小模型同构; trivial.
  destruct (相似的完全性三歧 𝓜 𝓝) as [H|[[l[a s]]|[r[x s]]]].
  - apply H.
  - exfalso. apply ZFₙS in Mn as [u [U [H _]]].
    apply Nn. apply 等级S. exists a. split.
    + apply (@集化值域是宇宙 𝓝 𝓜), s.
    + exists (i u). split. now apply s, i值域.
      assert (u ≈ i u) by apply i规范, l. split.
      * apply (相似保宇宙 (x:=u)); auto.
      * apply (相似保宇宙等级 (x:=u)); auto.
  - exfalso. apply ZFₙS in Nn as [u [U [H _]]].
    apply Mn. apply 等级S. exists x. split.
    + apply 集化定义域是宇宙, s.
    + exists (j u). split. now apply s, j定义域.
      assert (u ≈ j u) by apply 相似的对称性, j规范, r. split.
      * apply (相似保宇宙 (x:=u)); auto.
      * apply (相似保宇宙等级 (x:=u)); auto.
Qed.

End ZFsn.
