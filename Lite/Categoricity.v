(** Coq coding by choukh, May 2022 **)

Require Import Lite.Basic Lite.Embedding.

(* 范畴性 *)
Section Categoricity.
Variable 𝓜 𝓝 : ZF.
Implicit Type x y z : 𝓜.
Implicit Type a b c : 𝓝.
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
    unfold c in H at 4. rewrite ji, fg in H. 2: apply l.
    intuition.
  - exfalso.
    set (x ∩ₚ (λ y, y ∉ g (i y))) as y.
    set (j (f y)) as z.
    assert (zx: z ∈ x) by apply s, j定义域, r.
    assert (H: z ∈ y ↔ z ∈ x ∧ z ∉ g (i z)). unfold y. now rewrite 分离.
    unfold z in H at 4. rewrite ij, gf in H. 2: apply r.
    intuition.
Qed.

End Categoricity.
