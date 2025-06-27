import Mathlib
/-! Question:
6. Let $K$ be a field of characteristic 0 and let $\varepsilon \in \bar{K}$ be a root of unity $\left(\varepsilon^{n}=1\right.$ for some $n>0)$. Show that $K(\varepsilon)$ is Galois over $K$ and that $\operatorname{Gal}(K(\varepsilon): K)$ is abelian.
-/
open IntermediateField IsPrimitiveRoot IsCyclotomicExtension

variable {K : Type*} {n : ℕ+} [Field K] (ε : AlgebraicClosure K) (pow : ε ^ n.1 = 1)
include pow
/--$\varepsilon$ is of finite order since it's a root of $x ^ n = 1$. Let $d$ be the order of $\varepsilon$.-/
noncomputable def d : ℕ+ := ⟨orderOf ε, orderOf_pos_iff.mpr (isOfFinOrder_iff_pow_eq_one.mpr ⟨n.1, n.2, pow⟩)⟩

/--Then $K(\varepsilon)$ is a cyclotomic extension of $K$ of order $d$.-/
instance : IsCyclotomicExtension {d ε pow} K K⟮ε⟯ := by 
  have hd := (iff_def ε (d ε pow)).mpr ⟨pow_orderOf_eq_one ε, fun _ h ↦ orderOf_dvd_of_pow_eq_one h⟩
  have : IsCyclotomicExtension {d ε pow} K K⟮ε⟯.toSubalgebra := by 
    rw [adjoin_simple_toSubalgebra_of_integral (Algebra.IsIntegral.isIntegral ε)]
    exact (adjoin_isCyclotomicExtension K) hd
  exact this

/--Thus $K(\varepsilon)$ is Galois over $K$.-/
instance : IsGalois K K⟮ε⟯ := (isGalois (d ε pow) K K⟮ε⟯)

/--And $Gal(K(\varepsilon):K)$ is isomorphic to $\Z_d^{\times}$, so it's abelian.-/
noncomputable instance : CommGroup (K⟮ε⟯ ≃ₐ[K] K⟮ε⟯) := Aut.commGroup (n := d ε pow) K (L := K⟮ε⟯)

/-! Informal proof:

$\varepsilon$ is of finite order since it's a root of $x ^ n = 1$. Let $d$ be the order of $\varepsilon$.
Then $K(\varepsilon)$ is a cyclotomic extension of $K$ of order $d$.
Thus $K(\varepsilon)$ is Galois over $K$.
And $Gal(K(\varepsilon):K)$ is isomorphic to $\Z_d^{\times}$, so it's abelian.
-/
