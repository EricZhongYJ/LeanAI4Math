import Mathlib
/-! Question:
10. Suppose that $\alpha$ is a real number (which might not be rational), and suppose that it is a root of a polynomial $p \in \mathbb{Q}[x]$; that is, $p(\alpha)=0$. Suppose further that $p$ is irreducible in $\mathbb{Q}[x]$. Prove that $p$ has minimal degree in the set
\[
\{f \in \mathbb{Q}[x]: f(\alpha)=0 \text { and } f \
eq 0\} .
\]
-/

instance canonical_rat_to_real : ℚ →+* ℝ where
    toFun := fun q => q
    map_one' := Rat.cast_one
    map_mul' := fun x y => Rat.cast_mul x y
    map_zero' := Rat.cast_zero
    map_add' := by simp only [Rat.cast_add, implies_true]

example (a : ℝ) (p : Polynomial ℚ) (hp : Polynomial.eval₂ canonical_rat_to_real a p = 0)
 (irr : Irreducible p) (f : Polynomial ℚ) (hf : Polynomial.eval₂ canonical_rat_to_real a f = 0)
 (hn : f ≠ 0) : Polynomial.degree f ≥ Polynomial.degree p := by
    -- To show $\deg f \geqslant \deg p$, it suffices to prove that $p \mid f$.
    have dvd : p ∣ f := by
        -- Since $p$ is irreducible, we have $p \mid f$ or $gcd (p, f) = r \
eq 0 \in \mathbb{Q}$.
        apply (@Irreducible.dvd_iff_not_coprime _ _ _ p f irr).mpr
        intro hyp
        -- Suppose the later case is true, then by Bezout's theorem we have $px + fy = r$.
        rcases exists_gcd_eq_mul_add_mul p f with ⟨x, y, hxy⟩
        rcases (@Polynomial.isUnit_iff _ _ _ (gcd p f)).mp ((gcd_isUnit_iff p f).mpr hyp) with ⟨r, h1, h2⟩
        rw [<- h2] at hxy
        -- Evaluate this at $\alpha$, we obtain a contradiction.
        have eq_zero : Polynomial.eval₂ canonical_rat_to_real a (p * x + f * y) = 0 := by
            simp only [Polynomial.eval₂_add, Polynomial.eval₂_mul, hp, hf, zero_mul, add_zero]
        rw [<- hxy] at eq_zero
        simp only [Polynomial.eval₂_C, eq_ratCast, Rat.cast_eq_zero] at eq_zero
        subst eq_zero
        simp_all only [ne_eq, isUnit_iff_ne_zero, not_true_eq_false]
    exact Polynomial.degree_le_of_dvd dvd hn

/-! Informal proof:
Informal proof: Suppose that $f$ is another polynomial such that $f(\alpha) = 0$. To show $\deg f \geqslant \deg p$, it suffices to prove that $p \mid f$. Since $p$ is irreducible, we have $p \mid f$ or $gcd (p, f) = r \
eq 0 \in \mathbb{Q}$. Suppose the later case is true, then by Bezout's theorem we have $px + fy = r$. Evaluate this at $\alpha$, we obtain a contradiction.
-/
