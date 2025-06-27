import Mathlib
/-! Question:
12. Construct polynomials of arbitrarily large degree, which are irreducible in $\mathbb{Q}[x]$.
-/

open Polynomial

/- If $n > 1$, then the degree of $p(x)=x^n-x-1$ is n. -/
lemma Polynomial.degree_selmer {n : ℕ} (hn : 1 < n) : (X ^ n - X - 1 : ℚ[X]).degree = n := by
  rw [degree_eq_of_le_of_coeff_ne_zero]
  . simp_rw [degree_le_iff_coeff_zero, Nat.cast_lt]
    rintro m hnm
    rw [coeff_sub, coeff_sub, coeff_X_pow, if_neg (by omega), coeff_X, if_neg (by omega),
      coeff_one, if_neg (by omega), sub_zero, sub_zero]
  . rw [coeff_sub, coeff_sub, coeff_X_pow, if_pos (by omega), coeff_X_of_ne_one (by omega),
      coeff_one, if_neg (by omega), sub_zero, sub_zero]
    norm_num

/- **Question:** Construct polynomials of arbitrarily large degree, which are irreducible in $\mathbb{Q}[x]$.-/
theorem exists_irreducible_rat_poly_degree_ge (n : ℕ) : ∃ p : ℚ[X], Irreducible p ∧ n ≤ p.degree := by
  -- **Solution:** It is well known that Selmer Polynomial $p(x)=x^n-x-1$ is irreducible in  $\mathbb{Q}[x]$.
  -- And if $n>1$, the degree of $p(x)$ is exactly $n$.
  -- Hence, for any given natural number $n$.
  rcases le_or_lt n 1 with hn1 | hn1
  -- If $n \leq 1$, then we choose $p(x)=x^2-x-1$ which is irreducible and degree of $p(x)$ is greater than $n$.
  . have := X_pow_sub_X_sub_one_irreducible_rat (show 2 ≠ 1 by norm_num)
    refine Exists.intro _ ⟨this, ?_⟩
    rw [degree_selmer (by norm_num)]
    norm_cast
    omega
  -- Otherwise, if $n > 1$, then we choose $p(x)=x^n-x-1$ which is irreducible and degree of $p(x)$ is greater than or equal $n$.
  have := X_pow_sub_X_sub_one_irreducible_rat (show n ≠ 1 by omega)
  refine Exists.intro _ ⟨this, ?_⟩
  rw [degree_selmer (by omega)]


/-! Informal proof:
**Question:** Construct polynomials of arbitrarily large degree, which are irreducible in $\mathbb{Q}[x]$.
**Solution:** It is well known that Selmer Polynomial $p(x)=x^n-x-1$ is irreducible in  $\mathbb{Q}[x]$. And if $n>1$, the degree of $p(x)$ is exactly $n$.
Hence, for any given natural number $n$.
If $n \leq 1$, then we choose $p(x)=x^2-x-1$ which is irreducible and degree of $p(x)$ is greater than $n$.
Otherwise, if $n > 1$, then we choose $p(x)=x^n-x-1$ which is irreducible and degree of $p(x)$ is greater than or equal $n$.
-/
