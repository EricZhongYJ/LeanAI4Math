import Mathlib
/-! Question:
1. Show that $p(x)=x^{3}+9 x+6$ is irreducible in $\mathbb{Q}[x]$. Let $\theta$ be a root of $p(x)$. Find the inverse of $1+\theta$ in $\mathbb{Q}(\theta)$.
-/
import MIL.common

open Polynomial

noncomputable def p : Polynomial ℚ :=  X^3 + 9 * X + C 6

-- First of all, we try to prove that p is irreducible over ℤ[X] with Eisenstein criterion.

-- We prove a lemma we need to use in Eisenstein criterion that p is primitive.
-- And the prove is some trivial calculation.
lemma p_ℤ_IsPrimitive : (X^3 + 9 * X + C (6 : ℤ)).IsPrimitive := by
  intro r hr
  have dvd: r ∣ (X^3 + 9 * X + C (6 : ℤ)).coeff 3 := by
    apply (Polynomial.C_dvd_iff_dvd_coeff r (X^3 + 9 * X + C (6 : ℤ))).mp hr 3
  have : (X ^ 3 + 9 * X + C (6:ℤ)).coeff 3 = 1 := by
    simp
    apply coeff_X_of_ne_one
    norm_num
  rw [this] at dvd
  exact isUnit_of_dvd_one dvd

-- Here is the main body that we try to prove that p is irreducible over ℤ[X] with Eisenstein criterion.
lemma p_ℤ_irreducible : Irreducible (X^3 + 9 * X + C (6 : ℤ)) := by
  -- Here we try to prove that p satisfies the condition of coefficient in eisenstein criterion.
  have pIsEis : Polynomial.IsEisensteinAt (X^3 + 9 * X + C (6 : ℤ)) (Ideal.span {3}):= by
    constructor
    -- The case of leading coefficient.
    · have : (X^3 + 9 * X + C (6 : ℤ)).leadingCoeff = (X^3 + 9 * X + C (6 : ℤ)).coeff (X^3 + 9 * X + C (6 : ℤ)).natDegree := by apply Polynomial.coeff_natDegree
      rw [this]
      have : ( X ^ 3 + 9 * X + C (6:ℤ)).natDegree = 3 := by
        compute_degree
        · norm_num
        · norm_num
      rw[this]
      have : (X ^ 3 + 9 * X + C (6:ℤ)).coeff 3 = 1 := by
        simp
        refine coeff_X_of_ne_one ?hn
        norm_num
      rw [this]
      intro h
      have : 3 ∣ (1:ℤ) := by apply Ideal.mem_span_singleton.mp h
      norm_num at this
    -- The case of coefficient apart from the leading one and the constant.
    · intro n hn
      have : ( X ^ 3 + 9 * X + C (6:ℤ)).natDegree = 3 := by
        compute_degree
        · norm_num
        · norm_num
      rw [this] at hn
      interval_cases n
      · simp
        have : 2 ∣ (6 : ℤ) := by norm_num
        apply Ideal.mem_span_singleton.mpr
        norm_num
      · simp
        have : 3 ∣ (9 : ℤ) := by norm_num
        apply Ideal.mem_span_singleton.mpr
        norm_num
      · have : (X ^ 3 + 9 * X + C (6 : ℤ)).coeff 2 = 0 := by
          simp
          apply coeff_X_of_ne_one
          norm_num
        rw [this]
        exact Submodule.zero_mem (Ideal.span {3})
    -- The case of constant.
    · simp
      intro h
      have : Ideal.span {(3 : ℤ)} ^ 2 = Ideal.span {(9 : ℤ)} := by apply Ideal.span_singleton_pow
      rw [this] at h
      have : 9 ∣ (6 : ℤ) := by apply Ideal.mem_span_singleton.mp h
      norm_num at this
  -- We try to prove that the ideal we choose (Ideal.span {(3:ℤ)}) is a prime ideal.
  have hprime : (Ideal.span {(3:ℤ)}).IsPrime := by
    have : (3 : ℤ) ≠ 0 := by norm_cast
    apply (Ideal.span_singleton_prime this).mpr
    exact Int.prime_three
  -- Using the Isprimitive lemma we have just proved.
  have hu : (X^3 + 9 * X + C (6 : ℤ)).IsPrimitive := by
    exact p_ℤ_IsPrimitive
  -- Verify that the natdegree of p is positive.
  have hfd0 : 0 < (X^3 + 9 * X + C (6 : ℤ)).natDegree := by
    have : (X^3 + 9 * X + C (6 : ℤ)).natDegree = 3 := by
        compute_degree
        · norm_num
        · norm_num
    rw[this];simp
  -- Next, we use eisenstein criterion and prove the case that p is a polynomial over ℤ[X].
  apply Polynomial.IsEisensteinAt.irreducible pIsEis hprime hu hfd0

-- Finally, we cast p from ℤ[X] to ℚ[X] and we know the irreducibility keeps getting the irreducibility of p over ℚ[X].
lemma p_irreducible : Irreducible p := by
  rw [p]
  have irreducible : Irreducible (map (Int.castRingHom ℚ) (X ^ 3 + 9 * X + C 6)) := by
    apply (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast p_ℤ_IsPrimitive).mp p_ℤ_irreducible
  simp at irreducible
  exact irreducible

-- Prove that ((θ ^ 2 - θ + 10) / 4) is the inverse of (1 + θ) in ℚ[θ] with some calculation.
lemma inverse_of_1_add_θ (θ : ℚ) (h : θ ^ 3 + 9 * θ + 6 = 0) : (1 + θ) * ((θ ^ 2 - θ + 10) / 4) = 1 := by
  rw [← mul_div_assoc]
  have cal1 : (1 + θ) * (θ ^ 2 - θ + 10) = (θ ^ 3 + 9 * θ + 6) + 4 := by ring
  rw [cal1, h]
  norm_num

/-! Informal proof:
**Using the Eisenstein Criterion**: To apply Eisenstein's Criterion for irreducibility, we first note that the polynomial $p(x) = x^3 + 9x + 6$ can be examined with prime number $3$:
- The constant term $6$ is divisible by $3$.
- The linear coefficient $9$ is also divisible by $3$.
- The leading coefficient $1$ (of $x^3$) is not divisible by $3$.
- The constant term $6$ is not divisible by $3^2 = 9$.
Since all these conditions are satisfied, by the Eisenstein Criterion, $p(x)$ is irreducible over $\mathbb{Q}$.
**Finding the Inverse**: Knowing $\theta$ is a root of $p(x)$, we have $\theta^3 + 9\theta + 6 = 0$. We want to find an expression $\frac{a\theta^2 + b\theta + c}{d}$ such that:
$$(1 + \theta) \left(\frac{a\theta^2 + b\theta + c}{d}\right) = 1$$
To simplify and find the coefficients $a$, $b$, $c$, $d$, consider:
- We want $(1 + \theta)(a\theta^2 + b\theta + c) = d$.
- Expanding and collecting like terms, equate it to the constant $d$, considering $\theta^3 = -9\theta - 6$ to reduce higher powers of $\theta$.
Plugging in and reducing using $\theta^3 + 9\theta + 6 = 0$, we find:
- $a = 1$, $b = -1$, $c = 10$, and $d = 4$.
Thus, the inverse of $1 + \theta$ in $\mathbb{Q}(\theta)$ is:
$$\frac{\theta^2 - \theta + 10}{4}$$

-/
