import Mathlib
/-! Question:
 证明 $x^2+1$ 在四元数体 $H$ 内有无穷多个根。
-/

-- Q: Prove that $x^2+1$ has infinite roots in the quaternion $H$.
-- A: Define $f : [0,2π) → ℍ,  f(θ) := i \cosθ + j \sinθ$. Then ∀ θ, 
-- $$
-- \begin{aligned}
-- &f(θ)^2+1\\
-- =&(i\cos\theta + j\sin\theta)^2+1\\
-- =&-\cos^2\theta + ij\cos\theta\sin\theta + ji\cos\theta\sin\theta - \sin^2\theta +1\\
-- =& 0
-- \end{aligned}
-- $$
-- Therefore, $f(θ)$ is a root of $x^2+1$ in $ℍ$ for all $θ$. Since $f$ is injective(proved by the lemma behind) and its domain is an infinite set, there are infinite roots of $x^2+1$ in $ℍ$.

-- lemma: if $x, y ∈ [0, 2π)$ and $\cos x = \cos y$, $\sin x = \sin y$, then $x=y$
-- proof: $\cos x = \cos y$ imples that $y = 2kπ + x ∨ y = 2kπ - x$. 
--   -> Case 1: If $y = 2kπ + x$. We can use $x ≥ 0$ and $y < 2π$ to prove that $x = y$.
--   -> Case 2: If $y = 2kπ - x$. $\sin x = \sin y$ imples that $y = 2lπ + x ∨ y = (2l+1)π - x$.
--     -> Case 2.1: $y = 2lπ + x$. We can use $x ≥ 0$ and $y < 2π$ to prove that $x = y$.
--     -> Case 2.2: $y = 2(l+1)π - x$. We have $2kπ - x = (2l+1)π - x$, followed by $2k = 2l + 1$, which gives an contradiction.
lemma cos_eq_cos_sin_eq_sin_imp {x y : ℝ} {hx : 0 ≤ x ∧ x < 2 * Real.pi} {hy : 0 ≤ y ∧ y < 2 * Real.pi}
  (h_cos : Real.cos x = Real.cos y) (h_sin : Real.sin x = Real.sin y) : x = y := by
  rw [Real.cos_eq_cos_iff] at h_cos
  rw [Real.sin_eq_sin_iff] at h_sin
  rcases h_cos with ⟨k, h_cos₁ | h_cos₂⟩
  -- case 1: $\cos x = \cos y$ -> $y = 2kπ + x$.
  · rcases h_sin with ⟨l, h_sin⟩
    · have ne_one_lek: ¬1 ≤ (k : ℝ) := by
        by_contra con
        have : y ≥ 2 * Real.pi := by
          rw [h_cos₁, ← add_zero (2 * Real.pi)]; apply add_le_add
          · apply mul_le_mul; simp; exact con; rfl; exact Real.pi_nonneg; apply mul_nonneg; linarith; linarith
          · exact hx.1
        linarith
      have ne_kle_neg_one: ¬(k : ℝ) ≤ -1 := by
        by_contra con
        have : y < 0 := by
          rw [h_cos₁, ← sub_self (2 * (k : ℝ) * Real.pi), sub_eq_add_neg]
          have : x < -(2 * ↑k * Real.pi) := by
            rw [mul_comm 2 (k : ℝ), mul_assoc, ← neg_mul]
            apply hx.2.trans_le; rw [le_neg] at con; rw [← one_mul (2 * Real.pi), ← mul_assoc (-(k : ℝ)) 1, mul_one]
            apply mul_le_mul; exact con; simp; simp; exact Real.pi_nonneg; linarith
          linarith
        linarith
      have : k = 0 := by
        have h1 : k < 1 := by
          contrapose! ne_one_lek; norm_cast
        have h2 : -1 < k := by
          contrapose! ne_kle_neg_one; norm_cast
        linarith
      rw [this] at h_cos₁; simp at h_cos₁; exact h_cos₁.symm
  -- case 2: $\cos x = \cos y$ -> $y = 2kπ - x$.
  · rcases h_sin with ⟨l, h_sin₁ | h_sin₂⟩
    -- case 2.1: $\sin x = \sin y$ -> $y = 2lπ + x$. We use $x ≥ 0$ and $y < 2π$ to prove that $x = y$
    · have ne_one_lek: ¬1 ≤ (l : ℝ) := by
        by_contra con
        have : y ≥ 2 * Real.pi := by
          rw [h_sin₁, ← add_zero (2 * Real.pi)]; apply add_le_add
          · apply mul_le_mul; simp; exact con; rfl; exact Real.pi_nonneg; apply mul_nonneg; linarith; linarith
          · exact hx.1
        linarith
      have ne_kle_neg_one: ¬(l : ℝ) ≤ -1 := by
        by_contra con
        have : y < 0 := by
          rw [h_sin₁, ← sub_self (2 * (l : ℝ) * Real.pi), sub_eq_add_neg]
          have : x < -(2 * ↑l * Real.pi) := by
            rw [mul_comm 2 (l : ℝ), mul_assoc, ← neg_mul]
            apply hx.2.trans_le; rw [le_neg] at con; rw [← one_mul (2 * Real.pi), ← mul_assoc (-(l : ℝ)) 1, mul_one]
            apply mul_le_mul; exact con; simp; simp; exact Real.pi_nonneg; linarith
          linarith
        linarith
      have : l = 0 := by
        have h1 : l < 1 := by
          contrapose! ne_one_lek; norm_cast
        have h2 : -1 < l := by
          contrapose! ne_kle_neg_one; norm_cast
        linarith
      rw [this] at h_sin₁; simp at h_sin₁; exact h_sin₁.symm
    -- case 2.2: $\sin x = \sin y$ -> $y = (2l+1)π - x$. 
    · rw [h_cos₂, sub_left_inj, mul_eq_mul_right_iff] at h_sin₂;
      rcases h_sin₂ with h₁ | h₂
      · norm_cast at h₁
        have h_even : Even (2 * k) := even_two_mul k
        have h_odd : Odd (2 * l + 1) := odd_two_mul_add_one l
        rw [h₁] at h_even; rw [← Int.not_even_iff_odd] at h_odd
        contradiction
      · have : Real.pi ≠ 0 := Real.pi_ne_zero
        contradiction


theorem infinite_roots_in_H_for_x_squared_plus_one :
  Set.Infinite {x: Quaternion ℝ | x * x + ⟨1,0,0,0⟩ = 0} := by
  -- define function $f(θ) = i \cosθ + j \sinθ$
  let f : {θ: ℝ | 0 ≤ θ ∧ θ < 2 * Real.pi } → Quaternion ℝ := λ θ => ⟨ 0, (Real.cos θ), (Real.sin θ), 0 ⟩

  -- prove that $f(θ)$ is a root for all θ
  have hf: ∀ θ, f θ ∈ {x: Quaternion ℝ | x * x + 1 = 0} := by
    intro θ
    simp [f]
    let r : Quaternion ℝ := QuaternionAlgebra.mk 0 (Real.cos θ) (Real.sin θ) 0
    apply Quaternion.ext
    simp
    ring_nf
    rw [sub_eq_neg_add, ← neg_add]
    simp;simp;simp;simp
    rw [mul_comm]
    simp

  -- prove that $f$ is an injection
  have h_inj : Function.Injective f := by
    intro x y h_eq
    rw [Quaternion.ext_iff] at h_eq
    dsimp only at h_eq
    rcases h_eq with ⟨_,h1, h2,_⟩
    apply Subtype.ext
    apply cos_eq_cos_sin_eq_sin_imp h1 h2
    exact x.property; exact y.property

  -- prove that the domain of $f$ is an infinite set
  have h_inf : Infinite {θ | 0 ≤ θ ∧ θ < 2 * Real.pi} := by
    rw [Set.infinite_coe_iff]
    -- define $g(n)=\frac{1}{n + 1}$
    let g : ℕ → ℝ := λ n => 1 / (n + 1)
    -- prove that $g$ is an injection
    have g_inj : Function.Injective g := by
      intro n m; unfold g; simp
    -- prove that $g(n) ∈ [0, 2π)$
    have hg : ∀ n, g n ∈ {θ | 0 ≤ θ ∧ θ < 2 * Real.pi} := by
      simp
      intro n
      constructor
      · unfold g; apply div_nonneg; simp; exact add_nonneg (Nat.cast_nonneg n) zero_le_one
      · have h₁ : 1 / (↑n + 1 : ℝ) ≤ 1 := by
          rw [← inv_eq_one_div]
          apply inv_le_one_of_one_le₀
          rw [← zero_add 1, ← add_assoc, add_zero, add_le_add_iff_right]
          exact Nat.cast_nonneg n
        have h₂ : (1 : ℝ) < 2 * Real.pi := by
          linarith [Real.pi_gt_three]
        exact h₁.trans_lt h₂
    -- Since $g$ is an injection from an infinite set to $[0, 2π)$, $[0, 2π)$ is infinite
    exact Set.infinite_of_injective_forall_mem g_inj hg

  -- Since $f$ is an injection from an infinite set to ${x ∈ ℍ | x ^ 2 + 1 = 0}$, there are infinite roots.
  exact Set.infinite_of_injective_forall_mem h_inj hf

/-! Informal proof:
Define $f : [0,2π) → ℍ,  f(θ) := i \cosθ + j \sinθ$. Then ∀ θ, 
$$
\begin{aligned}
&f(θ)^2+1\\
=&(i\cos\theta + j\sin\theta)^2+1\\
=&-\cos^2\theta + ij\cos\theta\sin\theta + ji\cos\theta\sin\theta - \sin^2\theta +1\\
=& 0
\end{aligned}
$$
Therefore, $f(θ)$ is a root of $x^2+1$ in $ℍ$ for all $θ$. Since $f$ is injective(proved by the lemma behind) and its domain is an infinite set, there are infinite roots of $x^2+1$ in $ℍ$.

**Lemma**: if $x, y ∈ [0, 2π)$ and $\cos x = \cos y$, $\sin x = \sin y$, then $x=y$
proof: $\cos x = \cos y$ imples that $y = 2kπ + x ∨ y = 2kπ - x$.
**Case 1**: If $y = 2kπ + x$. We can use $x ≥ 0$ and $y < 2π$ to prove that $x = y$.
**Case 2**: If $y = 2kπ - x$. $\sin x = \sin y$ imples that $y = 2lπ + x ∨ y = (2l+1)π - x$.
-> **Case 2.1**: If $y = 2lπ + x$. We can use $x ≥ 0$ and $y < 2π$ to prove that $x = y$.
->** Case 2.2**: If $y = 2(l+1)π - x$. We have $2kπ - x = (2l+1)π - x$, followed by $2k = 2l + 1$, which gives an contradiction.
-/
