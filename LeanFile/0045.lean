import Mathlib
/-! Question:
9. Use the Rational Root Theorem 5.6 (applied to $x^{3}-2$ ) to argue that $\sqrt[3]{2}$ is irrational.
-/

/-
Use the Rational Root Theorem 5.6 (applied to $x^3−2$ ) to argue that $\sqrt[3]{2}$ is irrational.
1. First, according to the definition of cube roots, $\sqrt[3]{2}$ is the roots of $x^3-2$
2. Then according to well-known theorem : If $x^n, n > 0$, is integer and is not the $n$-th power
  of an integer, then $x$ is irrational.
3. Sufficient to check $\sqrt[3]{2}$ is not a integeral, actually it $> 1$ and $< 2$, of course it is
 not a integral.
-/
lemma Int.cast_eq {x y: ℤ} (h : (x : ℝ) = (y : ℝ)) : x = y := by
  linarith [Int.cast_le.mp (le_of_eq h), Int.cast_le.mp (ge_of_eq h)]

lemma main : Irrational (2 ^ ((1 : ℝ) / 3)) := by
  set x : ℝ := (2 ^ ((1 : ℝ) / 3))
  --1. First, according to the definition of cube roots, $\sqrt[3]{2}$ is the roots of $x^3-2$
  have eq : x ^ 3 = 2 := by
    rw [← Real.rpow_natCast (2 ^ (1 / 3)) 3]
    simp only [one_div, Nat.cast_ofNat, Nat.ofNat_nonneg, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, Real.rpow_inv_rpow]
  /- 2. Then according to well-known theorem : If $x^n, n > 0$, is integer and is not the $n$-th power
  of an integer, then $x$ is irrational. -/
  apply irrational_nrt_of_notint_nrt (3 : ℕ) (2 : ℕ)
  · simp only [eq, Nat.cast_ofNat, Int.cast_ofNat]
  · /- 3. Sufficient to check $\sqrt[3]{2}$ is not a integeral, actually it $> 1$ and $< 2$, of course it is
  not a integral. -/
    intro ⟨y, hy⟩
    have hy : y ^ 3 = 2 := by
      apply Int.cast_eq
      simp only [Int.cast_pow, Int.cast_ofNat, ← hy, eq]
    by_cases nh : y ≥ 2
    · linarith [hy, (pow_le_pow_left (by linarith) nh 3)]
    · have : 0 ≥ y ^ 3 :=
        Odd.pow_nonpos (Nat.odd_iff.mpr rfl) <| Int.lt_add_one_iff.mp <| lt_of_le_of_ne
         (Int.not_lt.mp nh) fun h ↦ (by rw [h] at hy; norm_num at hy)
      linarith
  · norm_num


/-! Informal proof:
Use the Rational Root Theorem 5.6 (applied to $x^3−2$ ) to argue that $\sqrt[3]{2}$ is irrational.
1. First, according to the definition of cube roots, $\sqrt[3]{2}$ is the roots of $x^3-2$
2. Then according to well-known theorem : If $x^n, n > 0$, is integer and is not the $n$-th power
  of an integer, then $x$ is irrational.
3. Sufficient to check $\sqrt[3]{2}$ is not a integeral, actually it $> 1$ and $< 2$, of course it is
 not a integral.
-/
