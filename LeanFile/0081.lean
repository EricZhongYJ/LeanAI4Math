import Mathlib
/-! Question:
3.2.8. 设 $E$ 为 $x^{8}-1$ 在 $\mathbb{Q}$ 上的分裂域. 求 $[E: \mathbb{Q}]$.
-/
import Mathlib.Tactic

/- Let E be the splitting field of x⁸-1 over ℚ. Compute [ E : ℚ]-/

-- by definition, E is the 8th cyclotomic field. We show that [E : ℚ]=4
example {E : Type*} [Field E] [Algebra ℚ E] [IsCyclotomicExtension {8} ℚ E] : Module.finrank ℚ E = 4 := by
  have le : 0 < 8 := by exact Nat.zero_lt_succ 7
  -- cyclotomic polynomials over ℚ are irreducible
  have irre := Polynomial.cyclotomic.irreducible_rat le
  have eq1 := @IsCyclotomicExtension.finrank 8 ℚ E _ _ _ _ _ irre
  rw [eq1]
  exact rfl

/-! Informal proof:
nth cyclotomic field over Q has dimension phi(n), where phi is the Euler's totient function
-/
