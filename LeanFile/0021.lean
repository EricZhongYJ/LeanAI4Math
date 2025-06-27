import Mathlib
/-! Question:
7. Show that an integral basis for the ring of algebraic integers of a number field $L$ is, in particular, a basis for $L$ over $\mathbb{Q}$.
-/
noncomputable def to_basis_on_ℚ
    {I K: Type*} [Field K] [NumberField K]
    (basis: Basis I ℤ  (NumberField.RingOfIntegers K)):
    Basis I ℚ K := by
      -- the basis map comes from composition of the algebra map and the basis map from I to (NumberField.RingOfIntegers K)
      apply Basis.mk (v := (algebraMap (NumberField.RingOfIntegers K) K) ∘ basis)
      ·
        -- linear indenpent infer linear indenpent on localisation
        apply LinearIndependent.localization_localization (R := ℤ) (S := nonZeroDivisors ℤ) (Rₛ := ℚ)
        exact Basis.linearIndependent basis
      ·
        -- is a generator infer is a generator on localisation
        apply ge_of_eq
        rw [Set.range_comp]
        apply span_eq_top_localization_localization (R := ℤ) (S := nonZeroDivisors ℤ) (Rₛ := ℚ)
        exact Basis.span_eq basis

/-! Informal proof:
1. Just use the fact that, if $\alpha_{i}$ is linear independent/a generator set for $A$ over $R$, then it is also linear independent/a generator set fro $S^{-1} A$ over $S^{-1} R$.
2. $\mathbb{Q}$ is the localization of $\Z$ on $\Z - {0}$, $K$ is the localization of the ring of algebraic integers on $\Z - {0}$, so the result is trivial.
-/
