import Mathlib
/-! Question:
3. Give an example of fields $K \subseteq E, F$ such that $E \otimes_{K} F$ contains zero divisors. Give an example of fields $K \subseteq E, F$ such that $E \otimes_{K} F$ contains nonzero nilpotent elements.
-/
import Mathlib.FieldTheory.Adjoin
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.Data.Real.Sqrt
import Mathlib.FieldTheory.KummerExtension
import Mathlib.Data.Real.Irrational

suppress_compilation

/-!

# UnexploredExercise_7334

- `UnexploredExercise_7334.tensorProduct_of_field_with_zeroDivisors`:
  Give an example of fields K ⊆ E,F such that E ⊗_K F contains zero divisors.

- `UnexploredExercise_7334.tensorProduct_of_field_with_nilpotent`: Give an example of fields 
  K ⊆ E, F such that E ⊗_K F contains nonzero nilpotent elements.
-/

namespace UnexploredExercise_7334

open IntermediateField TensorProduct Polynomial

instance (priority := high) : Algebra ℚ ℚ⟮√2⟯ := inferInstance

/--
Let `K = ℚ`, `E = ℚ⟮√2⟯`, and `F = ℚ⟮√2⟯`. Then `E ⊗_K F` contains zero divisors, namely
`√2 ⊗ 1 - 1 ⊗ √2`.
-/
lemma tensorProduct_of_field_with_zeroDivisors :
    AdjoinSimple.gen ℚ √2 ⊗ₜ 1 - 1 ⊗ₜ AdjoinSimple.gen ℚ √2 ∉
      nonZeroDivisors (ℚ⟮√2⟯ ⊗[ℚ] ℚ⟮√2⟯) := by
  classical
  -- Note that √2 * √2 = 2 in ℚ⟮√2⟯
  have eq1 : AdjoinSimple.gen ℚ √2 * AdjoinSimple.gen ℚ √2 = 2 := by aesop
  -- Note that 1 ⊗ 2 = 2 ⊗ 1 in ℚ⟮√2⟯ ⊗_ℚ ℚ⟮√2⟯
  have eq2 :
      (1 ⊗ₜ 2 : ℚ⟮√2⟯ ⊗[ℚ] ℚ⟮√2⟯) = 2 ⊗ₜ 1 := by
    conv_rhs => rw [show (2 : ℚ⟮√2⟯) = (2 : ℚ) • 1 by norm_num, smul_tmul, Algebra.smul_def,
      mul_one]
    rfl
  -- if `√2 ⊗ 1 - 1 ⊗ √2` is not a zero divisor, then since `(√2 ⊗ 1 - 1 ⊗ √2)(√2 ⊗ 1 + 1 ⊗ √2) = 0`
  -- we will have `√2 ⊗ 1 + 1 ⊗ √2 = 0`. But this is not possible, for the following reasons:
  intro h
  have eq := h (AdjoinSimple.gen ℚ √2 ⊗ₜ[ℚ] 1 + 1 ⊗ₜ[ℚ] AdjoinSimple.gen ℚ √2)
    (by
      simp only [add_mul, mul_sub, mul_sub, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one,
        eq1, eq2]
      abel)
  -- note that √2 is integral in ℚ with minimal polynomial X² - 2
  have H : IsIntegral ℚ √2 :=
    ⟨X^2 + C (-2), by rw [Monic.def, leadingCoeff_X_pow_add_C]; positivity, by simp⟩
  have hp : minpoly ℚ √2 = X^2 + C (-2) := by
    rw [Eq.comm, minpoly.eq_iff_aeval_eq_zero]
    · simp
    · rw [C_neg, ← sub_eq_add_neg]
      apply X_pow_sub_C_irreducible_of_prime Nat.prime_two
      simpa [IsSquare, pow_two, eq_comm] using
        irrational_sqrt_ratCast_iff_of_nonneg (q := 2) (by positivity) |>.1
        irrational_sqrt_two
    · rw [Monic.def, leadingCoeff_X_pow_add_C]
      positivity
  -- therefore ℚ⟮√2⟯ has a basis `{1, √2}`
  let b := adjoin.powerBasis H
  have dim_eq : b.dim = 2 := by
    change natDegree _ = 2
    rw [hp, natDegree_X_pow_add_C]
  haveI : NeZero b.dim := ⟨by omega⟩
  -- therefore ℚ⟮√2⟯ ⊗_ℚ ℚ⟮√2⟯ has a basis `{1, 1 ⊗ √2, √2 ⊗ 1, √2 ⊗ √2}`
  set ℬ := b.basis.tensorProduct b.basis with ℬ_eq
  have b1 : b.basis 1 = AdjoinSimple.gen ℚ √2 := by
    simp only [PowerBasis.coe_basis, Fin.val_one', dim_eq, Nat.mod_succ, pow_one]
    rfl
  have ℬ10 : ℬ (1, 0) = AdjoinSimple.gen ℚ √2 ⊗ₜ 1 := by simp [ℬ_eq, b1]
  have ℬ01 : ℬ (0, 1) = 1 ⊗ₜ AdjoinSimple.gen ℚ √2 := by simp [ℬ_eq, b1]
  -- Since `{1, 1 ⊗ √2, √2 ⊗ 1, √2 ⊗ √2}` is linearly independent, in particular, `{1 ⊗ √2, √2 ⊗ 1}`
  -- is linearly independent. This contradicts the fact that `√2 ⊗ 1 + 1 ⊗ √2 = 0`
  simpa using Fintype.linearIndependent_iff.1 (ℬ.linearIndependent.comp ![(1, 0), (0, 1)] (by
    intro i j
    fin_cases i <;> fin_cases j <;>
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero,
      imp_self, Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.head_cons, Prod.mk.injEq,
      Fin.one_eq_zero_iff, Fin.zero_eq_one_iff, and_self, zero_ne_one, imp_false] <;>
    omega)) ![1, 1] (by
    rw [Fin.sum_univ_two]
    simp only [Fin.isValue, Matrix.cons_val_zero, Nat.succ_eq_add_one, Nat.reduceAdd,
      Function.comp_apply, ℬ10, one_smul, Matrix.cons_val_one, Matrix.head_cons, ℬ01, eq,
      forall_const]) 0

namespace tensorProduct_of_field_with_nilpotent

-- Let `K = ℤ₂(X)`, field of fraction of the polynomial ring `ℤ₂[X]`
local notation \"K\" => FractionRing (ZMod 2)[X]
-- Let `E = F = K⟮√X⟯)`
local notation \"E\" => AdjoinRoot (R := FractionRing (ZMod 2)[X]) (X^2 - 1)
local notation \"F\" => AdjoinRoot (R := FractionRing (ZMod 2)[X]) (X^2 - 1)

-- then `K` has characteristic 2, i.e. `2 = 0` in `K`
instance : CharP K 2 := inferInstance
lemma eq0 : (2 : K) = 0 :=
  CharP.cast_eq_zero_iff K 2 2 |>.2 (by rfl)

-- therefore `2 ∈ E ⊗[K] F` is 0 since it is `(2 : K) • 1 = 0 • 1 = 0`.
set_option maxHeartbeats 500000 in
set_option synthInstance.maxHeartbeats 50000 in
lemma eq1 : (2 : E ⊗[K] F) = 0 := by
  rw [show (2 : E ⊗[K] F) = algebraMap K (E ⊗[K] F) (2 : K) by rfl]
  convert map_zero (algebraMap K (E ⊗[K] F)) using 1
  congr 1
  exact eq0

-- then `√X^2 = 1 in E` by construction (√X is the root of X^2 - 1 = 0)
lemma eq2 : (AdjoinRoot.root _ : E)^2 = 1 := by
  have : IsRoot _ (AdjoinRoot.root _ : E) := AdjoinRoot.isRoot_root _
  simpa [sub_eq_zero] using this

end tensorProduct_of_field_with_nilpotent

open tensorProduct_of_field_with_nilpotent in
/--
Let `K = ℤ₂(X)`, `E = F = K⟮√X⟯)`. Then `E ⊗_K F` contains nilpotent elements, namely
`1 ⊗ √X - √X ⊗ 1`. Because its square is `(1 ⊗ √X - √X ⊗ 1)² = 2 = 0`.
-/
lemma tensorProduct_of_field_with_nilpotent :
    IsNilpotent (1 ⊗ₜ AdjoinRoot.root _ - AdjoinRoot.root _ ⊗ₜ 1 :
      AdjoinRoot (R := FractionRing (ZMod 2)[X]) (X^2 - 1) ⊗[FractionRing (ZMod 2)[X]]
      AdjoinRoot (R := FractionRing (ZMod 2)[X]) (X^2 - 1)) := by
  use 2
  simp only [sub_sq, Algebra.TensorProduct.tmul_pow, one_pow, eq1, zero_mul, sub_zero, eq2,
    ← Algebra.TensorProduct.one_def, one_add_one_eq_two]

-- (1 ⊗ √X - √X ⊗ 1) is not zero
lemma tensorProduct_of_field_with_ne_zero_nilpotent :
    (1 ⊗ₜ AdjoinRoot.root _ - AdjoinRoot.root _ ⊗ₜ 1 :
      AdjoinRoot (R := FractionRing (ZMod 2)[X]) (X^2 - 1) ⊗[FractionRing (ZMod 2)[X]]
      AdjoinRoot (R := FractionRing (ZMod 2)[X]) (X^2 - 1)) ≠ 0 := by
  -- assume `(1 ⊗ √X - √X ⊗ 1)` is zero
  intro rid
  -- since `{1, √X}` is a basis of `K⟮√X⟯`,
  let b : PowerBasis _ (AdjoinRoot (R := FractionRing (ZMod 2)[X]) (X^2 - 1)) :=
    AdjoinRoot.powerBasis (by
      rw [show (X^2 - 1 : (FractionRing (ZMod 2)[X])[X]) = X^2 - C 1 by simp]
      apply X_pow_sub_C_ne_zero
      norm_num)
  have dim_eq : b.dim = 2 := by
    simp only [AdjoinRoot.powerBasis_dim, b]
    rw [show (X^2 - 1 : (FractionRing (ZMod 2)[X])[X]) = X^2 + (C (-1)) by simp [sub_eq_add_neg],
      natDegree_X_pow_add_C]
  haveI : NeZero b.dim := ⟨by omega⟩

  -- `{1, 1 ⊗ √X, √X ⊗ 1, √X ⊗ √X}` is a basis of `K⟮√X⟯ ⊗_K K⟮√X⟯`
  let ℬ := b.basis.tensorProduct b.basis
  have ℬ10 : ℬ (1, 0) = AdjoinRoot.root _ ⊗ₜ 1 := by
    simp only [Basis.tensorProduct_apply, PowerBasis.coe_basis, Fin.val_one', dim_eq, Nat.mod_succ,
      pow_one, Fin.val_zero, pow_zero, ℬ]
    rfl
  have ℬ01 : ℬ (0, 1) = 1 ⊗ₜ AdjoinRoot.root _ := by
    simp only [Basis.tensorProduct_apply, PowerBasis.coe_basis, Fin.val_one', dim_eq, Nat.mod_succ,
      pow_one, Fin.val_zero, pow_zero, ℬ]
    rfl
  -- in particular, `{1 ⊗ √X, √X ⊗ 1}` is linearly independent
  -- this contradicts `1 ⊗ √X - √X ⊗ 1 = 0`
  simpa using Fintype.linearIndependent_iff.1 (ℬ.linearIndependent.comp ![(1, 0), (0, 1)] (by
    intro i j
    fin_cases i <;> fin_cases j <;>
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero,
      imp_self, Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.head_cons, Prod.mk.injEq,
      Fin.one_eq_zero_iff, Fin.zero_eq_one_iff, and_self, zero_ne_one, imp_false] <;>
    omega)) ![-1, 1] (by
    rw [Fin.sum_univ_two]
    simp only [Fin.isValue, Matrix.cons_val_zero, Nat.succ_eq_add_one, Nat.reduceAdd,
      Function.comp_apply, ℬ10, neg_smul, one_smul, Matrix.cons_val_one, Matrix.head_cons, ℬ01,
      ←rid]
    abel) 0

end UnexploredExercise_7334

/-! Informal proof:
>   Give an example of fields $K ⊆ E,F$ such that $E \otimes_K F$ contains zero divisors.
Let $K = \mathbb Q$ and $E = F = \mathbb Q(\sqrt2)$, then $\sqrt2 \otimes 1 - 1 \otimes \sqrt2$ is a zero divisor. Because if it not a zero divisor, since $(\sqrt2 \otimes 1 - 1 \otimes \sqrt2)(\sqrt2 \otimes 1 + 1 \otimes \sqrt2) = 0$, we will have $\sqrt2 \otimes 1 + 1 \otimes \sqrt2$ = 0. But this is not possible. Notice that $\{1, \sqrt2\}$ is a basis of $\mathbb Q(\sqrt2)$ therefore $\{1, 1\otimes\sqrt2, \sqrt2\otimes1, \sqrt2\otimes\sqrt2\}$ is a basis of $\mathbb Q(\sqrt2)\otimes_{\mathbb Q}\mathbb Q(\sqrt2)$. In particular $\{1\otimes\sqrt2, \sqrt2\otimes1\}$ is linearly independent, therefore their sum $\sqrt2 \otimes 1 + 1 \otimes \sqrt2$ is not zero, a contradiciton.
> Give an example of fields $K ⊆ E, F$ such that $E \otimes_K F$ contains nonzero nilpotent elements.
Let $K = F_2(X)$, the field of rational polynomials over $F_2$, and $E=F=K[Y]/(Y^2-1)$, or in another word, the field extension over $K$ where $X^{1/2}$ is a solution for the polynomial $Y^2 -1 = 0$. Then $1\otimes X^{1/2}-X^{1/2}\otimes 1$ is nilpotent: its square $(1\otimes X^{1/2}-X^{1/2}\otimes 1)^2=1\otimes 1 - 2\cdot 1\otimes 1 + 1 \otimes 1 = 0$. It is also non-zero, because again $\{1, X^{1/2}\}$ is a basis of $E$ so that $\{1, 1\otimes X^{1/2}, X^{1/2}\otimes 1, X^{1/2}\otimes X^{1/2}\}$ is a basis of $E\otimes_K F$. In particular $1\otimes X^{1/2}$ and $X^{1/2}\otimes 1$ are linearly independent, therefore $\otimes X^{1/2}-X^{1/2}\otimes 1$ is not zero.
-/
