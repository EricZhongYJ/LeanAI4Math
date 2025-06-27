import Mathlib
/-! Question:
9. Show that the binomial coefficient $\left(\begin{array}{c}p_{p i}^{n}\end{array}\right)$ is the coefficient of $x^{p i}$ in the expansion of $(1+x)^{p n}$. Working over $\mathbb{F}_{p}$ show that this is the coefficient of $\left(x^{p}\right)^{i}$ in $\left(1+x^{p}\right)^{n}$ and hence prove that $\binom{p n}{p i} \equiv\binom{n}{i}(\bmod p)$.
-/
import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.BigOperators.Ring

open Nat
open Polynomial
open ZMod
open BigOperators
open Set
open Finset

/- Show that the bionomial coefficient pnCpi is the coefficient of x^{pi} in the expansion of (1+x)^{pn}}. Working over \uD835\uDD3Dₚ show that this is the coefficient of (xᵖ)ⁱ in (1+xᵖ)ⁿ and hence prove that pnCpi=nCi mod p -/

-- prove that the ith coefficient of (1+x)ⁿ is nCi
theorem BioCoeff (n : ℕ) : ∀ i : ℕ, ((1 + X) ^ n).coeff i = n.choose i := by
  intro i
  rw [add_comm 1]
  apply coeff_X_add_one_pow

example (n p : ℕ) : ((1 + X) ^ (p * n)).coeff (p * i) = (p * n).choose (p * i) := BioCoeff (p * n) (p * i)

-- prove that pnCpi=nCi mod p
theorem pnCpicongrnCi (n p : ℕ) (prime_p : Nat.Prime p) : ∀ i : ℕ, ((p * n).choose (p * i) : (ZMod p)) = (n.choose i : (ZMod p)) := by
  set f : (ZMod p)[X] := (1 + X) ^ (p * n); set g : (ZMod p)[X] := (1 + (X ^ p)) ^ n with hg
  -- (1+x)^pn=(1+x^p)^n mod p
  have eq : f = ((1 + X) ^ p) ^ n := by
    dsimp [f]; rw [← pow_mul, mul_comm]
  let (id : ℕ → (ZMod p) → (ZMod p)[X]) := fun (n : ℕ) (a : ZMod p) ↦ (monomial n a)
    --Frobenius morphism
  have eq1 (a b : (ZMod p)[X]) : (a + b) ^ p = a ^ p + b ^ p := by
    have : Fact (Nat.Prime p) := by
      exact { out := prime_p }
    have : CharP (ZMod p) p := by
      exact charP p
    apply add_pow_char_of_commute
    exact Commute.all a b
  -- f=g
  rw [eq1 1 X, one_pow, hg.symm] at eq
  intro i
  -- compute the coefficient of x^pi of both sides of f=g
  have eql : ((1 + X : (ZMod p)[X]) ^ (p * n)).coeff (p * i) = (p * n).choose (p * i) := by
    exact coeff_one_add_X_pow _ (p * n) (p * i)
  have eqr : ((1 + X ^ p : (ZMod p)[X]) ^ n).coeff (p * i) = n.choose i := by
    have coeffeq : ((1 + X ^ p : (ZMod p)[X]) ^ n).coeff (p * i) = (∑ m ∈ range (n + 1), (X ^ p) ^ m * 1 ^ (n - m) * (n.choose m)).coeff (p * i) := by
      rw [add_comm, add_pow (X ^ p) 1 n]
    simp [coeff_C, ← pow_mul, Nat.Prime.ne_zero prime_p] at coeffeq
    rw [coeffeq]
    simp
    intro hi
    symm
    refine (natCast_zmod_eq_zero_iff_dvd (n.choose i) p).mpr ?_
    rw [choose_eq_zero_of_lt]
    exact Nat.dvd_zero p
    exact hi
  have eq2 := eq1 1 X
  simp at eq2
  apply congrArg (fun (f : (ZMod p)[X]) ↦ f ^ n) at eq2
  rw [← pow_mul] at eq2
  rw [eql.symm, eqr.symm, eq2.symm]


/-! Informal proof:
Follow the instruction given by the exercise
-/
