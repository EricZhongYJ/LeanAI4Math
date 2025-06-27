import Mathlib
/-! Question:
设 $R$ 为一交换环，
证明：
若 $R$ 有限，
则 $R$ 的素理想都是极大理想。
-/

open Ideal

-- Suppose R is a finite commutative ring.
variable {R : Type*} [CommRing R] [Fintype R]

-- We try to prove in a finite commutative ring, every prime ideal is a maximal ideal.
theorem prime_ideal_is_maximal_in_finite_ring (P : Ideal R) [hP : P.IsPrime] : P.IsMaximal := by
  -- Since R is finite and the ideal P is prime, we consider the quotient ring R/P.
  have h1 : IsDomain (R ⧸ P) := by exact (Quotient.isDomain_iff_prime P).mpr hP
  -- Since R/P is a finite ring without zero divisors, it is a field.
  have h2 : IsField (R ⧸ P) := by exact Finite.isField_of_domain (R ⧸ P)
  -- According to the definition of a maximal ideal, P is a maximal ideal.
  exact Quotient.maximal_of_isField P h2
  
/-! Informal proof:
-- Suppose R is a finite commutative ring.
-- We try to prove in a finite commutative ring, every prime ideal is a maximal ideal.
-- Since R is finite and the ideal P is prime, we consider the quotient ring R/P.
  -- Since R/P is a finite ring without zero divisors, it is a field.
  -- According to the definition of a maximal ideal, P is a maximal ideal.
-/
