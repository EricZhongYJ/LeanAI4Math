import Mathlib
/-! Question:
6. Prove the Rational Root Theorem 5.6.
-/

/-
  If $R$ is a UFD and $f(x) = a_n x^n + a_{n-1} x^{n-1} + \dots + a_1 x + a_0$ is a polynomial in
 $R[x]$ with a rational root of the form $\frac{p}{q}$ (where $p, q \in R$ have no common divisors
  other than units), then :
  1. $p$ must divide $a_0$, the constant term of $f(x)$.
  2. $q$ must divide $a_n$, the leading coefficient of $f(x)$.
-/
variable {R : Type* } {K : Type u_2} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
 [Field K] [Algebra R K] [IsFractionRing R K] {f : Polynomial R} {r : K} 
--Both two theorem are well-known.

lemma part_1 (hr : (Polynomial.aeval r) f = 0) : IsFractionRing.num R r ∣ f.coeff 0 := 
  num_dvd_of_is_root hr
lemma part_2 (hr : (Polynomial.aeval r) f = 0) : ↑(IsFractionRing.den R r) ∣ f.leadingCoeff :=
  den_dvd_of_is_root hr



/-! Informal proof:
  If $R$ is a UFD and $f(x) = a_n x^n + a_{n-1} x^{n-1} + \dots + a_1 x + a_0$ is a polynomial in
 $R[x]$ with a rational root of the form $\frac{p}{q}$ (where $p, q \in R$ have no common divisors
  other than units), then :
  1. $p$ must divide $a_0$, the constant term of $f(x)$.
  2. $q$ must divide $a_n$, the leading coefficient of $f(x)$.
Both two theorem are well-known.
-/
