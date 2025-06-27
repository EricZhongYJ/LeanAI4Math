import Mathlib
/-! Question:
3.4.4. 求证: $x^{5}-x+1$ 是 $\mathbb{Z}_{3}[x]$ 中的本原多项式.
-/
open Polynomial
open Finset Polynomial BigOperators
/-Problem: Show that $X^5-X+1$ is a primitive polynomial in $\mathbb{Z}_3[X]$.-/
example: ((X^5-X+1):(ZMod 3)[X]).IsPrimitive :=by
/-Observe that $X^5-X+1$ is monic, so by definition of primitive we only need to verify $X^5-X+1$ is monic. -/ 
  refine Monic.isPrimitive ?hp
/-Note that $1$ has degree smaller than $X^5-X+1$, so we can equivalently show that $X^5-X$ is monic-/
  refine Monic.add_of_left ?hp.hp ?hp.hpq
/-Simlarly, $X$ has degree smaller than $X^5$, so we can equivalently show that $X^5$ is monice-/
  refine Monic.sub_of_left ?hp.hp.hp ?hp.hp.hpq
/-Show that $X^5$ is trivially monic.-/
  · exact monic_X_pow 5
/-Show that the degree of $X$ is less than $X^5$.-/
  · simp only [degree_X, degree_pow, nsmul_eq_mul, Nat.cast_ofNat, mul_one, Nat.one_lt_ofNat]
/-Show that the degree of $1$ is less than $X^5-X$-/
/-We can trivially show that $X^5$ and $X^5-X$ have the same degree.
Since the degree of $X^5$ is $5$ obviously bigger that $1$, we completes the proof.-/
  · have degree: ((X^5-X):(ZMod 3)[X]).degree=((X^5):(ZMod 3)[X]).degree :=by 
      refine degree_sub_eq_left_of_degree_lt ?h
      simp only [degree_X, degree_pow, nsmul_eq_mul, Nat.cast_ofNat, mul_one, Nat.one_lt_ofNat] 
    rw[degree];simp only [degree_one, degree_pow, degree_X, nsmul_eq_mul, Nat.cast_ofNat, mul_one,
      Nat.ofNat_pos]
    

/-! Informal proof:
**Problem**: Show that $X^5-X+1$ is a primitive polynomial in $\mathbb{Z}_3[X]$.
**Proof**:Since $X^5-X+1$ is monic, it is trivially a primitive polynomial. Q.E.D.
-/
