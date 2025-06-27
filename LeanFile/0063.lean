import Mathlib
/-! Question:
3.1.6. 设 $K / F$ 为域扩张, $a \in K$. 若 $a \in F\left(a^{m}\right), m>1$, 则 $a$ 在 $F$ 上代数.
-/
import Mathlib.RingTheory.Algebraic
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Field.Defs
import Mathlib.FieldTheory.Adjoin
import Mathlib.Logic.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Degree.Definitions

/- K/F field extension , a in K, a in F(a^m) for some integer m > 1 -/
variable {K F : Type*}


lemma simplify_to_algebraic_eq [Field F] [Field K] [Algebra F K] (f g : Polynomial F) (a : K)  (m : ℕ) : (Polynomial.aeval (a ^ m)) g * a = (Polynomial.aeval (a ^ m)) f
  → (Polynomial.aeval a) ((g.comp (Polynomial.X ^ m)) * Polynomial.X - (f.comp (Polynomial.X ^ m))) = 0
  := by
    /- lemma to simplify the expression g(a^m)*a = f(a^m) -/
    intro c1
    simp
    rw [<- sub_eq_zero_of_eq]
    rw [Polynomial.aeval_comp]
    rw [Polynomial.aeval_X_pow]
    rw [Polynomial.aeval_comp]
    rw [Polynomial.aeval_X_pow]
    exact c1



lemma h_nonzero [Field F] [Field K] [Algebra F K] (f g : Polynomial F) (a : K)  (m : ℕ) : (m > 1)
  → (g.comp (Polynomial.X ^ m) ≠ 0)
  → (g.comp (Polynomial.X ^ m) * Polynomial.X - f.comp (Polynomial.X ^ m) ≠ 0)
  := by
    /- lemma use the fact g(x^m) is nonzero and degree counting to prove h is not zero -/
    intro h1
    intro gnz
    by_contra a
    have aa : g.comp (Polynomial.X ^ m) * Polynomial.X - f.comp (Polynomial.X ^ m) = 0 := a
    rw [sub_eq_zero] at aa
    have aaa := congrArg (fun x => x.natDegree) aa
    dsimp at aaa
    rw [Polynomial.natDegree_mul_X] at aaa
    rw [Polynomial.natDegree_comp] at aaa
    rw [Polynomial.natDegree_comp] at aaa
    rw [Polynomial.natDegree_X_pow] at aaa
    have aaa := congrArg (fun x => x % m) aaa
    simp at aaa
    /-if h is zero, then g(x^m) * x = f(x^m), which means
    deg(g)* m + 1 = deg(f) * m which is impossible.-/

    rw [Nat.add_mod] at aaa
    simp at aaa
    apply ne_of_gt h1
    exact aaa
    exact gnz

lemma gcomp_nonzero [Field F] [Field K] [Algebra F K] (f g : Polynomial F) (a : K)  (m : ℕ) : (a ≠ 0)
  → (Polynomial.aeval (a ^ m)) g ≠ 0
  → (g.comp (Polynomial.X ^ m) ≠ 0)
  := by
    /- If g(a^m) is not zero, and a is nonzero, then g(x^m) should not be zero -/
    intro hz
    intro h
    by_contra w
    have ww := congrArg (fun x => (Polynomial.aeval a) x) w
    simp at ww
    rw [Polynomial.aeval_comp] at ww
    rw [Polynomial.aeval_X_pow] at ww
    contradiction

theorem Question_3_1_6 (a : K) [Field F] [Field K] [Algebra F K] : (m : ℕ) → (m > 1)
  → (a  ∈ IntermediateField.adjoin F {a ^ m})
  → IsAlgebraic F a
  := by
    intro m
    intro mlt1
    intro h
    by_cases hz : a = 0
    case pos =>
      rewrite [hz]
      exact isAlgebraic_zero
      /- a is zero, it is trivial. -/

    case neg =>
      /- Now assume a is nonzero. -/
      rewrite [IntermediateField.mem_adjoin_simple_iff] at h
      /- Since a ∈ F(a^m), there exists f and g in F[x]
        such that a = f(a^m)/g(a^m),  where g(a^m) should not be zero.-/
      obtain ⟨f, g, c⟩ := h
      have c1 := congrArg (fun x => ((Polynomial.aeval (a ^ m)) g) * x) c
      dsimp at c1
      let w := (Polynomial.aeval (a ^ m)) g
      by_cases hzz : ((Polynomial.aeval (a ^ m)) g = 0)
      case pos =>
        rw [hzz] at c
        rw [div_zero ((Polynomial.aeval (a ^ m)) f)] at c
        contradiction
      /- If g(a^m) is zero, there would be contradiction. -/
      case neg =>
        rw [mul_div] at c1
        rw [mul_div_cancel_left₀ ((Polynomial.aeval (a ^ m)) f) hzz] at c1

        have c2 := simplify_to_algebraic_eq f g a m c1
        /- simplify the expression  g(a^m)*a = f(a^m) to algebraic equation
          h(a) = 0, where h(x) = g(x^m)*x - f(x^m) -/
        let h := g.comp (Polynomial.X ^ m) * Polynomial.X - f.comp (Polynomial.X ^ m)
        have c23 : (Polynomial.aeval a) h = 0 := c2

        have c13 := gcomp_nonzero f g a m hz hzz
        /-  use lemma to prove that g(x^m) is nonzero-/
        have c3 := h_nonzero f g a m mlt1 c13
        /- use the fact g(x^m) is nonzero and degree counting to prove h is not zero-/

        have c33 : h ≠ 0 := c3
        unfold IsAlgebraic
        /- h is nonzero and h(a) = 0 is just the definition of a being algebraic -/
        exact ⟨h, ⟨c33,c23⟩⟩
        /-Now we done.-/

/-! Informal proof:
If a is zero, the whole problem is trivial.
Now assume a is nonzero.
Since a∈F(a^m), there exists f and g in F[x] such that a =  f(a^m)/g(a^m), where g(a^m) should not be zero.
If  g(a^m) is not zero, there would be a contradiction.
If g(a^m) is not zero, and a is nonzero, then g(x^m) should not be zero 
Simplify the expression  g(a^m)*a = f(a^m) into an algebraic equation
          h(a) = 0, where h(x) = g(x^m)*x - f(x^m) 
use lemma to prove that g(x^m) is nonzero
Use the fact g(x^m) is nonzero and degree counting to prove h is nonzero:
if h is zero, then g(x^m) * x = f(x^m), which means
deg(g)*m + 1 = deg(f)*m which is impossible.
h is nonzero and h(a) = 0, this is just the definition of a being algebraic. Now we done.

-/
