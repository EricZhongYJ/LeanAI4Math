import Mathlib
/-! Question:
3.1.6. 设 $K / F$ 为域扩张, $a \in K$. 若 $a \in F\left(a^{m}\right), m>1$, 则 $a$ 在 $F$ 上代数.
-/

open Polynomial
/-
Let $K / F$ be a field extension, and let $a \in K$. If $a \in F(a^m)$ with $m > 1$, then $a$ is
 algebraic over $F$.
1. Since $a \in F(a^m)$, $\exist f, g \in F[x]$ s.t. $a = \frac{f(a^m)}{g(a^m)}$
2. It is trivial that if $g(a^m) = 0$, then $a = 0$ and $a$ is algebric over $F$
3. Else $g(a^m) \
eq 0$, then $a \cdot g(a^m) = f(a^m)$, We can define
 $h(x) = x \cdot g(x^m) - f(x^m)$
4. Then $h(a) = a \cdot g(a^m) - f(a^m) = 0$
5. Also, $h(x) \
eq 0$ because if $h(x) = 0$, then $x \cdot f(x^m) = g(x^m)$, compare the degree of
 this equation, $1 + m \cdot \operatorname{deg} f = m \cdot \operatorname{deg} g$ which leads to
  $m = 1$, contradiction!
   Now we are done.
-/
lemma UnexploredExercise_105{K F : Type*}[Field F] [Field K] [Algebra F K]{a : K}{m : ℕ}
(hm : m > 1)(h : a ∈ IntermediateField.adjoin F {a ^ m}) : IsAlgebraic F a := by
  --1. Since $a \in F(a^m)$, $\exist f, g \in F[x]$ s.t. $a = \frac{f(a^m)}{g(a^m)}$
  obtain ⟨f, g, eq⟩ := (IntermediateField.mem_adjoin_simple_iff F a).mp h
  by_cases choice : (aeval (a ^ m)) g = 0
  · --2. It is trivial that if $g(a^m) = 0$, then $a = 0$ and $a$ is algebric over $F$
    simp only [choice, div_zero] at eq
    rw[eq]
    exact isAlgebraic_zero
  · /-3. Else $g(a^m) \
eq 0$, then $a \cdot g(a^m) = f(a^m)$, We can define
 $h(x) = x \cdot g(x^m) - f(x^m)$  -/
    set h := X * g.comp (X ^ m) - f.comp (X ^ m) with hh
    --4. Then $h(a) = a \cdot g(a^m) - f(a^m) = 0$
    have : (aeval a) h = 0 := by simp only [hh, map_sub, map_mul, aeval_X, aeval_comp, aeval_X_pow,
      sub_eq_zero_of_eq <| (eq_div_iff choice).mp eq]
    --5. Also, $h(x) \
eq 0$
    have : h ≠ 0 := by
      -- because if $h(x) = 0$, then $x \cdot f(x^m) = g(x^m)$
      intro nh
      rw[hh] at nh
      /-compare the degree of this equation,
      $1 + m \cdot \operatorname{deg} f = m \cdot \operatorname{deg} g$-/
      have := congrArg natDegree <| sub_eq_zero.mp nh
      rw [natDegree_X_mul, natDegree_comp, natDegree_comp, natDegree_X_pow] at this
      ·  /-which leads to $m = 1$, contradiction!-/
        have : 1 = (f.natDegree - g.natDegree) * m := by
          rw [Nat.eq_sub_of_add_eq' this, ←(Nat.mul_sub_right_distrib f.natDegree g.natDegree m)]
        linarith [Nat.eq_one_of_mul_eq_one_left <| id this.symm]
      · intro geq0
        have := congrArg (Polynomial.aeval a) geq0
        simp only [map_zero, aeval_comp, aeval_X_pow] at this
        contradiction
    use h


/-! Informal proof:
Let $K / F$ be a field extension, and let $a \in K$. If $a \in F(a^m)$ with $m > 1$, then $a$ is algebraic over $F$.
1. Since $a \in F(a^m)$, $\exist f, g \in F[x]$ s.t. $a = \frac{f(a^m)}{g(a^m)}$
2. It is trivial that if $g(a^m) = 0$, then $a = 0$ and $a$ is algebric over $F$
3. Else $g(a^m) \
eq 0$, then $a \cdot g(a^m) = f(a^m)$, We can define $h(x) = x \cdot g(x^m) - f(x^m)$
4. Then $h(a) = a \cdot g(a^m) - f(a^m) = 0$
5. Also, $h(x) \
eq 0$ because if $h(x) = 0$, then $x \cdot f(x^m) = g(x^m)$, compare the degree of this equation, $1 + m \cdot \operatorname{deg} f = m \cdot \operatorname{deg} g$ which leads to $m = 1$, contradiction!
   Now we are done.
-/
