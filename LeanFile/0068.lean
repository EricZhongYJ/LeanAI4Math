import Mathlib
/-! Question:
28. Let $(A, \star)$ and $(B, \diamond)$ be groups and let $A \times B$ be their direct product (as defined in Example
6). Verify all the group axioms for $A \times B$ :
(a) prove that the associative law holds: for all $\left(a_{i}, b_{i}\right) \in A \times B, i=1,2,3$ $\left(a_{1}, b_{1}\right)\left[\left(a_{2}, b_{2}\right)\left(a_{3}, b_{3}\right)\right]=\left[\left(a_{1}, b_{1}\right)\left(a_{2}, b_{2}\right)\right]\left(a_{3}, b_{3}\right)$,
(b) prove that $(1,1)$ is the identity of $A \times B$, and
(c) prove that the inverse of $(a, b)$ is $\left(a^{-1}, b^{-1}\right)$.
-/
import Mathlib.Tactic

/- Let A and B are groups. Verify that A×B forms a group -/

instance {A B : Type*} [Group A] [Group B] : Group (A × B) where
  --First define mul, one, inv and div of Group
  mul g h := ⟨g.1 * h.1, g.2 * h.2⟩
  one := ⟨1, 1⟩
  inv g := ⟨g.1⁻¹, g.2⁻¹⟩
  div g h := g * h⁻¹
  -- verify the axioms of Group
  -- verify the associative law
  mul_assoc _ _ _ := by
    ext
    exact mul_assoc _ _ _
    exact mul_assoc _ _ _
  -- verify that (1, 1) is the identity
  one_mul _ := by
    ext
    exact one_mul _
    exact one_mul _
  mul_one _ := by
    ext
    exact mul_one _
    exact mul_one _
    -- verify the inverse
  inv_mul_cancel _ := by
    ext
    exact inv_mul_cancel _
    exact inv_mul_cancel _


/-! Informal proof:
Follow the exercise requirements.
-/
