import Mathlib
/-! Question:
4.41 If $O$ is an orthogonal matrix, prove that $\operatorname{det}(O)= \pm 1$.
-/

/-
If $O$ is an orthogonal matrix, prove that $\det (O) = \pm 1$.
-/

variable {n : Type*} [Fintype n] [DecidableEq n]


example (O : Matrix n n ℝ) (h : O.transpose * O = 1) : O.det = 1 ∨ O.det = -1 := by

  -- As $O$ is an orthogonal matrix, $O^T \cdot O = I$, we have: $\det(O^T \cdot O) = \det(I)$.
  apply congrArg Matrix.det at h

  -- $\det(O^T \cdot O) = \det(O^T) \cdot \det(O) = \det(O) \cdot \det(O)$, and $\det(I) = 1$
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h

  -- then we have $\det (O) = \pm 1$.
  refine mul_self_eq_one_iff.mp h


/-! Informal proof:
As $O$ is an orthogonal matrix, $O^T \cdot O = I$, we have: $\det(O^T \cdot O) = \det(I)$.
$\det(O^T \cdot O) = \det(O^T) \cdot \det(O) = \det(O) \cdot \det(O)$, and $\det(I) = 1$.
Then we have $\det (O) = \pm 1$.
-/
