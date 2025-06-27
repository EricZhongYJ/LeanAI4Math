import Mathlib
/-! Question:
*4.42 If $A^{\prime}$ is obtained from an $n \times n$ matrix by interchanging two of its rows, prove that $\operatorname{det}\left(A^{\prime}\right)=-\operatorname{det}(A)$
-/

/-
If $A'$ is obtained from an $n \times n$ matrix by interchanging two of its rows, prove that $\det (A') = - \det (A)$.
-/

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {R : Type} [DecidableEq R] [CommRing R]


-- Define `matrix_swap_row` to swap rows `i` and `j` in a matrix `A`, using `Matrix.submatrix` with `Equiv.swap i j`.
def matrix_swap_row (A : Matrix n n R) (i j : n) :=
  Matrix.submatrix A (Equiv.swap i j) id

-- Prove that swapping two rows negates the determinant.
example (A : Matrix n n R) (i j : n) (h : i ≠ j) :
    (matrix_swap_row A i j).det = -1 * A.det := by

  --  $\det (M_{\sigma}) = sign (\sigma) \cdot \det (M)$, where $M_{\sigma}$ is the matrix with rows permuted according to $\sigma$.
  rw [matrix_swap_row, Matrix.det_permute]

  -- Use `Equiv.Perm.sign_swap` which gives `-1` for a swap
  rw [Equiv.Perm.sign_swap h]
  norm_cast


/-! Informal proof:
We know that $\det (M_{\sigma}) = sign (\sigma) \cdot \det (M)$, where $M_{\sigma}$ is the matrix with rows permuted according to $\sigma$. Let $\sigma$ equals a swap where $A' = A_{\sigma}$. As a swap's sign equals to $-1$, we have $\det (A') = \det{A_{\sigma}} = sign(\sigma) \cdot \det(M) = - \det (M)$.
-/
