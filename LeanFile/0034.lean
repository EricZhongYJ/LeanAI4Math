import Mathlib
/-! Question:
4.48 Let $R$ be a commutative ring, let $A$ be an $n \times n$ with entries in $R$, let $B$ be an $m \times m$ matrix, and let $D$ be the $(n+m) \times(n+m)$ matrix $D=\left[\begin{array}{cc}A & 0 \\ 0 & B\end{array}\right]$. Prove that $\operatorname{det}(D)=\operatorname{det}(A) \operatorname{det}(B)$.
-/

variable {R : Type*} [CommRing R]

open Matrix

-- Theorem: Determinant of a block diagonal matrix
theorem det_block_diag {n m : ℕ} (A : Matrix (Fin n) (Fin n) R) (B : Matrix (Fin m) (Fin m) R) :
  det (fromBlocks A 0 0 B) = det A * det B := by
  -- Use the fact that the determinant of a block diagonal matrix is the product of determinants of each block.
  rw [det_fromBlocks_zero₂₁]
  -- Simplifies to `det A * det B`

/-! Informal proof:
We work with two square matrices $A$ and $B$, with dimensions $n \times n$ and $m \times m$ respectively, where the entries of both matrices are from a commutative ring $R$.
The matrix $D$ is defined as the block diagonal matrix with $A$ in the upper left corner and $B$ in the lower right corner, and the off-diagonal blocks being zero.
We use the known result that the determinant of a block diagonal matrix with zero off-diagonal blocks is the product of the determinants of the diagonal blocks. This is expressed as:
   $$
   \det \begin{bmatrix} A & 0 \\ 0 & B \end{bmatrix} = \det(A) \cdot \det(B)
   $$
The determinant of the block diagonal matrix $D$ is the product of the determinants of $A$ and $B$, thus completing the proof.

-/
