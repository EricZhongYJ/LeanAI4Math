import Mathlib
/-! Question:
4.35 Let $V$ be a finite-dimensional vector space over a field $k$, and let $\mathcal{B}$ denote the family of all the bases of $V$. Prove that $\mathcal{B}$ is a transitive $\operatorname{GL}(V)$-set.
-/

-- Q: Let $V$ be a finite-dimensional vector space over a field $k$, and let $\mathcal{B}$ denote the family of all the bases of $V$. Prove that $\mathcal{B}$ is a transitive $GL(V)$-set.
-- A: Suppose that $b_1, b_2 \in \mathcal{B}$, and $B_1$ and $B_2$ are the matrices with columns the vectors in $b_1$ and $b_2$ respectively. We claim that $B_1 * B_2^{-1}$ is the matrix in $GL(V)$ that takes vectors in $b_1$ to vectors in $b_2$, i.e. \forall j, $(B_1 * B_2^{-1})(b_1^{(j)}) = (b_2^{(j)})$, where $b_i^{(j)}$ denotes the $j$-th vector in $b_i$. This is clearly true by the definition.

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {k : Type*} [Field k]

noncomputable def matrix_from_basis_col
  (e : Basis ι k (ι → k)) : Matrix ι ι k := fun i j => e j i

def matrix_cols  (M : Matrix ι ι k) := fun j => fun i => M i j

-- lemma: for matrixs $A, B, C$, if $AB = C$ then $Ab_j = c_j$, where $b_j$ denotes the $j$-th column of $B$ and so as $c_j$
lemma matrix_mul_eq_imp_mulVec_eq  (A B C: Matrix ι ι k) (h : A * B = C) :
  ∀ j, A.mulVec ((matrix_cols B) j) = matrix_cols C j := by
  intro j; ext i
  have h': (A * B) i j = C i j := by rw [h]
  rw [Matrix.mul_apply] at h'
  exact h'

theorem basis_is_GL_transive
  (b₁ : Basis ι k (ι → k)) (b₂ : Basis ι k (ι → k)) :
  ∃ (A : Matrix ι ι k), (IsUnit A) ∧ (∀ (j : ι), (A.mulVec (b₁ j)) = b₂ j) := by
  -- change $b_1$, $b_2$ into matrix
  let M₁ : Matrix ι ι k := λ i j => b₁ j i
  let M₂ : Matrix ι ι k := λ i j => b₂ j i
  -- prove that the matrices are invertible.
  have m1_isunit : IsUnit M₁ := by
    rw [← Matrix.linearIndependent_cols_iff_isUnit]
    apply Basis.linearIndependent b₁
  have m2_isunit : IsUnit M₂ := by
    rw [← Matrix.linearIndependent_cols_iff_isUnit]
    apply Basis.linearIndependent b₂
  have m1_inv : Invertible M₁ := by
    apply Matrix.invertibleOfIsUnitDet
    exact (Matrix.isUnit_iff_isUnit_det M₁).1 m1_isunit
  
  -- claim: M₁ * ⅟M₁ is the matrix
  use M₂ * ⅟M₁
  constructor
  -- prove that the matrix is invertible
  · have : IsUnit ⅟M₁ := by apply isUnit_of_invertible
    apply IsUnit.mul; exact m2_isunit; exact this

  -- prove that the matrix takes vectors in $b_1$ to vectors in $b_2$
  . intro j
    have h : M₂ * ⅟M₁ * M₁ = M₂ := by
      rw [invOf_mul_cancel_right]
    have h₁ : b₁ j = matrix_cols M₁ j := by rfl
    have h₂ : b₂ j = matrix_cols M₂ j := by rfl
    rw [h₁, h₂]
    apply matrix_mul_eq_imp_mulVec_eq
    exact h


/-! Informal proof:
Suppose that $b_1, b_2 \in \mathcal{B}$, and $B_1$ and $B_2$ are the matrices with columns the vectors in $b_1$ and $b_2$ respectively. We claim that $B_1 * B_2^{-1}$ is the matrix in $GL(V)$ that takes vectors in $b_1$ to vectors in $b_2$, i.e. \forall j, $(B_1 * B_2^{-1})(b_1^{(j)}) = (b_2^{(j)})$, where $b_i^{(j)}$ denotes the $j$-th vector in $b_i$. This is clearly true by the definition.
-/
