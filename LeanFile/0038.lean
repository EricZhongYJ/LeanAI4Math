import Mathlib
/-! Question:
4.37 Let $T: V \rightarrow W$ be a linear transformation between vector spaces over a field $k$, and define
$$
\operatorname{rank}(T)=\operatorname{dim}(\operatorname{im} T) .
$$
(i)
 Let $A$ be an $m \times n$ matrix over $k$.  If $T_{A}: k^{n} \rightarrow k^{m}$ is the linear transformation defined by $T_{A}(x)=A x$, where $x$ is an $n \times 1$ column vector, prove that $\operatorname{rank}(A)=\operatorname{rank}\left(T_{A}\right)$. Conclude that one can compute the rank of a linear transformation $T: V \rightarrow W$ by $\operatorname{rank}(T)=\operatorname{rank}(A)$, where $A={ }_{Y}[T]_{X}$ for bases $X$ of $V$ and $Y$ of $W$.
(ii) Prove that similar $n \times n$ matrices have the same rank.
(iii) If $A$ is an $m \times n$ matrix and $B$ is an $p \times m$ matrix, prove that
$$
\operatorname{rank}(B A) \leq \operatorname{rank}(A) .
$$
-/

-- Q: Let $T:V→W$ be a linear transformation between vector spaces over a field $k$, and define $rank(T)=dim(imT)$.
-- (i) Let $A$ be an $m×n$ matrix over $k$. If $T_A:k^n \to k^m is the linear transformation defined by $T_A(x)=Ax$, where $x$ is an $n \times 1$ column vector, prove that $\rank(A) = \rank(T_A).
-- (ii) Prove that similar $n \times n$ matrices have the same rank.
-- (iii) If $A$ is an $m×n$ matrix and $B$ is an $p \times m$ matrix, prove that $rank(BA)≤rank(A)$.
-- A:
-- (i) $\text{rank}(T_A) = \text{dim}(\text{im}(T_A)) = \text{dim}(\{Ax | x \in k^n\}) = \text{rank}(A)$.
-- (ii) If $A$ is similar to $B$ then there exists invertible matrix $P$ such that $B = P^{-1} A P$.
-- $\rank(B) = \rank(P^{-1} * A * P) = \rank(P^{-1} * A) = \rank(A)$.
-- (iii) There exists an injection from $\{Bx | x \in M\}$ to $M$. Therefore, $\text{dim}(\{Bx | x \in M\}) \leq \text{dim}(M)$. Let $M$ be $\{Ax | x \in k^n\}$ then we have completed the proof.

variable {m n p : Type*} [Fintype m] [Fintype n] [Fintype p] [DecidableEq m] [DecidableEq n] [DecidableEq p]
variable {k : Type*} [Field k]
variable {M : Type*} {R : Type*}
variable [CommRing R] [StrongRankCondition R]
variable [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']

theorem matrix_rank_eq_tolin_rank (A : Matrix m n R) (T : (n → R) →ₗ[R] m → R) (h : T = A.mulVecLin) :
  A.rank = T.rank := by
  unfold Matrix.rank LinearMap.rank Module.finrank; rw [h]
  rw [Cardinal.cast_toNat_of_lt_aleph0]
  -- prove that T.rank is finite (just some type transformation in lean)
  rw [Matrix.range_mulVecLin]
  have : Fintype (Set.range A.transpose) := by
    have : Finite (Set.range A.transpose) := Set.finite_range A.transpose
    rw [finite_iff_nonempty_fintype] at this
    exact Classical.choice this
  have : (Set.range A.transpose) = ↑((Set.range A.transpose).toFinset) := by
    have : ((Set.range A.transpose).toFinset) = Set.range A.transpose := by
      apply Set.ext; intro x; exact Set.mem_toFinset
    rw [this]
  rw [this]
  exact rank_span_of_finset (Set.range A.transpose).toFinset

theorem similar_matrix_rank_eq (A B : Matrix n n R) (P : Matrix n n R) (h : IsUnit P) (h_eq : B = P⁻¹ * A * P) :
  A.rank = B.rank := by
  rw [h_eq]
  -- $\rank(P^{-1} * A * P) = \rank(P^{-1} * A)$
  rw [Matrix.rank_mul_eq_left_of_isUnit_det P (P⁻¹ * A) ((Matrix.isUnit_iff_isUnit_det P).1 h)]
  -- $\rank(P^{-1} * A) = \rank(A)$
  rw [Matrix.rank_mul_eq_right_of_isUnit_det P⁻¹ A ((Matrix.isUnit_iff_isUnit_det P⁻¹).1 (Matrix.isUnit_nonsing_inv_iff.2 h))]

theorem rank_mul_le_right (A : Matrix m n R) (B : Matrix p m R) :
  (B * A).rank ≤ A.rank := Matrix.rank_mul_le_right B A

/-! Informal proof:
(i) $\text{rank}(T_A) = \text{dim}(\text{im}(T_A)) = \text{dim}(\{Ax | x \in k^n\}) = \text{rank}(A)$.
(ii) If $A$ is similar to $B$ then there exists invertible matrix $P$ such that $B = P^{-1} A P$. $\text{rank}(B) = \text{rank}(P^{-1} * A * P) = \text{rank}(P^{-1} * A) = \text{rank}(A)$.
(iii) There exists an injection from $\{Bx | x \in M\}$ to $M$. Therefore, $\text{dim}(\{Bx | x \in M\}) \leq \text{dim}(M)$. Let $M$ be $\{Ax | x \in k^n\}$ then we have completed the proof.

-/
