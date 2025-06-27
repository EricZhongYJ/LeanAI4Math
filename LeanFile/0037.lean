import Mathlib
/-! Question:
*4.40 Let $R$ be a commutative ring, let $D: \operatorname{Mat}_{n}(R) \rightarrow R$ be a determinant function, and let $A$ be an $n \times n$ matrix with rows $\alpha_{1}, \ldots, \alpha_{n}$. Define $d: R^{n} \rightarrow R$ by $d_{i}(\beta)=D\left(\alpha_{i}, \ldots, \alpha_{i-1}, \beta, \alpha_{i+1}, \ldots, \alpha_{n}\right)$.
(i) If $i \
eq j$ and $r \in R$, prove that
\[
d_{i}\left(r \alpha_{j}\right)=0 .
\]
(ii) If $i \
eq j$ and $r \in R$, prove that $d_{i}\left(\alpha_{i}+r \alpha_{j}\right)=D(A)$.
(iii) If $r_{j} \in R$, prove that
\[
d_{i}\left(\alpha_{i}+\sum_{j \
eq i} r_{j} \alpha_{j}\right)=D(A) .
\]
-/



/- Question
Let $R$ be a commutative ring, let $D: \operatorname{Mat}_{n}(R) \rightarrow R$ be a determinant function, and let $A$ be an $n \times n$ matrix with rows $\alpha_{1}, \ldots, \alpha_{n}$. Define $d: R^{n} \rightarrow R$ by $d_{i}(\beta)=D\left(\alpha_{i}, \ldots, \alpha_{i-1}, \beta, \alpha_{i+1}, \ldots, \alpha_{n}\right)$.

(i) If $i \
eq j$ and $r \in R$, prove that

$$
d_{i}\left(r \alpha_{j}\right)=0 .
$$

(ii) If $i \
eq j$ and $r \in R$, prove that $d_{i}\left(\alpha_{i}+r \alpha_{j}\right)=D(A)$.

(iii) If $r_{j} \in R$, prove that

$$
d_{i}\left(\alpha_{i}+\sum_{j \
eq i} r_{j} \alpha_{j}\right)=D(A) .
$$
-/



-- Let $R$ be a commutative ring
variable {R : Type*} [CommRing R] [DecidableEq R]

-- let $D: \operatorname{Mat}_{n}(R) \rightarrow R$ be a determinant function
variable {n : Type*} [Fintype n] [DecidableEq n]
def D : Matrix n n R → R := Matrix.det

-- Define $d: R^{n} \rightarrow R$ by $d_{i}(\beta)=D\left(\alpha_{i}, \ldots, \alpha_{i-1}, \beta, \alpha_{i+1}, \ldots, \alpha_{n}\right)$.
def d (A : Matrix n n R) (i : n) (β : n → R) : R :=
  D (A.updateRow i β)



-- (i) If $i \
eq j$ and $r \in R$, prove that $ d_{i}\left(r \alpha_{j}\right)=0 .$
example {A : Matrix n n R} {r : R} {i j : n} (hij : i ≠ j) :
    d A i (r • (A j)) = 0 := by
  dsimp [d, D]
  -- $d_i (r \alpha_j) = r d_i (r \alpha_j) = r \cdot 0 = 0$
  rw [Matrix.det_updateRow_smul]
  rw [Matrix.det_updateRow_eq_zero hij.symm]
  rw [mul_zero]



-- (ii) If $i \
eq j$ and $r \in R$, prove that $d_{i}\left(\alpha_{i}+r \alpha_{j}\right)=D(A)$.
example {A : Matrix n n R} {r : R} {i j : n} (hij : i ≠ j) :
    d A i (A i + r • (A j)) = D A := by
  dsimp [d, D]
  rw [Matrix.det_updateRow_add_smul_self]
  exact hij

-- (iii) If $r_{j} \in R$, prove that $d_{i}\left(\alpha_{i}+\sum_{j \
eq i} r_{j} \alpha_{j}\right)=D(A) .$
example {A : Matrix n n R} {i : n} {s : Finset n} (r : n → R) (hs : s = univ \ {i}):
    d A i (A i + ∑ j ∈ s, r j • A j) = D A := by
  dsimp [d, D]
  -- Simply by induction, using the result above, we can prove it.
  have hi : i ∉ s := by simp [hs]
  have : ∀ s', i ∉ s' → (A.updateRow i (A i + ∑ j ∈ s', r j • A j)).det = A.det := by
    intro s hs
    induction s using Finset.induction_on with
    | empty => simp
    | @insert j s' hj h_ind =>
      have h : j ≠ i := by
        apply ne_of_mem_of_not_mem _ hs
        exact Finset.mem_insert_self j s'
      rw [Finset.sum_insert hj, add_comm ((r j) • A j), ← add_assoc, Matrix.det_updateRow_add,
          Matrix.det_updateRow_smul, Matrix.det_updateRow_eq_zero h, mul_zero, add_zero, h_ind]
      exact fun a => hs ((Finset.subset_insert j s') a)
  exact this s hi

/-! Informal proof:
i) 
If we repeat a row of a matrix, we get a matrix of determinant zero, then we have:
$$
d_i (r \alpha_j) = r d_i (r \alpha_j) = r \cdot 0 = 0
$$
ii)
This is a basic property of determinant, and it's already in mathlib.
iii)
Simply by induction, using the result above, we can prove it.
-/
