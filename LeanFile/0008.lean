import Mathlib
/-! Question:
3. Prove the following: when a partially ordered set $X$ satisfies the a.c.c. and the d.c.c., then every chain of elements of $X$ is finite.
-/

set_option linter.unusedVariables false
set_option diagnostics true

variable {P : Type}
variable [PartialOrder P] [LocallyFiniteOrder P]

def acc (f : ℤ → P) (s : Monotone f) : Prop := ∃ n : ℤ, ∀ i ≥ n, f i = f n
def dcc (f : ℤ → P) (s : Monotone f) : Prop := ∃ n : ℤ, ∀ i ≤ n, f i = f n

example : ∀ f : ℤ → P, (s : Monotone f)
                     → (acc f s) ∧ (dcc f s)
                     → Set.Finite (f '' ⊤) := by
  intro f s ⟨⟨u, up⟩, ⟨l, lp⟩⟩
  -- Thus take an arbitrary chain $f$ of $P$, which in lean is instanced as a map from $\N$ to $P$.
  -- We claim that $f$ is finite, argued as follow:
  -- First, the chain is isomorphic to a subset of $\N$,
  -- and any subset of $N$ is finite if it is bounded from above and bounded from bellow.
  apply BddBelow.finite_of_bddAbove
  -- So it suffices to prove that the isomorphic image of $f$ in $\N$ is bounded.
  · simp only [Set.top_eq_univ, Set.image_univ]
    use f l
    intro x ⟨j, w⟩
    rw [← w]
    by_cases jl : j = l
    · rw [jl]
    · by_cases jgel : j ≥ l
      -- By acc, there exists $j \in \N$ such that forall $k \in \N$, if $k \ge j$ we have $f(j) = f(k)$,
      -- and thus the image of $f$ is bounded from above by this $f(j)$, since it is monotone.
      · have jgtl : j > l := by exact lt_of_le_of_ne jgel fun a => jl (id (Eq.symm a))
        exact s jgel
      · -- here we obtain the fact that the natural is a linear order set by contradiction.
        have jltl : j ≤ l := by exact Int.le_of_not_le jgel
        obtain foo := lp j jltl
        exact le_of_eq (id (Eq.symm foo))
  · simp only [Set.top_eq_univ, Set.image_univ]
    use f u
    intro x ⟨j, w⟩
    rw [← w]
    by_cases ju : j = u
    · rw [ju]
    · by_cases jgeu : j ≥ u
      -- By acc, there exists $u \in \N$ such that forall $k \in \N$, if $k \le u$ we have $f(j) = f(k)$,
      -- and thus the image of $f$ is bounded from bellow by this $f(u)$, since it is monotone.
      · have jgtu : j > u := by exact lt_of_le_of_ne jgeu fun a => ju (id (Eq.symm a))
        exact le_of_eq (up j jgeu)
      · -- here we obtain the fact that the natural is a linear order set by contradiction.
        have jltu : j ≤ u := by exact Int.le_of_not_le jgeu
        exact s jltu

-- At last we have the fact that the image of $f$ is bounded,
-- and thus is finite as an isomorphic image of a subset of $\N$.


/-! Informal proof:
Suppose we have a poset $P$ which indeed satisfies acc and dcc.
So any chain of this poset $P$ will have a upper bound and lower bound. 
Thus take an arbitrary chain $f$ of $P$, which in lean is instanced as a map from $\N$ to $P$. We claim that $f$ is finite, argued as follow:
First, the chain is isomorphic to a subset of $\N$, and any subset of $N$ is finite if it is bounded from above and bounded from bellow. So it suffices to prove that the isomorphic image of $f$ in $\N$ is bounded. By acc, there exists $j \in \N$ such that forall $k \in \N$, if $k \ge j$ we have $f(j) = f(k)$, and thus the image of $f$ is bounded from above by this $f(j)$, since it is monotone. By acc, there exists $u \in \N$ such that forall $k \in \N$, if $k \le u$ we have $f(j) = f(k)$, and thus the image of $f$ is bounded from bellow by this $f(u)$, since it is monotone.
At last we have the fact that the image of $f$ is bounded, and thus is finite as an isomorphic image of a subset of $\N$.

-/
