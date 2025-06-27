import Mathlib
/-! Question:
*27. If $f \in A(S)$, call, for $s \in S$, the orbit of $s$ (relative to $f$ ) the set $O(s)=$ $\left\{f^{j}(s) \mid\right.$ all integers $\left.j\right\}$. Show that if $s, t \in S$, then either $O(s) \cap O(t)=\varnothing$ or $O(s)=O(t)$.
-/

-- If two orbits are not disjoint, then they have a common element $g$. In group action, $g \in orbit x$ is equal to $orbit g = orbit x$, then two orbits are equal. 
theorem orbit_disjoint_or_eq {G: Type*} [Group G] (f: G ≃* G) :
    let orbit := MulAction.orbit (Subgroup.zpowers f) (α := G)
    ∀ x y, Disjoint (orbit x) (orbit y) ∨ orbit x = orbit y := by
  extract_lets orbit
  intro x y
  rw [Classical.or_iff_not_imp_left]  -- a or b iff not a -> b
  intro h
  rw [Set.not_disjoint_iff] at h
  let ⟨g, hg⟩ := h
  simp [orbit, <-MulAction.orbit_eq_iff] at hg
  aesop

/-! Informal proof:
If two orbits are not disjoint, then they have a common element $g$. In group action, $g \in orbit \space x$ is equal to $orbit \space g = orbit \space x$, then two orbits are equal. 

-/
