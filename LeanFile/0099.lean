import Mathlib
/-! Question:
Given two set $T\subset S$. Prove that $\operatorname{Sym}(T)\cong\operatorname{Sym'}(S,S\backslash T)$ is a subgroup of $\operatorname{Sym}(S)$. 
Here is something harder to prove: If $\varnothing\subsetneq T\subsetneq S$ then this subgroup is not normal.
-/
import Mathlib.Tactic

/- Given two sets T ⊆ S. Prove that Sym(T) is a subgroup of Sym(S) -/

instance {S : Type} {T : Set S} : Subgroup (Equiv.Perm S) where
  -- subgroup H = Sym(T)
  carrier := {f : S ≃ S | ∀ x : S, x ∉ T → f x = x}
  -- if f g ∈ H then f * g ∈ H
  mul_mem' := by
    intro f g hf hg
    intro x hx
    dsimp
    rw [hg x hx, hf x hx]
  -- 1 ∈ H
  one_mem' := by
    intro x _
    rfl
  -- if f ∈ H then f⁻¹ ∈ H
  inv_mem' := by
    intro f hf x hx
    exact ((@Equiv.Perm.eq_inv_iff_eq S f x x).mpr (hf x hx)).symm


/-! Informal proof:
Simply verify
-/
