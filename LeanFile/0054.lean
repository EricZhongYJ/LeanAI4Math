import Mathlib
/-! Question:
17. Prove that $G^{(i)}$ is a characteristic subgroup of $G$ for all $i$.
-/
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.Abelianization
import Mathlib.Algebra.Group.Subgroup.Basic

variable {G : Type*} [Group G]
variable (n : ℕ)

-- prove that $G^{(0)}$ is a characteristic subgroup of $G$
lemma G0_is_characteristic : (derivedSeries G 0).Characteristic where
  fixed := by simp

-- prove that $G^{(i)}$ is a characteristic subgroup of $G$ by induction
theorem Gi_is_characteristic (i : ℕ) : (derivedSeries G i).Characteristic := by induction i with
  |zero => apply G0_is_characteristic
  |succ n h => 
  dsimp
  apply Subgroup.commutator_characteristic
/-! Informal proof:
prove that $G^{(0)}$ is a characteristic subgroup of $G$.
prove that $G^{(i)}$ is a characteristic subgroup of $G$ by induction
-/
