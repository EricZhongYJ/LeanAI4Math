import Mathlib
/-! Question:
7. The center of a ring $R$ is $\{z \in R \mid z r=r z$ for all $r \in R\}$ (i.e., is the set of all elements which commute with every element of $R$ ). Prove that the center of a ring is a subring that contains the identity. Prove that the center of a division ring is a field.
-/

-- The center of a ring forms a subring containing the identity
#check Subring.center

/-- The center of a division ring is a field -/
def center_division_ring_is_field (R : Type*) [DivisionRing R] : 
  Field (Subring.center R) := by exact Subring.instField

/-! Informal proof:
Mathlib4库里已有.
-/
