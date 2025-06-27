import Mathlib
/-! Question:
24. Describe all ring homomorphisms of $\mathbb{Z}$ into $\mathbb{Z} \times \mathbb{Z}$.
-/


/-
Describe all ring homomorphisms of $\mathbb{Z}$ into $\mathbb{Z} \times \mathbb{Z}$.
It is well-know that the only ring homomorphisms of $\mathbb{Z}$ into $\mathbb{Z}$ is the identity map.
Suppose $\phi : x \mapsto (\phi_1 x, \phi_2 x)$, then $\phi_1$ and $\phi_2$ are both ring homomorphisms
 of $\mathbb{Z}$ into $\mathbb{Z}$,Hence $\phi_1$ and $\phi_2$ is ideantity.
-/

lemma UnexploredExercise_2549{f : ℤ →+* ℤ × ℤ} : f = RingHom.prod (RingHom.id ℤ) (RingHom.id ℤ) :=
  /-It is well-know that the only ring homomorphisms of $\mathbb{Z}$ into $\mathbb{Z}$ is the identity map.
  Suppose $\phi : x \mapsto (\phi_1 x, \phi_2 x)$, then $\phi_1$ and $\phi_2$ are both ring homomorphisms
  of $\mathbb{Z}$ into $\mathbb{Z}$,Hence $\phi_1$ and $\phi_2$ is ideantity.-/
  RingHom.ext_int f ((RingHom.id ℤ).prod (RingHom.id ℤ))

/-! Informal proof:
Describe all ring homomorphisms of $\mathbb{Z}$ into $\mathbb{Z} \times \mathbb{Z}$.
It is well-know that the only ring homomorphisms of $\mathbb{Z}$ into $\mathbb{Z}$ is the identity map.
Suppose $\phi : x \mapsto (\phi_1 x, \phi_2 x)$, then $\phi_1$ and $\phi_2$ are both ring homomorphisms
 of $\mathbb{Z}$ into $\mathbb{Z}$,Hence $\phi_1$ and $\phi_2$ is ideantity.
-/
