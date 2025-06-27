import Mathlib
/-! Question:
12. Prove that the following groups are not cyclic:
(a) $Z_{2} \times Z_{2}$
(b) $Z_{2} \times \mathbb{Z}$
(c) $\mathbb{Z} \times \mathbb{Z}$.
-/

example : ¬ IsAddCyclic (ZMod 2 × ZMod 2) := by
  by_contra! h
  exact IsAddKleinFour.not_isAddCyclic h

example : ¬ IsAddCyclic (ZMod 2 × ℤ) := by 
  /-Suppose not, if $a=(a_1, a_2)$ is the generator. Consider $(1,0)$. 
 $\exists b, b \times a = (1,0)$.-/
  by_contra! h
  obtain ⟨a, hf⟩ := exists_zsmul_surjective (ZMod 2 × ℤ)
  obtain ⟨b, hb⟩ := hf ⟨1, 0⟩
  have eq : ∀ e : (ZMod 2 × ℤ), ∀ d : ℤ, d • e = ⟨d * e.1, d * e.2⟩ := by
    intro e d
    simp only [zsmul_eq_mul]
    rfl
  simp only [eq, Prod.mk.injEq] at hb
  /-If $a_2=0$, then $(1,1)$ can not be generate by $a$. -/
  by_cases h : a.2 = 0
  · obtain ⟨c, hc⟩ := hf ⟨1, 1⟩
    simp only [eq, Prod.mk.injEq, h, mul_zero] at hc
    exact zero_ne_one hc.2
  · /-If not, we have $b=0$, then $b \times a = (0,0)$, contradiction!-/
    rw [mul_eq_zero] at hb
    simp only [Or.resolve_right hb.2 h, Int.cast_zero, zero_mul] at hb
    exact zero_ne_one hb.1

example : ¬ IsAddCyclic (ℤ × ℤ) := by 
  /-Suppose not, if $a=(a_1, a_2)$ is the generator. Consider $(1,0)$. 
 $\exists b, b \times a = (1,0)$.-/
  by_contra! h
  obtain ⟨a, hf⟩ := exists_zsmul_surjective (ℤ × ℤ)
  obtain ⟨b, hb⟩ := hf ⟨0, 1⟩
  have eq : ∀ e : ℤ × ℤ, ∀ d : ℤ, d • e = ⟨d * e.1, d * e.2⟩ :=fun e d ↦ rfl
  simp only [eq, Prod.mk.injEq] at hb
  /-If $a_2=0$, then $(1,1)$ can not be generate by $a$. -/
  by_cases h : a.1 = 0
  · obtain ⟨c, hc⟩ := hf ⟨1, 1⟩
    simp only [eq, Prod.mk.injEq, h, mul_zero] at hc
    exact zero_ne_one hc.1
  · /-If not, we have $b=0$, then $b \times a = (0,0)$, contradiction!-/
    rw [mul_eq_zero] at hb
    simp only [Or.resolve_right hb.1 h, zero_mul] at hb
    exact zero_ne_one hb.2


/-! Informal proof:
(a) $Z_2×Z_2$ is not cyclic since all the elements are of order eq or less than 2.
(b)Suppose not, if $a=(a_1, a_2)$ is the generator. Consider $(1,0)$. 
 $\exists b, b \times a = (1,0)$. If $a_2=0$, then $(1,1)$ can not be generate by $a$. If not, we have $b=0$, then $b \times a = (0,0)$, contradiction!
\(c)Suppose not, if $a=(a_1, a_2)$ is the generator. Consider $(1,0)$. 
 $\exists b, b \times a = (1,0)$. If $a_2=0$, then $(1,1)$ can not be generate by $a$. If not, we have $b=0$, then $b \times a = (0,0)$, contradiction!
-/
