import Mathlib
/-! Question:
37. If $G$ is a nonabelian group of order 6 , prove that $G \simeq S_{3}$.
-/
import Mathlib.Tactic
import Mathlib.Data.Fintype.Basic
import Mathlib.GroupTheory.Perm.Cycle.Concrete
import Mathlib.GroupTheory.Perm.Subgroup

/- If G is a nonabelian group of order 6, prove that G ≃ S₃ -/

open Equiv
open Function

-- some trivial but useful lemmas
lemma eqtwoofne (n : Fin 3) : n ≠ 0 → n ≠ 1 → n = 2 := by
  intro n0 n1
  fin_omega

lemma eqsixofne (n : Fin 7) : n ≠ 0 → n ≠ 1 → n ≠ 2 → n ≠ 3 → n ≠ 4 → n ≠ 5 → n = 6 := by
  intro n0 n1 n2 n3 n4 n5
  fin_omega

variable {G : Type*} [Group G] [Fintype G] {hcard : Fintype.card G = 6} {a b : G} {hab : a * b ≠ b * a}

-- the following tedious arguments are to show that 1, a, b, ab, ba are five distinct elements of G, and except them there is only one element left.
omit [Fintype G] in theorem aneone (hab : a * b ≠ b * a) : a ≠ 1 := by
    by_contra aeqone
    rw [aeqone, mul_one, one_mul] at hab
    exact hab rfl
omit [Fintype G] in theorem bneone (hab : a * b ≠ b * a) : b ≠ 1 := by
    by_contra beqone
    rw [beqone, mul_one, one_mul] at hab
    exact hab rfl
omit [Fintype G] in theorem aneb (hab : a * b ≠ b * a) : a ≠ b := by
    by_contra aeqb
    rw [aeqb] at hab
    exact hab rfl
omit [Fintype G] in theorem aneab (hab : a * b ≠ b * a) : a ≠ a * b := by
    by_contra aeqab
    symm at aeqab
    apply mul_right_eq_self.mp at aeqab
    exact bneone hab aeqab
omit [Fintype G] in theorem aneba (hab : a * b ≠ b * a) : a ≠ b * a := by
    by_contra aeqba
    symm at aeqba
    apply mul_left_eq_self.mp at aeqba
    exact bneone hab aeqba
omit [Fintype G] in theorem bneab (hab : a * b ≠ b * a) : b ≠ a * b := by
    by_contra beqab
    symm at beqab
    apply mul_left_eq_self.mp at beqab
    exact aneone hab beqab
omit [Fintype G] in theorem bneba (hab : a * b ≠ b * a) : b ≠ b * a := by
    by_contra beqba
    symm at beqba
    apply mul_right_eq_self.mp at beqba
    exact aneone hab beqba
omit [Fintype G] in theorem abneone (hab : a * b ≠ b * a) : a * b ≠ 1 := by
    by_contra abeqone
    have inv : a = b⁻¹ := by exact eq_inv_of_mul_eq_one_left abeqone
    rw [inv, mul_inv_cancel, inv_mul_cancel] at hab
    exact hab rfl
omit [Fintype G] in theorem baneone (hab : a * b ≠ b * a) : b * a ≠ 1 := by
    by_contra baeqone
    have inv : a = b⁻¹ := by exact Eq.symm (DivisionMonoid.inv_eq_of_mul b a baeqone)
    rw [inv, mul_inv_cancel, inv_mul_cancel] at hab
    exact hab rfl
omit [Fintype G] in theorem abneba (hab : a * b ≠ b * a) : a * b ≠ b * a := hab


-- for G and noncommutative pairs a, b, we first prove that if a²≠1 then G ≃* S₃ via map a ↦ c[1, 2, 3] and b ↦ c[1, 2],  then prove the same when both a²=b²=1. So first we introduce the following intermediate lemma
lemma intermediate {G : Type*} [Group G] [Fintype G] (hcard : Fintype.card G = 6) {a b : G} {hab : a * b ≠ b * a} {asqneone : a * a ≠ 1} : ∃ (f : G ≃* Perm (Fin 3)), f = f := by
  let G5 (x : G) := x = 1 ∨ x = a ∨ x = b ∨ x = a * b ∨ x = b * a
  have G5n0 (z : G) : ¬ G5 z → z ≠ 1 := by
      intro hz
      dsimp [G5] at hz
      push_neg at hz
      exact hz.1
  have G5n1 (z : G) : ¬ G5 z → z ≠ a := by
      intro hz
      dsimp [G5] at hz
      push_neg at hz
      exact hz.2.1
  have G5n2 (z : G) : ¬ G5 z → z ≠ b := by
      intro hz
      dsimp [G5] at hz
      push_neg at hz
      exact hz.2.2.1
  have G5n3 (z : G) : ¬ G5 z → z ≠ a * b := by
      intro hz
      dsimp [G5] at hz
      push_neg at hz
      exact hz.2.2.2.1
  have G5n4 (z : G) : ¬ G5 z → z ≠ b * a := by
      intro hz
      dsimp [G5] at hz
      push_neg at hz
      exact hz.2.2.2.2
    -- we show that there remains exactly one element of G distinct from the above five, by constructing a injection from Fin 7 to G to lead a contradiction
  have elem5 : ∀ (x y : G), ¬ G5 x ∧ ¬ G5 y → x = y := by
    by_contra h
    push_neg at h
    rcases h with ⟨x, y, ⟨⟨hx, hy⟩, hxy⟩⟩

    let f : Fin 7 → G := by
      intro n
      if n = 0 then exact 1
      else if n = 1 then exact a
      else if n = 2 then exact b
      else if n = 3 then exact a * b
      else if n = 4 then exact b * a
      else if n = 5 then exact x
      else exact y
    have inj_f : Injective f := by
      intro s t hst
      if s0 : s = 0 then
        if t0 : t = 0 then rw [s0, t0]
        else if t1 : t = 1 then rw [s0, t1] at hst; dsimp [f] at hst; symm at hst; absurd hst; exact aneone hab
        else if t2 : t = 2 then rw [s0, t2] at hst; dsimp [f] at hst; symm at hst; absurd hst; exact bneone hab
        else if t3 : t = 3 then rw [s0, t3] at hst; dsimp [f] at hst; symm at hst; absurd hst; exact abneone hab
        else if t4 : t = 4 then rw [s0, t4] at hst; dsimp [f] at hst; symm at hst; absurd hst; exact baneone hab
        else if t5 : t = 5 then rw [s0, t5] at hst; dsimp [f] at hst; symm at hst; have : x ≠ 1 := (G5n0 x hx); absurd hst; exact this
        else
          have t6 : f t = y := by dsimp [f]; split; contradiction; rfl;
          rw [s0, t6] at hst
          dsimp [f] at hst
          symm at hst
          have : y ≠ 1 := (G5n0 y hy)
          contradiction
      else if s1 : s = 1 then
        if t1 : t = 1 then rw [s1, t1]
        else if t0 : t = 0 then rw [s1, t0] at hst; dsimp [f] at hst; absurd hst; exact aneone hab
        else if t2 : t = 2 then rw [s1, t2] at hst; dsimp [f] at hst; absurd hst; exact aneb hab
        else if t3 : t = 3 then rw [s1, t3] at hst; dsimp [f] at hst; absurd hst; exact aneab hab
        else if t4 : t = 4 then rw [s1, t4] at hst; dsimp [f] at hst; absurd hst; exact aneba hab
        else if t5 : t = 5 then rw [s1, t5] at hst; dsimp [f] at hst; symm at hst; have : x ≠ a := (G5n1 x hx); contradiction
        else
          have t6 : f t = y := by dsimp [f]; split; contradiction; rfl;
          rw [s1, t6] at hst
          dsimp [f] at hst
          symm at hst
          have : y ≠ a := (G5n1 y hy)
          contradiction
      else if s2 : s = 2 then
        if t2 : t = 2 then rw [s2, t2]
        else if t0 : t = 0 then rw [s2, t0] at hst; dsimp [f] at hst; absurd hst; exact bneone hab
        else if t1 : t = 1 then rw [s2, t1] at hst; dsimp [f] at hst; absurd hst.symm; exact aneb hab
        else if t3 : t = 3 then rw [s2, t3] at hst; dsimp [f] at hst; absurd hst; exact bneab hab
        else if t4 : t = 4 then rw [s2, t4] at hst; dsimp [f] at hst; absurd hst; exact bneba hab
        else if t5 : t = 5 then rw [s2, t5] at hst; dsimp [f] at hst; symm at hst; have : x ≠ b := (G5n2 x hx); contradiction
        else
          have t6 : f t = y := by dsimp [f]; split; contradiction; rfl;
          rw [s2, t6] at hst
          dsimp [f] at hst
          symm at hst
          have : y ≠ b := (G5n2 y hy)
          contradiction
      else if s3 : s = 3 then
        if t3 : t = 3 then rw [s3, t3]
        else if t0 : t = 0 then rw [s3, t0] at hst; dsimp [f] at hst; absurd hst; exact abneone hab
        else if t1 : t = 1 then rw [s3, t1] at hst; dsimp [f] at hst; absurd hst.symm; exact aneab hab
        else if t2 : t = 2 then rw [s3, t2] at hst; dsimp [f] at hst; absurd hst.symm; exact bneab hab
        else if t4 : t = 4 then rw [s3, t4] at hst; dsimp [f] at hst; contradiction
        else if t5 : t = 5 then rw [s3, t5] at hst; dsimp [f] at hst; symm at hst; have : x ≠ a * b := (G5n3 x hx); contradiction
        else
          have t6 : f t = y := by dsimp [f]; split; contradiction; rfl;
          rw [s3, t6] at hst
          dsimp [f] at hst
          symm at hst
          have : y ≠ a * b := (G5n3 y hy)
          contradiction
      else if s4 : s = 4 then
        if t4 : t = 4 then rw [s4, t4]
        else if t0 : t = 0 then rw [s4, t0] at hst; dsimp [f] at hst; absurd hst; exact baneone hab
        else if t1 : t = 1 then rw [s4, t1] at hst; dsimp [f] at hst; absurd hst.symm; exact aneba hab
        else if t2 : t = 2 then rw [s4, t2] at hst; dsimp [f] at hst; absurd hst.symm; exact bneba hab
        else if t3 : t = 3 then rw [s4, t3] at hst; dsimp [f] at hst; symm at hst; contradiction
        else if t5 : t = 5 then rw [s4, t5] at hst; dsimp [f] at hst; symm at hst; have : x ≠ b * a := (G5n4 x hx); contradiction
        else
          have t6 : f t = y := by dsimp [f]; split; contradiction; rfl;
          rw [s4, t6] at hst
          dsimp [f] at hst
          symm at hst
          have : y ≠ b * a := (G5n4 y hy)
          contradiction
      else if s5 : s = 5 then
        if t5 : t = 5 then rw [s5, t5]
        else if t0 : t = 0 then rw [s5, t0] at hst; dsimp [f] at hst; have : x ≠ 1 := (G5n0 x hx); contradiction
        else if t1 : t = 1 then rw [s5, t1] at hst; dsimp [f] at hst; have : x ≠ a := (G5n1 x hx); contradiction
        else if t2 : t = 2 then rw [s5, t2] at hst; dsimp [f] at hst; have : x ≠ b := (G5n2 x hx); contradiction
        else if t3 : t = 3 then rw [s5, t3] at hst; dsimp [f] at hst; have : x ≠ a * b := (G5n3 x hx); contradiction
        else if t4 : t = 4 then rw [s5, t4] at hst; dsimp [f] at hst; have : x ≠ b * a := (G5n4 x hx); contradiction
        else
          have t6 : f t = y := by dsimp [f]; split; contradiction; rfl;
          rw [s5, t6] at hst
          dsimp [f] at hst
          symm at hst
          have : y ≠ x := hxy.symm
          contradiction
      else
        have s6 : f s = y := by dsimp [f]; split; contradiction; rfl
        if t0 : t = 0 then rw [s6, t0] at hst; dsimp [f] at hst; have : y ≠ 1 := (G5n0 y hy); contradiction
        else if t1 : t = 1 then rw [s6, t1] at hst; dsimp [f] at hst; have : y ≠ a := (G5n1 y hy); contradiction
        else if t2 : t = 2 then rw [s6, t2] at hst; dsimp [f] at hst; have : y ≠ b := (G5n2 y hy); contradiction
        else if t3 : t = 3 then rw [s6, t3] at hst; dsimp [f] at hst; have : y ≠ a * b := (G5n3 y hy); contradiction
        else if t4 : t = 4 then rw [s6, t4] at hst; dsimp [f] at hst; have : y ≠ b * a := (G5n4 y hy); contradiction
        else if t5 : t = 5 then rw [s6, t5] at hst; dsimp [f] at hst; symm at hst; contradiction
        else
          have seq6 : s = 6 := eqsixofne s s0 s1 s2 s3 s4 s5
          have teq6 : t = 6 := eqsixofne t t0 t1 t2 t3 t4 t5
          rw [seq6, teq6]
    have card7: Fintype.card (Fin 7) ≤ Fintype.card G := by exact Fintype.card_le_of_injective f inj_f
    rw [hcard] at card7
    simp at card7
  have asqnea : a * a ≠ a := by
    by_contra asqeqa
    nth_rw 3 [← mul_one a] at asqeqa
    apply mul_left_cancel at asqeqa
    exact aneone hab asqeqa
  have asqneb : a * a ≠ b := by
    by_contra asqeqb
    rw [asqeqb.symm, mul_assoc] at hab
    exact hab rfl
  have asqneab : a * a ≠ a * b := by
    by_contra asqeqab
    apply mul_left_cancel at asqeqab
    exact aneb hab asqeqab
  have asqneba : a * a ≠ b * a := by
    by_contra asqeqba
    apply mul_right_cancel at asqeqba
    exact aneb hab asqeqba

  have asqnG5 : ¬ G5 (a * a) := by
        dsimp [G5]
        push_neg
        exact ⟨asqneone, ⟨asqnea, ⟨asqneb, ⟨asqneab, asqneba⟩⟩⟩⟩
  have e5asq : ∀ x : G, x ≠ 1 → x ≠ a → x ≠ b → x ≠ a * b → x ≠ b * a → x = a * a := by
        intro x x1 x2 x3 x4 x5
        have xnG5 : ¬ G5 x := by
          dsimp [G5]
          push_neg
          exact ⟨x1, ⟨x2, ⟨x3, ⟨x4, x5⟩⟩⟩⟩
        exact elem5 x (a * a) ⟨xnG5, asqnG5⟩
      --check a³ ≠ a, b, ab, ba, a²
  have acbnea : a * a * a ≠ a := by
        by_contra acbeqa
        nth_rw 4 [← one_mul a] at acbeqa
        apply mul_right_cancel at acbeqa
        exact asqneone acbeqa
  have acbneb : a * a * a ≠ b := by
        by_contra acbeqb
        rw [acbeqb.symm, ← mul_assoc, ← mul_assoc] at hab
        exact hab rfl
  have acbneab : a * a * a ≠ a * b := by
        by_contra acbeqab
        rw [mul_assoc] at acbeqab
        apply mul_left_cancel at acbeqab
        exact asqneb acbeqab
  have acbneba : a * a * a ≠ b * a := by
        by_contra acbeqba
        apply mul_right_cancel at acbeqba
        exact asqneb acbeqba
  have acbneasq : a * a * a ≠ a * a := by
        by_contra acbeqasq
        nth_rw 2 [← mul_one (a * a)] at acbeqasq
        apply mul_left_cancel at acbeqasq
        exact aneone hab acbeqasq
      -- we conclude that a³=1
  have acbeqone : a * a * a = 1 := by
        by_contra acbneone
        have acbeqasq : a * a * a = a * a := e5asq (a * a * a) acbneone acbnea acbneb acbneab acbneba
        exact acbneasq acbeqasq
      -- check b²≠a, b, ab, ba, a²
  have bsqnea : b * b ≠ a := by
        by_contra bsqeqa
        rw [bsqeqa.symm, mul_assoc] at hab
        exact hab rfl
  have bsqneb : b * b ≠ b := by
        by_contra bsqeqb
        nth_rw 3 [← mul_one b] at bsqeqb
        apply mul_left_cancel at bsqeqb
        exact bneone hab bsqeqb
  have bsqneab : b * b ≠ a * b := by
        by_contra bsqeqab
        apply mul_right_cancel at bsqeqab
        exact (aneb hab).symm bsqeqab
  have bsqneba : b * b ≠ b * a := by
        by_contra bsqeqba
        apply mul_left_cancel at bsqeqba
        exact (aneb hab).symm bsqeqba
  have bsqneasq : b * b ≠ a * a := by
        by_contra bsqeqasq
        have bbaeqacb : b * b * a = a * a * a := by
          rw [bsqeqasq]
        rw [acbeqone] at bbaeqacb
        have aeqbsqinv : a = (b * b)⁻¹ := by
          exact (mul_eq_one_iff_inv_eq.mp bbaeqacb).symm
        rw [aeqbsqinv, Group.toDivisionMonoid.proof_2, mul_assoc, inv_mul_cancel, mul_one, ← mul_assoc, mul_inv_cancel, one_mul] at hab
        exact hab rfl
  have bsqeqone : b * b = 1 := by
        by_contra bsqneone
        have bsqnG5 : ¬ G5 (b * b) := by
          dsimp [G5]
          push_neg
          exact ⟨bsqneone, ⟨bsqnea, ⟨bsqneb, ⟨bsqneab, bsqneba⟩⟩⟩⟩
        have bsqeqasq : b * b = a * a := by
          exact elem5 (b * b) (a * a) ⟨bsqnG5, asqnG5⟩
        contradiction
      -- now we define a isomorphism f : G ≃* S₃ in case a²≠1, where a and b are respectively sent to c[1, 2, 3] and c[1, 2]
  let f : G → Perm (Fin 3) := by
        intro x
        if x = 1 then exact c[1]
        else if x = a then exact c[1, 2, 3]
        else if x = b then exact c[1, 2]
        else if x = a * b then exact c[1, 2, 3] * c[1, 2]
        else if x = b * a then exact c[1, 2] * c[1, 2, 3]
        else exact c[1, 2, 3] * c[1, 2, 3]

  have fone : f 1 = c[1] := by
        dsimp [f]
        split
        rfl
        contradiction
  have fa : f a = c[1, 2, 3] := by
        simp [f, aneone hab]
  have fb : f b = c[1, 2] := by
        simp [f, bneone hab]
        exact (aneb hab).symm
  have fab : f (a * b) = c[1, 2, 3] * c[1, 2] := by
        simp [f, abneone hab, (aneab hab).symm, aneone hab]
  have fba : f (b * a) = c[1, 2] * c[1, 2, 3] := by
        simp [f, baneone hab, (aneba hab).symm, (bneba hab).symm, (abneba hab).symm]
  have fasq : f (a * a) = c[1, 2, 3] * c[1, 2, 3] := by
        simp [f, asqneone, asqnea, asqneb, asqneab, asqneba]
      --prove that f is injective
  have inj_f : Injective f := by
        intro x y hxy
        if x0 : x = 1 then
          if y0 : y = 1 then rw [x0, y0]
          else if y1 : y = a then rw [x0, y1, fone, fa] at hxy; have : c[(1 : Fin 3)] ≠ c[1, 2, 3] := ne_of_beq_false rfl; absurd hxy; exact this
          else if y2 : y = b then rw [x0, y2, fone, fb] at hxy; have : c[(1 : Fin 3)] ≠ c[1, 2] := ne_of_beq_false rfl; absurd hxy; exact this
          else if y3 : y = a * b then rw [x0, y3, fone, fab] at hxy; have : c[(1 : Fin 3)] ≠ c[1, 2, 3] * c[1, 2] := ne_of_beq_false rfl; absurd hxy; exact this
          else if y4 : y = b * a then rw [x0, y4, fone, fba] at hxy; have : c[(1 : Fin 3)] ≠ c[1, 2] * c[1, 2, 3] := ne_of_beq_false rfl; absurd hxy; exact this
          else
            have y5 := e5asq y y0 y1 y2 y3 y4
            rw [x0, y5, fone, fasq] at hxy
            have : c[(1 : Fin 3)] ≠ c[1, 2, 3] * c[1, 2, 3] := ne_of_beq_false rfl; absurd hxy; exact this
        else if x1 : x = a then
          if y1 : y = a then rw [x1, y1]
          else if y0 : y = 1 then rw [x1, y0, fa, fone] at hxy; have : c[(1 : Fin 3), 2, 3] ≠ 1 := ne_of_beq_false rfl; absurd hxy; exact this
          else if y2 : y = b then rw [x1, y2, fa, fb] at hxy; have : c[(1 : Fin 3), 2, 3] ≠ c[1, 2] := ne_of_beq_false rfl; absurd hxy; exact this
          else if y3 : y = a * b then rw [x1, y3, fa, fab] at hxy; have : c[(1 : Fin 3), 2, 3] ≠ c[1, 2, 3] * c[1, 2] := ne_of_beq_false rfl; absurd hxy; exact this
          else if y4 : y = b * a then rw [x1, y4, fa, fba] at hxy; have : c[(1 : Fin 3), 2, 3] ≠ c[1, 2] * c[1, 2, 3] := ne_of_beq_false rfl; absurd hxy; exact this
          else
            have y5 := e5asq y y0 y1 y2 y3 y4
            rw [x1, y5, fa, fasq] at hxy
            have : c[(1 : Fin 3), 2, 3] ≠ c[1, 2, 3] * c[1, 2, 3] := ne_of_beq_false rfl
            absurd hxy; exact this
        else if x2 : x = b then
          if y2 : y = b then rw [x2, y2]
          else if y0 : y = 1 then rw [x2, y0, fb, fone] at hxy; have : c[(1 : Fin 3), 2] ≠ 1 := ne_of_beq_false rfl; absurd hxy; exact this
          else if y1 : y = a then rw [x2, y1, fb, fa] at hxy; have : c[(1 : Fin 3), 2] ≠ c[1, 2, 3] := ne_of_beq_false rfl; absurd hxy; exact this
          else if y3 : y = a * b then rw [x2, y3, fb, fab] at hxy; have : c[(1 : Fin 3), 2] ≠ c[1, 2, 3] * c[1, 2] := ne_of_beq_false rfl; absurd hxy; exact this
          else if y4 : y = b * a then rw [x2, y4, fb, fba] at hxy; have : c[(1 : Fin 3), 2] ≠ c[1, 2] * c[1, 2, 3] := ne_of_beq_false rfl;absurd hxy; exact this
          else
            have y5 := e5asq y y0 y1 y2 y3 y4
            rw [x2, y5, fb, fasq] at hxy
            have : c[(1 : Fin 3), 2] ≠ c[1, 2, 3] * c[1, 2, 3] := ne_of_beq_false rfl
            absurd hxy; exact this
        else if x3 : x = a * b then
          if y3 : y = a * b then rw [x3, y3]
          else if y0 : y = 1 then rw [x3, y0, fab, fone] at hxy; have : c[(1 : Fin 3), 2, 3] * c[1, 2] ≠ 1 := Ne.symm (ne_of_beq_false rfl); absurd hxy; exact this
          else if y1 : y = a then rw [x3, y1, fab, fa] at hxy; have : c[(1 : Fin 3), 2, 3] * c[1, 2] ≠ c[1, 2, 3] := Ne.symm (ne_of_beq_false rfl); absurd hxy; exact this
          else if y2 : y = b then rw [x3, y2, fab, fb] at hxy; have : c[(1 : Fin 3), 2, 3] * c[1, 2] ≠ c[1, 2] := Ne.symm (ne_of_beq_false rfl); absurd hxy; exact this
          else if y4 : y = b * a then rw [x3, y4, fab, fba] at hxy; have : c[(1 : Fin 3), 2, 3] * c[1, 2] ≠ c[1, 2] * c[1, 2, 3] := Ne.symm (ne_of_beq_false rfl); absurd hxy; exact this
          else
            have y5 := e5asq y y0 y1 y2 y3 y4
            rw [x3, y5, fab, fasq] at hxy
            have : c[(1 : Fin 3), 2, 3] * c[1, 2] ≠ c[1, 2, 3] * c[1, 2, 3] := Ne.symm (ne_of_beq_false rfl)
            absurd hxy; exact this
        else if x4 : x = b * a then
          if y4 : y = b * a then rw [x4, y4]
          else if y0 : y = 1 then rw [x4, y0, fba, fone] at hxy; have : c[(1 : Fin 3), 2] * c[1, 2, 3] ≠ 1 := Ne.symm (ne_of_beq_false rfl); absurd hxy; exact this
          else if y1 : y = a then rw [x4, y1, fba, fa] at hxy; have : c[(1 : Fin 3), 2] * c[1, 2, 3] ≠ c[1, 2, 3] := Ne.symm (ne_of_beq_false rfl); absurd hxy; exact this
          else if y2 : y = b then rw [x4, y2, fba, fb] at hxy; have : c[(1 : Fin 3), 2] * c[1, 2, 3] ≠ c[1, 2] := Ne.symm (ne_of_beq_false rfl); absurd hxy; exact this
          else if y3 : y = a * b then rw [x4, y3, fba, fab] at hxy; have : c[(1 : Fin 3), 2] * c[1, 2, 3] ≠ c[1, 2, 3] * c[1, 2] := ne_of_beq_false rfl; absurd hxy; exact this
          else
            have y5 := e5asq y y0 y1 y2 y3 y4
            rw [x4, y5, fba, fasq] at hxy
            have : c[(1 : Fin 3), 2] * c[1, 2, 3] ≠ c[1, 2, 3] * c[1, 2, 3] := Ne.symm (ne_of_beq_false rfl)
            absurd hxy; exact this
        else
          have x5 := e5asq x x0 x1 x2 x3 x4
          if y0 : y = 1 then rw [x5, y0, fasq, fone] at hxy; have : c[(1 : Fin 3), 2, 3] * c[1, 2, 3] ≠ 1 := ne_of_beq_false rfl; absurd hxy; exact this
          else if y1 : y = a then rw [x5, y1, fasq, fa] at hxy; have : c[(1 : Fin 3), 2, 3] * c[1, 2, 3] ≠ c[1, 2, 3] := ne_of_beq_false rfl; absurd hxy; exact this
          else if y2 : y = b then rw [x5, y2, fasq, fb] at hxy; have : c[(1 : Fin 3), 2, 3] * c[1, 2, 3] ≠ c[1, 2] := ne_of_beq_false rfl; absurd hxy; exact this
          else if y3 : y = a * b then rw [x5, y3, fasq, fab] at hxy; have : c[(1 : Fin 3), 2, 3] * c[1, 2, 3] ≠ c[1, 2, 3] * c[1, 2] := ne_of_beq_false rfl; absurd hxy;exact this
          else if y4 : y = b * a then rw [x5, y4, fasq, fba] at hxy; have : c[(1 : Fin 3), 2, 3] * c[1, 2, 3] ≠ c[1, 2] * c[1, 2, 3] := ne_of_beq_false rfl; absurd hxy; exact this
          else
            have y5 := e5asq y y0 y1 y2 y3 y4
            rw [x5, y5]
      -- f is a set equivalence from that f is injective and card G = card S₃
  have cardeq : Fintype.card G = Fintype.card (Perm (Fin 3)) := by rw [hcard]; rfl
  have bij_f := (@Fintype.bijective_iff_injective_and_card G (Perm (Fin 3)) _ _ f).mpr ⟨inj_f, cardeq⟩
  let equiv_f := ofBijective f bij_f
  -- check that f commutes with multiplication
  have aabeqba : a * a * b = b * a := by
        have bab'0 : b * a * b⁻¹ ≠ 1 := by
          by_contra bab'
          rw [mul_inv_eq_iff_eq_mul, one_mul] at bab'
          exact bneba hab bab'.symm
        have bab'1 : b * a * b⁻¹ ≠ a := by
          by_contra bab'
          rw [mul_inv_eq_iff_eq_mul] at bab'
          exact abneba hab bab'.symm
        have bab'2 : b * a * b⁻¹ ≠ b := by
          by_contra bab'
          rw [mul_inv_eq_iff_eq_mul] at bab'
          apply mul_left_cancel at bab'
          exact aneb hab bab'
        have bab'3 : b * a * b⁻¹ ≠ a * b := by
          by_contra bab'
          rw [mul_inv_eq_iff_eq_mul, mul_assoc, bsqeqone, mul_one] at bab'
          exact aneba hab bab'.symm
        have bab'4 : b * a * b⁻¹ ≠ b * a := by
          by_contra bab'
          rw [mul_inv_eq_iff_eq_mul] at bab'
          nth_rw 1 [← mul_one (b * a)] at bab'
          apply (mul_left_cancel) at bab'
          exact bneone hab bab'.symm
        have bab'5 := e5asq (b * a * b⁻¹) bab'0 bab'1 bab'2 bab'3 bab'4
        rw [mul_inv_eq_iff_eq_mul] at bab'5
        exact bab'5.symm
  have abaeqb : a * b * a = b := by
        rw [mul_assoc, ← aabeqba, ← mul_assoc, ← mul_assoc, acbeqone, one_mul]
  have baaeqab : b * a * a = a * b := by
        have eq1 : a * b * a * a * a = b * a * a := by rw [abaeqb]
        have eq2 : a * b * a * a * a = a * b * (a * a * a) := by simp only [mul_assoc]
        rw [eq2, acbeqone, mul_one] at eq1
        exact eq1.symm
  have babeqasq : b * a * b = a * a := by
        have eq1 : b * a * b = a * a * (b * b) := by rw [← mul_assoc, aabeqba]
        rw [eq1, bsqeqone, mul_one]
  have mul_f : ∀ x y : G, f (x * y) = f x * f y := by
        intro x y
        if x0 : x = 1 then
          if y0 : y = 1 then rw [x0, y0, one_mul, fone]; exact rfl
          else if y1 : y = a then rw [x0, y1, one_mul, fone, fa]; exact rfl
          else if y2 : y = b then rw [x0, y2, one_mul, fone, fb];  exact rfl
          else if y3 : y = a * b then rw [x0, y3, one_mul, fone, fab]; exact rfl
          else if y4 : y = b * a then rw [x0, y4, one_mul, fone, fba]; exact rfl
          else have y5 := e5asq y y0 y1 y2 y3 y4; rw [x0, y5, one_mul, fone, fasq]; exact rfl
        else if x1 : x = a then
          if y0 : y = 1 then rw [x1, y0, mul_one, fa, fone]; exact rfl
          else if y1 : y = a then rw [x1, y1, fasq, fa]
          else if y2 : y = b then rw [x1, y2, fa, fb, fab]
          else if y3 : y = a * b then
            rw [x1, y3, ← mul_assoc, aabeqba, fba, fa, fab]
            ext n
            if n0 : n = 0 then rw [n0]; rfl
            else if n1 : n = 1 then rw [n1]; rfl
            else have n2 : n = 2 := eqtwoofne n n0 n1; rw [n2]; rfl
          else if y4 : y = b * a then
            rw [x1, y4, ← mul_assoc, abaeqb, fb, fa, fba]
            ext n
            if n0 : n = 0 then rw [n0]; rfl
            else if n1 : n = 1 then rw [n1]; rfl
            else have n2 : n = 2 := eqtwoofne n n0 n1; rw [n2]; rfl
          else
            have y5 := e5asq y y0 y1 y2 y3 y4
            rw [x1, y5, ← mul_assoc, acbeqone, fone, fa, fasq]
            ext n
            if n0 : n = 0 then rw [n0]; rfl
            else if n1 : n = 1 then rw [n1]; rfl
            else have n2 : n = 2 := eqtwoofne n n0 n1; rw [n2]; rfl
        else if x2 : x = b then
          if y0 : y = 1 then rw [x2, y0, mul_one, fb, fone]; exact rfl
          else if y1 : y = a then rw [x2, y1, fba, fb, fa]
          else if y2 : y = b then
            rw [x2, y2, bsqeqone, fone, fb];
            ext n
            if n0 : n = 0 then rw [n0]; rfl
            else if n1 : n = 1 then rw [n1]; rfl
            else have n2 : n = 2 := eqtwoofne n n0 n1; rw [n2]; rfl
          else if y3 : y = a * b then
            rw [x2, y3, ← mul_assoc, babeqasq, fasq, fb, fab]
            ext n
            if n0 : n = 0 then rw [n0]; rfl
            else if n1 : n = 1 then rw [n1]; rfl
            else have n2 : n = 2 := eqtwoofne n n0 n1; rw [n2]; rfl
          else if y4 : y = b * a then
            rw [x2, y4, ← mul_assoc, bsqeqone, one_mul, fb, fa, fba]
            ext n
            if n0 : n = 0 then rw [n0]; rfl
            else if n1 : n = 1 then rw [n1]; rfl
            else have n2 : n = 2 := eqtwoofne n n0 n1; rw [n2]; rfl
          else
            have y5 := e5asq y y0 y1 y2 y3 y4
            rw [x2, y5, ← mul_assoc, baaeqab, fab, fb, fasq]
            ext n
            if n0 : n = 0 then rw [n0]; rfl
            else if n1 : n = 1 then rw [n1]; rfl
            else have n2 : n = 2 := eqtwoofne n n0 n1; rw [n2]; rfl
        else if x3 : x = a * b then
          if y0 : y = 1 then rw [x3, y0, mul_one, fab, fone]; exact rfl
          else if y1 : y = a then
            rw [x3, y1, abaeqb, fb, fab, fa]
            ext n
            if n0 : n = 0 then rw [n0]; rfl
            else if n1 : n = 1 then rw [n1]; rfl
            else have n2 : n = 2 := eqtwoofne n n0 n1; rw [n2]; rfl
          else if y2 : y = b then
            rw [x3, y2, mul_assoc, bsqeqone, mul_one, fa, fab, fb]
            ext n
            if n0 : n = 0 then rw [n0]; rfl
            else if n1 : n = 1 then rw [n1]; rfl
            else have n2 : n = 2 := eqtwoofne n n0 n1; rw [n2]; rfl
          else if y3 : y = a * b then
            rw [x3, y3, ← mul_assoc, abaeqb, bsqeqone, fone, fab]
            ext n
            if n0 : n = 0 then rw [n0]; rfl
            else if n1 : n = 1 then rw [n1]; rfl
            else have n2 : n = 2 := eqtwoofne n n0 n1; rw [n2]; rfl
          else if y4 : y = b * a then
            rw [x3, y4, ← mul_assoc, mul_assoc a b b, bsqeqone, mul_one, fasq, fab, fba]
            ext n
            if n0 : n = 0 then rw [n0]; rfl
            else if n1 : n = 1 then rw [n1]; rfl
            else have n2 : n = 2 := eqtwoofne n n0 n1; rw [n2]; rfl
          else
            have y5 := e5asq y y0 y1 y2 y3 y4
            rw [x3, y5, ← mul_assoc, abaeqb, fba, fab, fasq]
            ext n
            if n0 : n = 0 then rw [n0]; rfl
            else if n1 : n = 1 then rw [n1]; rfl
            else have n2 : n = 2 := eqtwoofne n n0 n1; rw [n2]; rfl
        else if x4 : x = b * a then
          if y0 : y = 1 then rw [x4, y0, mul_one, fba, fone]; exact rfl
          else if y1 : y = a then
            rw [x4, y1, baaeqab, fba, fab, fa]
            ext n
            if n0 : n = 0 then rw [n0]; rfl
            else if n1 : n = 1 then rw [n1]; rfl
            else have n2 : n = 2 := eqtwoofne n n0 n1; rw [n2]; rfl
          else if y2 : y = b then
            rw [x4, y2, babeqasq, fasq, fba, fb]
            ext n
            if n0 : n = 0 then rw [n0]; rfl
            else if n1 : n = 1 then rw [n1]; rfl
            else have n2 : n = 2 := eqtwoofne n n0 n1; rw [n2]; rfl
          else if y3 : y = a * b then
            rw [x4, y3, ← mul_assoc, baaeqab, mul_assoc, bsqeqone, mul_one, fa, fba, fab]
            ext n
            if n0 : n = 0 then rw [n0]; rfl
            else if n1 : n = 1 then rw [n1]; rfl
            else have n2 : n = 2 := eqtwoofne n n0 n1; rw [n2]; rfl
          else if y4 : y = b * a then
            rw [x4, y4, ← mul_assoc, babeqasq, acbeqone, fone, fba]
            ext n
            if n0 : n = 0 then rw [n0]; rfl
            else if n1 : n = 1 then rw [n1]; rfl
            else have n2 : n = 2 := eqtwoofne n n0 n1; rw [n2]; rfl
          else
            have y5 := e5asq y y0 y1 y2 y3 y4
            rw [x4, y5, ← mul_assoc, baaeqab, abaeqb, fba, fb, fasq]
            ext n
            if n0 : n = 0 then rw [n0]; rfl
            else if n1 : n = 1 then rw [n1]; rfl
            else have n2 : n = 2 := eqtwoofne n n0 n1; rw [n2]; rfl
        else
          have x5 : x = a * a := e5asq x x0 x1 x2 x3 x4
          if y0 : y = 1 then
            rw [x5, y0, mul_one, fasq, fone]
            ext n
            if n0 : n = 0 then rw [n0]; rfl
            else if n1 : n = 1 then rw [n1]; rfl
            else have n2 : n = 2 := eqtwoofne n n0 n1; rw [n2]; rfl
          else if y1 : y = a then
            rw [x5, y1, acbeqone, fone, fasq, fa]
            ext n
            if n0 : n = 0 then rw [n0]; rfl
            else if n1 : n = 1 then rw [n1]; rfl
            else have n2 : n = 2 := eqtwoofne n n0 n1; rw [n2]; rfl
          else if y2 : y = b then
            rw [x5, y2, aabeqba, fba, fasq, fb]
            ext n
            if n0 : n = 0 then rw [n0]; rfl
            else if n1 : n = 1 then rw [n1]; rfl
            else have n2 : n = 2 := eqtwoofne n n0 n1; rw [n2]; rfl
          else if y3 : y = a * b then
            rw [x5, y3, ← mul_assoc, acbeqone, one_mul, fb, fasq, fab]
            ext n
            if n0 : n = 0 then rw [n0]; rfl
            else if n1 : n = 1 then rw [n1]; rfl
            else have n2 : n = 2 := eqtwoofne n n0 n1; rw [n2]; rfl
          else if y4 : y = b * a then
            rw [x5, y4, ← mul_assoc, aabeqba, baaeqab, fab, fasq, fba]
            ext n
            if n0 : n = 0 then rw [n0]; rfl
            else if n1 : n = 1 then rw [n1]; rfl
            else have n2 : n = 2 := eqtwoofne n n0 n1; rw [n2]; rfl
          else
            have y5 := e5asq y y0 y1 y2 y3 y4
            rw [x5, y5, ← mul_assoc, acbeqone, one_mul, fa, fasq]
            ext n
            if n0 : n = 0 then rw [n0]; rfl
            else if n1 : n = 1 then rw [n1]; rfl
            else have n2 : n = 2 := eqtwoofne n n0 n1; rw [n2]; rfl
  have iso : G ≃* Perm (Fin 3) := MulEquiv.mk equiv_f mul_f
  use iso














-- prove that G ≃ S₃
example (hab : a * b ≠ b * a) : ∃ (f : G ≃* Perm (Fin 3)), f = f := by
  -- the following tedious arguments are to show that 1, a, b, ab, ba are five distinct elements of G
  let G5 (x : G) := x = 1 ∨ x = a ∨ x = b ∨ x = a * b ∨ x = b * a
  have G5n0 (z : G) : ¬ G5 z → z ≠ 1 := by
      intro hz
      dsimp [G5] at hz
      push_neg at hz
      exact hz.1
  have G5n1 (z : G) : ¬ G5 z → z ≠ a := by
      intro hz
      dsimp [G5] at hz
      push_neg at hz
      exact hz.2.1
  have G5n2 (z : G) : ¬ G5 z → z ≠ b := by
      intro hz
      dsimp [G5] at hz
      push_neg at hz
      exact hz.2.2.1
  have G5n3 (z : G) : ¬ G5 z → z ≠ a * b := by
      intro hz
      dsimp [G5] at hz
      push_neg at hz
      exact hz.2.2.2.1
  have G5n4 (z : G) : ¬ G5 z → z ≠ b * a := by
      intro hz
      dsimp [G5] at hz
      push_neg at hz
      exact hz.2.2.2.2
    -- we show that there remains exactly one element of G distinct from the above five, by constructing a injection from Fin 7 to G to lead a contradiction
  have elem5 : ∀ (x y : G), ¬ G5 x ∧ ¬ G5 y → x = y := by
    by_contra h
    push_neg at h
    rcases h with ⟨x, y, ⟨⟨hx, hy⟩, hxy⟩⟩

    let f : Fin 7 → G := by
      intro n
      if n = 0 then exact 1
      else if n = 1 then exact a
      else if n = 2 then exact b
      else if n = 3 then exact a * b
      else if n = 4 then exact b * a
      else if n = 5 then exact x
      else exact y
    have inj_f : Injective f := by
      intro s t hst
      if s0 : s = 0 then
        if t0 : t = 0 then rw [s0, t0]
        else if t1 : t = 1 then rw [s0, t1] at hst; dsimp [f] at hst; symm at hst; absurd hst; exact aneone hab
        else if t2 : t = 2 then rw [s0, t2] at hst; dsimp [f] at hst; symm at hst; absurd hst; exact bneone hab
        else if t3 : t = 3 then rw [s0, t3] at hst; dsimp [f] at hst; symm at hst; absurd hst; exact abneone hab
        else if t4 : t = 4 then rw [s0, t4] at hst; dsimp [f] at hst; symm at hst; absurd hst; exact baneone hab
        else if t5 : t = 5 then rw [s0, t5] at hst; dsimp [f] at hst; symm at hst; have : x ≠ 1 := (G5n0 x hx); absurd hst; exact this
        else
          have t6 : f t = y := by dsimp [f]; split; contradiction; rfl;
          rw [s0, t6] at hst
          dsimp [f] at hst
          symm at hst
          have : y ≠ 1 := (G5n0 y hy)
          contradiction
      else if s1 : s = 1 then
        if t1 : t = 1 then rw [s1, t1]
        else if t0 : t = 0 then rw [s1, t0] at hst; dsimp [f] at hst; absurd hst; exact aneone hab
        else if t2 : t = 2 then rw [s1, t2] at hst; dsimp [f] at hst; absurd hst; exact aneb hab
        else if t3 : t = 3 then rw [s1, t3] at hst; dsimp [f] at hst; absurd hst; exact aneab hab
        else if t4 : t = 4 then rw [s1, t4] at hst; dsimp [f] at hst; absurd hst; exact aneba hab
        else if t5 : t = 5 then rw [s1, t5] at hst; dsimp [f] at hst; symm at hst; have : x ≠ a := (G5n1 x hx); contradiction
        else
          have t6 : f t = y := by dsimp [f]; split; contradiction; rfl;
          rw [s1, t6] at hst
          dsimp [f] at hst
          symm at hst
          have : y ≠ a := (G5n1 y hy)
          contradiction
      else if s2 : s = 2 then
        if t2 : t = 2 then rw [s2, t2]
        else if t0 : t = 0 then rw [s2, t0] at hst; dsimp [f] at hst; absurd hst; exact bneone hab
        else if t1 : t = 1 then rw [s2, t1] at hst; dsimp [f] at hst; absurd hst.symm; exact aneb hab
        else if t3 : t = 3 then rw [s2, t3] at hst; dsimp [f] at hst; absurd hst; exact bneab hab
        else if t4 : t = 4 then rw [s2, t4] at hst; dsimp [f] at hst; absurd hst; exact bneba hab
        else if t5 : t = 5 then rw [s2, t5] at hst; dsimp [f] at hst; symm at hst; have : x ≠ b := (G5n2 x hx); contradiction
        else
          have t6 : f t = y := by dsimp [f]; split; contradiction; rfl;
          rw [s2, t6] at hst
          dsimp [f] at hst
          symm at hst
          have : y ≠ b := (G5n2 y hy)
          contradiction
      else if s3 : s = 3 then
        if t3 : t = 3 then rw [s3, t3]
        else if t0 : t = 0 then rw [s3, t0] at hst; dsimp [f] at hst; absurd hst; exact abneone hab
        else if t1 : t = 1 then rw [s3, t1] at hst; dsimp [f] at hst; absurd hst.symm; exact aneab hab
        else if t2 : t = 2 then rw [s3, t2] at hst; dsimp [f] at hst; absurd hst.symm; exact bneab hab
        else if t4 : t = 4 then rw [s3, t4] at hst; dsimp [f] at hst; contradiction
        else if t5 : t = 5 then rw [s3, t5] at hst; dsimp [f] at hst; symm at hst; have : x ≠ a * b := (G5n3 x hx); contradiction
        else
          have t6 : f t = y := by dsimp [f]; split; contradiction; rfl;
          rw [s3, t6] at hst
          dsimp [f] at hst
          symm at hst
          have : y ≠ a * b := (G5n3 y hy)
          contradiction
      else if s4 : s = 4 then
        if t4 : t = 4 then rw [s4, t4]
        else if t0 : t = 0 then rw [s4, t0] at hst; dsimp [f] at hst; absurd hst; exact baneone hab
        else if t1 : t = 1 then rw [s4, t1] at hst; dsimp [f] at hst; absurd hst.symm; exact aneba hab
        else if t2 : t = 2 then rw [s4, t2] at hst; dsimp [f] at hst; absurd hst.symm; exact bneba hab
        else if t3 : t = 3 then rw [s4, t3] at hst; dsimp [f] at hst; symm at hst; contradiction
        else if t5 : t = 5 then rw [s4, t5] at hst; dsimp [f] at hst; symm at hst; have : x ≠ b * a := (G5n4 x hx); contradiction
        else
          have t6 : f t = y := by dsimp [f]; split; contradiction; rfl;
          rw [s4, t6] at hst
          dsimp [f] at hst
          symm at hst
          have : y ≠ b * a := (G5n4 y hy)
          contradiction
      else if s5 : s = 5 then
        if t5 : t = 5 then rw [s5, t5]
        else if t0 : t = 0 then rw [s5, t0] at hst; dsimp [f] at hst; have : x ≠ 1 := (G5n0 x hx); contradiction
        else if t1 : t = 1 then rw [s5, t1] at hst; dsimp [f] at hst; have : x ≠ a := (G5n1 x hx); contradiction
        else if t2 : t = 2 then rw [s5, t2] at hst; dsimp [f] at hst; have : x ≠ b := (G5n2 x hx); contradiction
        else if t3 : t = 3 then rw [s5, t3] at hst; dsimp [f] at hst; have : x ≠ a * b := (G5n3 x hx); contradiction
        else if t4 : t = 4 then rw [s5, t4] at hst; dsimp [f] at hst; have : x ≠ b * a := (G5n4 x hx); contradiction
        else
          have t6 : f t = y := by dsimp [f]; split; contradiction; rfl;
          rw [s5, t6] at hst
          dsimp [f] at hst
          symm at hst
          have : y ≠ x := hxy.symm
          contradiction
      else
        have s6 : f s = y := by dsimp [f]; split; contradiction; rfl
        if t0 : t = 0 then rw [s6, t0] at hst; dsimp [f] at hst; have : y ≠ 1 := (G5n0 y hy); contradiction
        else if t1 : t = 1 then rw [s6, t1] at hst; dsimp [f] at hst; have : y ≠ a := (G5n1 y hy); contradiction
        else if t2 : t = 2 then rw [s6, t2] at hst; dsimp [f] at hst; have : y ≠ b := (G5n2 y hy); contradiction
        else if t3 : t = 3 then rw [s6, t3] at hst; dsimp [f] at hst; have : y ≠ a * b := (G5n3 y hy); contradiction
        else if t4 : t = 4 then rw [s6, t4] at hst; dsimp [f] at hst; have : y ≠ b * a := (G5n4 y hy); contradiction
        else if t5 : t = 5 then rw [s6, t5] at hst; dsimp [f] at hst; symm at hst; contradiction
        else
          have seq6 : s = 6 := eqsixofne s s0 s1 s2 s3 s4 s5
          have teq6 : t = 6 := eqsixofne t t0 t1 t2 t3 t4 t5
          rw [seq6, teq6]
    have card7: Fintype.card (Fin 7) ≤ Fintype.card G := by exact Fintype.card_le_of_injective f inj_f
    rw [hcard] at card7
    simp at card7
  -- let have a look at a²
  -- check a² ≠ a, b, ab, ba
  -- so a² is either 1 or the last element of G



  -- first assume the latter, a²≠1
  if asqneone : a * a ≠ 1 then exact @intermediate G _ _ hcard a b hab asqneone

  -- the case of b²≠1 is a symmetry of a²≠1, which is discussed as above
  else if bsqneone : b * b ≠ 1 then exact @intermediate G _ _ hcard b a hab.symm bsqneone

  -- so now assume that a²=b²=1
    else
      have asqeqone : a * a = 1 := by exact nmem_mulSupport.mp asqneone
      have bsqeqone : b * b = 1 := by exact nmem_mulSupport.mp bsqneone
      --check aba ≠ 1, a, b, ab, ba
      have abaneone : a * b * a ≠ 1 := by
        by_contra abaeqone
        have eq1 : a * b * a * a = a := by rw [abaeqone, one_mul]
        rw [mul_assoc, asqeqone, mul_one] at eq1
        exact aneab hab eq1.symm
      have abanea : a * b * a ≠ a := by
        by_contra abaeqa
        nth_rw 3 [← one_mul a] at abaeqa
        apply mul_right_cancel at abaeqa
        exact abneone hab abaeqa
      have abaneb : a * b * a ≠ b := by
        by_contra abaeqb
        have eq1 : a * b * a * a = b * a := by rw [abaeqb]
        rw [mul_assoc, asqeqone, mul_one] at eq1
        exact abneba hab eq1
      have abaneab : a * b * a ≠ a * b := by
        by_contra abaeqab
        nth_rw 2 [← mul_one (a * b)] at abaeqab
        apply mul_left_cancel at abaeqab
        exact aneone hab abaeqab
      have abaneba : a * b * a ≠ b * a := by
        by_contra abaeqba
        apply mul_right_cancel at abaeqba
        exact bneab hab abaeqba.symm
      have abanG5 : ¬ G5 (a * b * a) := by
        dsimp [G5]
        push_neg
        exact ⟨abaneone, ⟨abanea, ⟨abaneb, ⟨abaneab, abaneba⟩⟩⟩⟩
      --check bab ≠ 1, a, b, ab, ba
      have babnG5 : ¬ G5 (b * a * b) := by
        dsimp [G5]
        push_neg
        constructor
        by_contra babeqone
        have eq1 : b * a * b * b =b := by rw [babeqone, one_mul]
        rw [mul_assoc, bsqeqone, mul_one] at eq1
        exact bneba hab eq1.symm
        constructor
        by_contra babeqa
        have eq1 : b * a * b * b = a * b := by rw [babeqa]
        rw [mul_assoc, bsqeqone, mul_one] at eq1
        exact abneba hab eq1.symm
        constructor
        by_contra babeqb
        nth_rw 3 [← one_mul b] at babeqb
        apply mul_right_cancel at babeqb
        exact baneone hab babeqb
        constructor
        by_contra babeqab
        apply mul_right_cancel at babeqab
        exact aneba hab babeqab.symm
        by_contra babeqab
        nth_rw 2 [← mul_one (b * a)] at babeqab
        apply mul_left_cancel at babeqab
        exact bneone hab babeqab
      --so aba=bab
      have abaeqbab : a * b * a = b * a * b := elem5 (a * b * a) (b * a * b) ⟨abanG5, babnG5⟩
      have e5aba : ∀ x : G, x ≠ 1 → x ≠ a → x ≠ b → x ≠ a * b → x ≠ b * a → x = a * b * a := by
        intro x x1 x2 x3 x4 x5
        have xnG5 : ¬ G5 x := by
          dsimp [G5]
          push_neg
          exact ⟨x1, ⟨x2, ⟨x3, ⟨x4, x5⟩⟩⟩⟩
        exact elem5 x (a * b * a) ⟨xnG5, abanG5⟩
      --define f : G → G such that ab ↦ c[1, 2, 3] and b ↦ c[1, 2]
      let f : G → Perm (Fin 3) := by
        intro x
        if x = 1 then exact c[1]
        else if x = a then exact c[1, 3]
        else if x = b then exact c[1, 2]
        else if x = a * b then exact c[1, 2, 3]
        else if x = b * a then exact c[1, 3, 2]
        else exact c[2, 3]

      have fone : f 1 = c[1] := by
        dsimp [f]
        split
        rfl
        contradiction
      have fa : f a = c[1, 3] := by
        simp [f, aneone hab]
      have fb : f b = c[1, 2] := by
        simp [f, bneone hab, aneb hab]
        intro beqa
        absurd beqa.symm
        exact aneb hab
      have fab : f (a * b) = c[1, 2, 3] := by
        simp [f, abneone hab, (aneab hab).symm, aneone hab]
      have fba : f (b * a) = c[1, 3, 2] := by
        simp [f, baneone hab, (aneba hab).symm, (bneba hab).symm, (abneba hab).symm]
      have faba : f (a * b * a) = c[2, 3] := by
        simp [f, abaneone, abanea, abaneb, abaneab, abaneba]
      --prove that f is injective
      have inj_f : Injective f := by
        intro x y hxy
        if x0 : x = 1 then
          if y0 : y = 1 then rw [x0, y0]
          else if y1 : y = a then rw [x0, y1, fone, fa] at hxy; have : c[(1 : Fin 3)] ≠ c[1, 3] := ne_of_beq_false rfl; absurd hxy; exact this
          else if y2 : y = b then rw [x0, y2, fone, fb] at hxy; have : c[(1 : Fin 3)] ≠ c[1, 2] := ne_of_beq_false rfl; absurd hxy; exact this
          else if y3 : y = a * b then rw [x0, y3, fone, fab] at hxy; have : c[(1 : Fin 3)] ≠ c[1, 2, 3] := ne_of_beq_false rfl; absurd hxy; exact this
          else if y4 : y = b * a then rw [x0, y4, fone, fba] at hxy; have : c[(1 : Fin 3)] ≠ c[1, 3, 2] := ne_of_beq_false rfl; absurd hxy; exact this
          else
            have y5 := e5aba y y0 y1 y2 y3 y4
            rw [x0, y5, fone, faba] at hxy
            have : c[(1 : Fin 3)] ≠ c[2, 3] := ne_of_beq_false rfl; absurd hxy; exact this
        else if x1 : x = a then
          if y1 : y = a then rw [x1, y1]
          else if y0 : y = 1 then rw [x1, y0, fa, fone] at hxy; have : c[(1 : Fin 3), 3] ≠ 1 := ne_of_beq_false rfl; absurd hxy; exact this
          else if y2 : y = b then rw [x1, y2, fa, fb] at hxy; have : c[(1 : Fin 3), 3] ≠ c[1, 2] := ne_of_beq_false rfl; absurd hxy; exact this
          else if y3 : y = a * b then rw [x1, y3, fa, fab] at hxy; have : c[(1 : Fin 3), 3] ≠ c[1, 2, 3] := ne_of_beq_false rfl; absurd hxy; exact this
          else if y4 : y = b * a then rw [x1, y4, fa, fba] at hxy; have : c[(1 : Fin 3), 3] ≠ c[1, 3, 2] := ne_of_beq_false rfl; absurd hxy; exact this
          else
            have y5 := e5aba y y0 y1 y2 y3 y4
            rw [x1, y5, fa, faba] at hxy
            have : c[(1 : Fin 3), 3] ≠ c[2, 3] := ne_of_beq_false rfl
            absurd hxy; exact this
        else if x2 : x = b then
          if y2 : y = b then rw [x2, y2]
          else if y0 : y = 1 then rw [x2, y0, fb, fone] at hxy; have : c[(1 : Fin 3), 2] ≠ 1 := ne_of_beq_false rfl; absurd hxy; exact this
          else if y1 : y = a then rw [x2, y1, fb, fa] at hxy; have : c[(1 : Fin 3), 2] ≠ c[1, 3] := ne_of_beq_false rfl; absurd hxy; exact this
          else if y3 : y = a * b then rw [x2, y3, fb, fab] at hxy; have : c[(1 : Fin 3), 2] ≠ c[1, 2, 3] := ne_of_beq_false rfl; absurd hxy; exact this
          else if y4 : y = b * a then rw [x2, y4, fb, fba] at hxy; have : c[(1 : Fin 3), 2] ≠ c[1, 3, 2] := ne_of_beq_false rfl;absurd hxy; exact this
          else
            have y5 := e5aba y y0 y1 y2 y3 y4
            rw [x2, y5, fb, faba] at hxy
            have : c[(1 : Fin 3), 2] ≠ c[2, 3] := ne_of_beq_false rfl
            absurd hxy; exact this
        else if x3 : x = a * b then
          if y3 : y = a * b then rw [x3, y3]
          else if y0 : y = 1 then rw [x3, y0, fab, fone] at hxy; have : c[(1 : Fin 3), 2, 3] ≠ 1 := Ne.symm (ne_of_beq_false rfl); absurd hxy; exact this
          else if y1 : y = a then rw [x3, y1, fab, fa] at hxy; have : c[(1 : Fin 3), 2, 3] ≠ c[1, 3] := Ne.symm (ne_of_beq_false rfl); absurd hxy; exact this
          else if y2 : y = b then rw [x3, y2, fab, fb] at hxy; have : c[(1 : Fin 3), 2, 3] ≠ c[1, 2] := Ne.symm (ne_of_beq_false rfl); absurd hxy; exact this
          else if y4 : y = b * a then rw [x3, y4, fab, fba] at hxy; have : c[(1 : Fin 3), 2, 3] ≠ c[1, 3, 2] := Ne.symm (ne_of_beq_false rfl); absurd hxy; exact this
          else
            have y5 := e5aba y y0 y1 y2 y3 y4
            rw [x3, y5, fab, faba] at hxy
            have : c[(1 : Fin 3), 2, 3] ≠ c[2, 3] := Ne.symm (ne_of_beq_false rfl)
            absurd hxy; exact this
        else if x4 : x = b * a then
          if y4 : y = b * a then rw [x4, y4]
          else if y0 : y = 1 then rw [x4, y0, fba, fone] at hxy; have : c[(1 : Fin 3), 3, 2] ≠ 1 := Ne.symm (ne_of_beq_false rfl); absurd hxy; exact this
          else if y1 : y = a then rw [x4, y1, fba, fa] at hxy; have : c[(1 : Fin 3), 3, 2] ≠ c[1, 3] := Ne.symm (ne_of_beq_false rfl); absurd hxy; exact this
          else if y2 : y = b then rw [x4, y2, fba, fb] at hxy; have : c[(1 : Fin 3), 3, 2] ≠ c[1, 2] := Ne.symm (ne_of_beq_false rfl); absurd hxy; exact this
          else if y3 : y = a * b then rw [x4, y3, fba, fab] at hxy; have : c[(1 : Fin 3), 3, 2] ≠ c[1, 2, 3] := ne_of_beq_false rfl; absurd hxy; exact this
          else
            have y5 := e5aba y y0 y1 y2 y3 y4
            rw [x4, y5, fba, faba] at hxy
            have : c[(1 : Fin 3), 3, 2] ≠ c[2, 3] := Ne.symm (ne_of_beq_false rfl)
            absurd hxy; exact this
        else
          have x5 := e5aba x x0 x1 x2 x3 x4
          if y0 : y = 1 then rw [x5, y0, faba, fone] at hxy; have : c[(2 : Fin 3), 3] ≠ 1 := ne_of_beq_false rfl; absurd hxy; exact this
          else if y1 : y = a then rw [x5, y1, faba, fa] at hxy; have : c[(2 : Fin 3), 3] ≠ c[1, 3] := ne_of_beq_false rfl; absurd hxy; exact this
          else if y2 : y = b then rw [x5, y2, faba, fb] at hxy; have : c[(2 : Fin 3), 3] ≠ c[1, 2] := ne_of_beq_false rfl; absurd hxy; exact this
          else if y3 : y = a * b then rw [x5, y3, faba, fab] at hxy; have : c[(2 : Fin 3), 3] ≠ c[1, 2, 3] := ne_of_beq_false rfl; absurd hxy;exact this
          else if y4 : y = b * a then rw [x5, y4, faba, fba] at hxy; have : c[(2 : Fin 3), 3] ≠ c[1, 3, 2] := ne_of_beq_false rfl; absurd hxy; exact this
          else
            have y5 := e5aba y y0 y1 y2 y3 y4
            rw [x5, y5]
      -- f is a set equivalence from that f is injective and card G = card S₃
      have cardeq : Fintype.card G = Fintype.card (Perm (Fin 3)) := by rw [hcard]; rfl
      have bij_f := (@Fintype.bijective_iff_injective_and_card G (Perm (Fin 3)) _ _ f).mpr ⟨inj_f, cardeq⟩
      let equiv_f := ofBijective f bij_f
      -- check that f commutes with multiplication
      have mul_f : ∀ x y : G, f (x * y) = f x * f y := by
        intro x y
        if x0 : x = 1 then
          if y0 : y = 1 then rw [x0, y0, mul_one, fone]; rfl
          else if y1 : y = a then rw [x0, y1, one_mul, fa, fone]; rfl
          else if y2 : y = b then rw [x0, y2, one_mul, fb, fone]; rfl
          else if y3 : y = a * b then rw [x0, y3, one_mul, fab, fone]; rfl
          else if y4 : y = b * a then rw [x0, y4, one_mul, fba, fone]; rfl
          else have y5 := e5aba y y0 y1 y2 y3 y4; rw [x0 ,y5, one_mul, faba, fone]; rfl
        else if x1 : x = a then
          if y0 : y = 1 then rw [x1, y0, mul_one, fa, fone]; rfl
          else if y1 : y = a then
            rw [x1, y1, asqeqone, fone, fa]
            ext n
            if n0 : n = 0 then rw [n0]; rfl
            else if n1 : n = 1 then rw [n1]; rfl
            else have n2 : n = 2 := eqtwoofne n n0 n1; rw [n2]; rfl
          else if y2 : y = b then
            rw [x1, y2, fab, fa, fb]
            ext n
            if n0 : n = 0 then rw [n0]; rfl
            else if n1 : n = 1 then rw [n1]; rfl
            else have n2 : n = 2 := eqtwoofne n n0 n1; rw [n2]; rfl
          else if y3 : y = a * b then
            rw [x1, y3, ← mul_assoc, asqeqone, one_mul, fb, fa, fab]
            ext n
            if n0 : n = 0 then rw [n0]; rfl
            else if n1 : n = 1 then rw [n1]; rfl
            else have n2 : n = 2 := eqtwoofne n n0 n1; rw [n2]; rfl
          else if y4 : y = b * a then
            rw [x1, y4, ← mul_assoc, faba, fa, fba]
            ext n
            if n0 : n = 0 then rw [n0]; rfl
            else if n1 : n = 1 then rw [n1]; rfl
            else have n2 : n = 2 := eqtwoofne n n0 n1; rw [n2]; rfl
          else
            have y5 := e5aba y y0 y1 y2 y3 y4
            rw [x1 ,y5, ← mul_assoc, ← mul_assoc, asqeqone, one_mul, faba, fba, fa]
            ext n
            if n0 : n = 0 then rw [n0]; rfl
            else if n1 : n = 1 then rw [n1]; rfl
            else have n2 : n = 2 := eqtwoofne n n0 n1; rw [n2]; rfl
        else if x2 : x = b then
          if y0 : y = 1 then rw [x2, y0, mul_one, fb, fone]; rfl
          else if y1 : y = a then
            rw [x2, y1, fba, fb, fa]
            ext n
            if n0 : n = 0 then rw [n0]; rfl
            else if n1 : n = 1 then rw [n1]; rfl
            else have n2 : n = 2 := eqtwoofne n n0 n1; rw [n2]; rfl
          else if y2 : y = b then
            rw [x2, y2, bsqeqone, fone, fb]
            ext n
            if n0 : n = 0 then rw [n0]; rfl
            else if n1 : n = 1 then rw [n1]; rfl
            else have n2 : n = 2 := eqtwoofne n n0 n1; rw [n2]; rfl
          else if y3 : y = a * b then
            rw [x2, y3, ← mul_assoc, abaeqbab.symm, faba, fb, fab]
            ext n
            if n0 : n = 0 then rw [n0]; rfl
            else if n1 : n = 1 then rw [n1]; rfl
            else have n2 : n = 2 := eqtwoofne n n0 n1; rw [n2]; rfl
          else if y4 : y = b * a then
            rw [x2, y4, ← mul_assoc, bsqeqone, one_mul, fa, fb, fba]
            ext n
            if n0 : n = 0 then rw [n0]; rfl
            else if n1 : n = 1 then rw [n1]; rfl
            else have n2 : n = 2 := eqtwoofne n n0 n1; rw [n2]; rfl
          else
            have y5 := e5aba y y0 y1 y2 y3 y4
            rw [x2 ,y5, ← mul_assoc, ← mul_assoc, abaeqbab.symm, mul_assoc, asqeqone, mul_one, fab, fb, faba]
            ext n
            if n0 : n = 0 then rw [n0]; rfl
            else if n1 : n = 1 then rw [n1]; rfl
            else have n2 : n = 2 := eqtwoofne n n0 n1; rw [n2]; rfl
        else if x3 : x = a * b then
          if y0 : y = 1 then rw [x3, y0, mul_one, fab, fone]; rfl
          else if y1 : y = a then
            rw [x3, y1, faba, fab, fa]
            ext n
            if n0 : n = 0 then rw [n0]; rfl
            else if n1 : n = 1 then rw [n1]; rfl
            else have n2 : n = 2 := eqtwoofne n n0 n1; rw [n2]; rfl
          else if y2 : y = b then
            rw [x3, y2, mul_assoc, bsqeqone, mul_one, fa, fab, fb]
            ext n
            if n0 : n = 0 then rw [n0]; rfl
            else if n1 : n = 1 then rw [n1]; rfl
            else have n2 : n = 2 := eqtwoofne n n0 n1; rw [n2]; rfl
          else if y3 : y = a * b then
            rw [x3, y3, ← mul_assoc, abaeqbab, mul_assoc, bsqeqone, mul_one, fba, fab]
            ext n
            if n0 : n = 0 then rw [n0]; rfl
            else if n1 : n = 1 then rw [n1]; rfl
            else have n2 : n = 2 := eqtwoofne n n0 n1; rw [n2]; rfl
          else if y4 : y = b * a then
            rw [x3, y4, ← mul_assoc, mul_assoc a, bsqeqone, mul_one, asqeqone, fone, fab, fba]
            ext n
            if n0 : n = 0 then rw [n0]; rfl
            else if n1 : n = 1 then rw [n1]; rfl
            else have n2 : n = 2 := eqtwoofne n n0 n1; rw [n2]; rfl
          else
            have y5 := e5aba y y0 y1 y2 y3 y4
            rw [x3 ,y5, ← mul_assoc, ← mul_assoc, abaeqbab, mul_assoc (b * a), bsqeqone, mul_one, mul_assoc, asqeqone, mul_one, abaeqbab.symm, fb, fab, faba]
            ext n
            if n0 : n = 0 then rw [n0]; rfl
            else if n1 : n = 1 then rw [n1]; rfl
            else have n2 : n = 2 := eqtwoofne n n0 n1; rw [n2]; rfl
        else if x4 : x =  b * a then
          if y0 : y = 1 then rw [x4, y0, mul_one, fba, fone]; rfl
          else if y1 : y = a then
            rw [x4, y1, mul_assoc, asqeqone, mul_one, fb, fba, fa]
            ext n
            if n0 : n = 0 then rw [n0]; rfl
            else if n1 : n = 1 then rw [n1]; rfl
            else have n2 : n = 2 := eqtwoofne n n0 n1; rw [n2]; rfl
          else if y2 : y = b then
            rw [x4, y2, abaeqbab.symm, faba, fba, fb]
            ext n
            if n0 : n = 0 then rw [n0]; rfl
            else if n1 : n = 1 then rw [n1]; rfl
            else have n2 : n = 2 := eqtwoofne n n0 n1; rw [n2]; rfl
          else if y3 : y = a * b then
            rw [x4, y3, ← mul_assoc, mul_assoc b, asqeqone, mul_one, bsqeqone, fone, fba, fab]
            ext n
            if n0 : n = 0 then rw [n0]; rfl
            else if n1 : n = 1 then rw [n1]; rfl
            else have n2 : n = 2 := eqtwoofne n n0 n1; rw [n2]; rfl
          else if y4 : y = b * a then
            rw [x4, y4, ← mul_assoc, abaeqbab.symm, mul_assoc, asqeqone, mul_one, fab, fba]
            ext n
            if n0 : n = 0 then rw [n0]; rfl
            else if n1 : n = 1 then rw [n1]; rfl
            else have n2 : n = 2 := eqtwoofne n n0 n1; rw [n2]; rfl
          else
            have y5 := e5aba y y0 y1 y2 y3 y4
            rw [x4 ,y5, ← mul_assoc, ← mul_assoc, mul_assoc b, asqeqone, mul_one, bsqeqone, one_mul, fa, fba, faba]
            ext n
            if n0 : n = 0 then rw [n0]; rfl
            else if n1 : n = 1 then rw [n1]; rfl
            else have n2 : n = 2 := eqtwoofne n n0 n1; rw [n2]; rfl
        else
          have x5 := e5aba x x0 x1 x2 x3 x4
          if y0 : y = 1 then rw [x5, y0, mul_one, faba, fone]; rfl
          else if y1 : y = a then
            rw [x5, y1, mul_assoc, asqeqone, mul_one, fab, faba, fa]
            ext n
            if n0 : n = 0 then rw [n0]; rfl
            else if n1 : n = 1 then rw [n1]; rfl
            else have n2 : n = 2 := eqtwoofne n n0 n1; rw [n2]; rfl
          else if y2 : y = b then
            rw [x5, y2, abaeqbab, mul_assoc, bsqeqone, mul_one, abaeqbab.symm, faba, fb, fba]
            ext n
            if n0 : n = 0 then rw [n0]; rfl
            else if n1 : n = 1 then rw [n1]; rfl
            else have n2 : n = 2 := eqtwoofne n n0 n1; rw [n2]; rfl
          else if y3 : y = a * b then
            rw [x5, y3, ← mul_assoc, mul_assoc (a * b), asqeqone, mul_one, mul_assoc, bsqeqone, mul_one, fa, faba, fab]
            ext n
            if n0 : n = 0 then rw [n0]; rfl
            else if n1 : n = 1 then rw [n1]; rfl
            else have n2 : n = 2 := eqtwoofne n n0 n1; rw [n2]; rfl
          else if y4 : y = b * a then
            rw [x5, y4, ← mul_assoc, abaeqbab, mul_assoc (b * a), bsqeqone, mul_one, mul_assoc, asqeqone, mul_one, fb, abaeqbab.symm, faba, fba]
            ext n
            if n0 : n = 0 then rw [n0]; rfl
            else if n1 : n = 1 then rw [n1]; rfl
            else have n2 : n = 2 := eqtwoofne n n0 n1; rw [n2]; rfl
          else
            have y5 := e5aba y y0 y1 y2 y3 y4
            rw [x5 ,y5, ← mul_assoc, ← mul_assoc, mul_assoc (a * b), asqeqone, mul_one, mul_assoc a, bsqeqone, mul_one, asqeqone, fone, faba]
            ext n
            if n0 : n = 0 then rw [n0]; rfl
            else if n1 : n = 1 then rw [n1]; rfl
            else have n2 : n = 2 := eqtwoofne n n0 n1; rw [n2]; rfl
      have iso : G ≃* Perm (Fin 3) := MulEquiv.mk equiv_f mul_f
      use iso


/-! Informal proof:
We follow the top answer from
https://math.stackexchange.com/questions/2588501/non-abelian-group-of-order-6
Assume that G is non-abelian and has order 6. Hence we can find two elements a,b∈G with ab≠ba and 1∉{a,b}. So the subset {1,a,b,ab,ba} of G consists of exactly five different elements.
Let us have a look at a^2. Then an easy check gives a^2∉{a,b,ab,ba}. Hence a^2=1
 or a^2 is a \"new\" element ≠1.
Assume that a^2≠1, so G={1,a,b,ab,ba,a^2}. Then a^3∉{a,b,ab,ba,a^2}. So in this case we must have a^3=1. And also b^2∉{a,b,ab,ba,^a2}, so b2=1. Now the map a↦(123) and b↦(12) yields an isomorphism with S_3.
Because of symmetry, we can finally assume that a^2=1=b^2, that is a=a^−1and b=b^−1. It is again easily checked that aba∉{1,a,b,ab,ba}. Then aba is the sixth element and by symmetry, aba=bab, so ba=(ab)^2 and (ab)^3=1. Now the map ab↦(123) b↦(12) gives the desired isomorphism with S_3.
-/
