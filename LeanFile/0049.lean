import Mathlib
/-! Question:
11. Show that the presentation
\[
\left(a, b: a^{3}=1, b^{2}=1, b a=a^{2} b\right)
\]
gives (up to isomorphism) the only nonabelian group of order 6 , and hence gives a group isomorphic to $S_{3}$.
-/
/-11. Show that the presentation

\[

\left(a, b: a^{3}=1, b^{2}=1, b a=a^{2} b\right)

\]

gives (up to isomorphism) the only nonabelian group of order 6 , and hence gives a group isomorphic to $S_{3}$.-/


open Equiv
open Function

/-- define the elements a of the free group F₂ -/
def a := FreeGroup.mk [((0 : Fin 2), true)]
/-- define the element b of the free group F₂ -/
def b := FreeGroup.mk [((1 : Fin 2), true)]
/-- define rels, the relations of the presentation H -/
def rels : Set (FreeGroup (Fin 2)) := {a * a * a, b * b, a * b * a * b⁻¹}


/-- define the elements a' of H -/
def a' : (PresentedGroup rels) := QuotientGroup.mk a
/-- define the elements b' of H -/
def b' : (PresentedGroup rels) := QuotientGroup.mk b

/-- a' * a' * a' = 1 in H -/
lemma eqapow : a' * a' * a' = 1 := by
  show QuotientGroup.mk (a * a * a) = 1
  refine (QuotientGroup.eq_one_iff (a * a * a)).mpr ?_
  -- a * a * a ∈ rels
  have ain : a * a * a ∈ rels := by
    left
    exact rfl
  have relsle : rels ≤ Subgroup.normalClosure rels := by refine Set.le_iff_subset.mpr ?_; exact Subgroup.subset_normalClosure
  exact relsle ain

/-- b' * b' = 1 in H -/
lemma eqbpow : b' * b' = 1 := by
  show QuotientGroup.mk (b * b) = 1
  refine (QuotientGroup.eq_one_iff (b * b)).mpr ?_
  -- b * b ∈ rels
  have bin : b * b ∈ rels := by
    right
    left
    exact rfl
  have relsle : rels ≤ Subgroup.normalClosure rels := by refine Set.le_iff_subset.mpr ?_; exact Subgroup.subset_normalClosure
  exact relsle bin

/-- a'⁻¹ = a' * a' in H -/
lemma eqainv : a'⁻¹ = a' * a' := by
  refine inv_eq_of_mul_eq_one_left ?h
  exact eqapow

/-- b⁻¹ '= b' -/
lemma eqbinv : b'⁻¹ = b' := by
  refine DivisionMonoid.inv_eq_of_mul b' b' ?_
  exact eqbpow

/-- a' * b' = b' * a' * a' -/
lemma eqab : a' * b' = b' * a' * a' := by
  have mid : a' * b' * a' * b'⁻¹ = 1 := by
    show QuotientGroup.mk (a * b * a * b⁻¹) = 1
    refine (QuotientGroup.eq_one_iff (a * b * a * b⁻¹)).mpr ?_
    -- a * b * a * b⁻¹ ∈ rels, so a' * b' * a' * b'⁻¹ = 1 in H
    have cin : a * b * a * b⁻¹ ∈ rels := by
      right
      right
      exact rfl
    have relsle : rels ≤ Subgroup.normalClosure rels := by refine Set.le_iff_subset.mpr ?_; exact Subgroup.subset_normalClosure
    exact relsle cin
  -- by some algebraic manipulation, we can show that a' * b' = b' * a' * a'
  rw [← mul_one (a' * b'), ← eqapow, ← mul_assoc, ← mul_assoc, ← mul_one (a' * b' * a'), ← eqbpow, ← mul_assoc]
  nth_rw 2 [← eqbinv]
  rw [mid, one_mul]

/-- a' * a' * b' = b' * a' -/
lemma eqaab : a' * a' * b' = b' * a' := by
  rw [mul_assoc a', eqab, ← mul_assoc, ← mul_assoc, eqab, mul_assoc b', mul_assoc b', eqapow, mul_one]


/-- H has only six elements 1, a', b', a' * a', b' * a', b' * a' * a' -/
lemma elemspre : ∀ x : PresentedGroup rels, x ∈ ({1, a', b', a' * a', b' * a', b' * a' * a'} : Set (PresentedGroup rels)) := by
  intro _
  -- we prove that x ∈ {1, a', b', a' * a', b' * a', b' * a' * a'} by proving that for all z in F₂, z / ⟨rels⟩ ∈ {1, a', b', a' * a', b' * a', b' * a' * a'}
  apply QuotientGroup.induction_on
  intro _
  -- we prove that z / ⟨rels⟩ ∈ {1, a', b', a' * a', b' * a', b' * a' * a'} by free group induction
  apply @FreeGroup.induction_on (Fin 2) (fun y ↦ (QuotientGroup.mk y : PresentedGroup rels) ∈ ({1, a', b', a' * a', b' * a', b' * a' * a'} : Set (PresentedGroup rels))) _
  · -- base case: z = 1 ∈ {1, a', b', a' * a', b' * a', b' * a' * a'}
    exact Set.mem_insert 1 {a', b', a' * a', b' * a', b' * a' * a'}
  · -- base case: z = a ∈ {1, a', b', a' * a', b' * a', b' * a' * a'} or z = b ∈ {1, a', b', a' * a', b' * a', b' * a' * a'}
    intro i
    fin_cases i
    -- z = a
    right
    left
    exact rfl
    -- z = b
    right
    right
    left
    exact rfl
  · -- base case: z = a⁻¹ ∈ {1, a', b', a' * a', b' * a', b' * a' * a'} or z = b⁻¹ ∈ {1, a', b', a' * a', b' * a', b' * a' * a'}
    intro i hi
    fin_cases i
    -- z = a⁻¹
    right
    right
    right
    left
    exact eqainv
    -- z = b⁻¹
    right
    right
    left
    exact eqbinv
  · -- induction step: if x and y are in {1, a', b', a' * a', b' * a', b' * a' * a'}, then x * y is in {1, a', b', a' * a', b' * a', b' * a' * a'}
    intro x y xeq yeq
    have xyeq : @QuotientGroup.mk (FreeGroup (Fin 2)) FreeGroup.instGroup (Subgroup.normalClosure rels) (x * y) = (@QuotientGroup.mk (FreeGroup (Fin 2)) FreeGroup.instGroup (Subgroup.normalClosure rels) x) * (@QuotientGroup.mk (FreeGroup (Fin 2)) FreeGroup.instGroup (Subgroup.normalClosure rels) y) := by exact rfl
    rcases xeq with xeq | xeq | xeq | xeq | xeq | xeq
    · -- x = 1
      rw [xyeq, xeq, one_mul]
      exact yeq
    · -- x = a'
      rcases yeq with yeq | yeq | yeq | yeq | yeq | yeq
      · -- y = 1
        rw [xyeq, xeq, yeq, mul_one]
        right
        left
        exact rfl
      · -- y = a'
        rw [xyeq, xeq, yeq]
        right
        right
        right
        left
        exact rfl
      · -- y = b'
        rw [xyeq, xeq, yeq, eqab]
        right
        right
        right
        right
        right
        exact rfl
      · -- y = a' * a'
        rw [xyeq, xeq, yeq, ← mul_assoc, eqapow]
        exact Set.mem_insert 1 {a', b', a' * a', b' * a', b' * a' * a'}
      · -- y = b' * a'
        rw [xyeq, xeq, yeq, ← mul_assoc, eqab, mul_assoc, mul_assoc, eqapow, mul_one]
        right
        right
        left
        exact rfl
      · -- y = b' * a' * a'
        rw [xyeq, xeq, yeq, ← mul_assoc, ← mul_assoc, eqab, mul_assoc (b' * a'), mul_assoc (b' * a'), eqapow, mul_one]
        right
        right
        right
        right
        left
        exact rfl
    · -- x = b'
      rcases yeq with yeq | yeq | yeq | yeq | yeq | yeq
      · -- y = 1
        rw [xyeq, xeq, yeq, mul_one]
        right
        right
        left
        exact rfl
      · -- y = a'
        rw [xyeq, xeq, yeq]
        right
        right
        right
        right
        left
        exact rfl
      · -- y = b'
        rw [xyeq, xeq, yeq, eqbpow]
        exact Set.mem_insert 1 {a', b', a' * a', b' * a', b' * a' * a'}
      · -- y = a' * a'
        rw [xyeq, xeq, yeq, ← mul_assoc]
        right
        right
        right
        right
        right
        exact rfl
      · -- y = b' * a'
        rw [xyeq, xeq, yeq, ← mul_assoc, eqbpow, one_mul]
        right
        exact Set.mem_insert a' {b', a' * a', b' * a', b' * a' * a'}
      · -- y = b' * a' * a'
        rw [xyeq, xeq, yeq, ← mul_assoc, ← mul_assoc, eqbpow, one_mul]
        right
        right
        right
        exact Set.mem_insert (a' * a') {b' * a', b' * a' * a'}
    · -- x = a' * a'
      rcases yeq with yeq | yeq | yeq | yeq | yeq | yeq
      · -- y = 1
        rw [xyeq, xeq, yeq, mul_one]
        right
        right
        right
        exact Set.mem_insert (a' * a') {b' * a', b' * a' * a'}
      · -- y = a'
        rw [xyeq, xeq, yeq, eqapow]
        exact Set.mem_insert 1 {a', b', a' * a', b' * a', b' * a' * a'}
      · -- y = b'
        rw [xyeq, xeq, yeq, eqaab]
        right
        right
        right
        right
        exact Set.mem_insert (b' * a') {b' * (a' * a')}
      · -- y = a' * a'
        rw [xyeq, xeq, yeq, ← mul_assoc, eqapow, one_mul]
        right
        exact Set.mem_insert a' {b', a' * a', b' * a', b' * a' * a'}
      · -- y = b' * a'
        rw [xyeq, xeq, yeq, ← mul_assoc, eqaab]
        right
        right
        right
        right
        right
        exact rfl
      · -- y = b' * a' * a'
        rw [xyeq, xeq, yeq, ← mul_assoc, ← mul_assoc, eqaab, mul_assoc, mul_assoc, eqapow, mul_one]
        right
        right
        exact Set.mem_insert b' {a' * a', b' * a', b' * (a' * a')}
    · -- x = b' * a'
      rcases yeq with yeq | yeq | yeq | yeq | yeq | yeq
      · -- y = 1
        rw [xyeq, xeq, yeq, mul_one]
        right
        right
        right
        right
        exact Set.mem_insert (b' * a') {b' * a' * a'}
      · -- y = a'
        rw [xyeq, xeq, yeq]
        right
        right
        right
        right
        right
        exact rfl
      · -- y = b'
        rw [xyeq, xeq, yeq, mul_assoc b' a' b', eqab, ← mul_assoc, ← mul_assoc, eqbpow, one_mul]
        right
        right
        right
        exact Set.mem_insert (a' * a') {b' * a', b' * a' * a'}
      · -- y = a' * a'
        rw [xyeq, xeq, yeq, mul_assoc b' a' (a' * a'), ← mul_assoc a', eqapow, mul_one]
        right
        right
        exact Set.mem_insert b' {a' * a', b' * a', b' * a' * a'}
      · -- y = b' * a'
        rw [xyeq, xeq, yeq, ← mul_assoc, mul_assoc b' a' b', eqab, ← mul_assoc, ← mul_assoc, eqbpow, one_mul, eqapow]
        exact Set.mem_insert 1 {a', b', a' * a', b' * a', b' * a' * a'}
      · -- y = b' * a' * a'
        rw [xyeq, xeq, yeq, ← mul_assoc, ← mul_assoc, mul_assoc b' a' b', eqab, ← mul_assoc, ← mul_assoc, eqbpow, one_mul, eqapow, one_mul]
        right
        exact Set.mem_insert a' {b', a' * a', b' * a', b' * a' * a'}
    · -- x = b' * a' * a'
      rcases yeq with yeq | yeq | yeq | yeq | yeq | yeq
      · -- y = 1
        rw [xyeq, xeq, yeq, mul_one]
        right
        right
        right
        right
        right
        exact rfl
      · -- y = a'
        rw [xyeq, xeq, yeq, mul_assoc, mul_assoc, eqapow, mul_one]
        right
        right
        exact Set.mem_insert b' {a' * a', b' * a', b' * (a' * a')}
      · -- y = b'
        rw [xyeq, xeq, yeq, mul_assoc, mul_assoc, eqaab, ← mul_assoc b' b', eqbpow, one_mul]
        right
        exact Set.mem_insert a' {b', a' * a', b' * a', b' * (a' * a')}
      · -- y = a' * a'
        rw [xyeq, xeq, yeq, ← mul_assoc, mul_assoc, mul_assoc b', eqapow, mul_one]
        right
        right
        right
        right
        exact Set.mem_insert (b' * a') {b' * (a' * a')}
      · -- y = b' * a'
        rw [xyeq, xeq, yeq, ← mul_assoc, mul_assoc, mul_assoc b', eqaab, ← mul_assoc b' b', eqbpow, one_mul]
        right
        right
        right
        exact Set.mem_insert (a' * a') {b' * a', b' * (a' * a')}
      · -- y = b' * a' * a'
        rw [xyeq, xeq, yeq, ← mul_assoc, ← mul_assoc, mul_assoc b', mul_assoc b', eqaab, ← mul_assoc, ← mul_assoc, eqbpow, one_mul, eqapow]
        exact Set.mem_insert 1 {a', b', a' * a', b' * a', b' * a' * a'}


/-- Perm (Fin 3) has only six elements 1, c[1, 2, 3], c[1, 2], c[1, 3, 2], c[2, 3], c[1, 3] -/
lemma elemsperm : ∀ x : Perm (Fin 3), x ∈ ({1, c[1, 2, 3], c[1, 2], c[1, 3, 2], c[2, 3], c[1, 3]} : Set (Perm (Fin 3))) := by
  -- the cardinality of Perm (Fin 3) is 6
  have : Fintype.card (Perm (Fin 3)) = 6 := by
    exact rfl
  -- define f : Fin 6 → Perm (Fin 3) by f 0 = 1, f 1 = c[1, 2, 3], f 2 = c[1, 2], f 3 = c[1, 3, 2], f 4 = c[2, 3], f 5 = c[1, 3]
  let f : Fin 6 → Perm (Fin 3) := ![1, c[1, 2, 3], c[1, 2], c[1, 3, 2], c[2, 3], c[1, 3]]
  -- f is injective
  have inj_f : Injective f := by
    intro x y hxy
    -- we prove that f x = f y → x = y for:
    fin_cases x
    · -- x = 0
      fin_cases y
      -- y = 0
      exact rfl
      -- y = 1
      have : (1 : Perm (Fin 3)) ≠ c[1, 2, 3] := by
        exact ne_of_beq_false rfl
      contradiction
      -- y = 2
      have : (1 : Perm (Fin 3)) ≠ c[1, 2] := by
        exact ne_of_beq_false rfl
      contradiction
      -- y = 3
      have : (1 : Perm (Fin 3)) ≠ c[1, 3, 2] := by
        exact ne_of_beq_false rfl
      contradiction
      -- y = 4
      have : (1 : Perm (Fin 3)) ≠ c[2, 3] := by
        exact ne_of_beq_false rfl
      contradiction
      -- y = 5
      have : (1 : Perm (Fin 3)) ≠ c[1, 3] := by
        exact ne_of_beq_false rfl
      contradiction
    · -- x = 1
      fin_cases y
      -- y = 0
      have : (c[1, 2, 3] : Perm (Fin 3)) ≠ 1 := by
        exact ne_of_beq_false rfl
      contradiction
      -- y = 1
      exact rfl
      -- y = 2
      have : (c[1, 2, 3] : Perm (Fin 3)) ≠ c[1, 2] := by
        exact ne_of_beq_false rfl
      contradiction
      -- y = 3
      have : (c[1, 2, 3] : Perm (Fin 3)) ≠ c[1, 3, 2] := by
        exact ne_of_beq_false rfl
      contradiction
      -- y = 4
      have : (c[1, 2, 3] : Perm (Fin 3)) ≠ c[2, 3] := by
        exact ne_of_beq_false rfl
      contradiction
      -- y = 5
      have : (c[1, 2, 3] : Perm (Fin 3)) ≠ c[1, 3] := by
        exact ne_of_beq_false rfl
      contradiction
    · -- x = 2
      fin_cases y
      -- y = 0
      have : (c[1, 2] : Perm (Fin 3)) ≠ 1 := by
        exact ne_of_beq_false rfl
      contradiction
      -- y = 1
      have : (c[1, 2] : Perm (Fin 3)) ≠ c[1, 2, 3] := by
        exact ne_of_beq_false rfl
      contradiction
      -- y = 2
      exact rfl
      -- y = 3
      have : (c[1, 2] : Perm (Fin 3)) ≠ c[1, 3, 2] := by
        exact ne_of_beq_false rfl
      contradiction
      -- y = 4
      have : (c[1, 2] : Perm (Fin 3)) ≠ c[2, 3] := by
        exact ne_of_beq_false rfl
      contradiction
      -- y = 5
      have : (c[1, 2] : Perm (Fin 3)) ≠ c[1, 3] := by
        exact ne_of_beq_false rfl
      contradiction
    · -- x = 3
      fin_cases y
      -- y = 0
      have : (c[1, 3, 2] : Perm (Fin 3)) ≠ 1 := by
        exact ne_of_beq_false rfl
      contradiction
      -- y = 1
      have : (c[1, 3, 2] : Perm (Fin 3)) ≠ c[1, 2, 3] := by
        exact ne_of_beq_false rfl
      contradiction
      -- y = 2
      have : (c[1, 3, 2] : Perm (Fin 3)) ≠ c[1, 2] := by
        exact ne_of_beq_false rfl
      contradiction
      -- y = 3
      exact rfl
      -- y = 4
      have : (c[1, 3, 2] : Perm (Fin 3)) ≠ c[2, 3] := by
        exact ne_of_beq_false rfl
      contradiction
      -- y = 5
      have : (c[1, 3, 2] : Perm (Fin 3)) ≠ c[1, 3] := by
        exact ne_of_beq_false rfl
      contradiction
    · -- x = 4
      fin_cases y
      -- y = 0
      have : (c[2, 3] : Perm (Fin 3)) ≠ 1 := by
        exact ne_of_beq_false rfl
      contradiction
      -- y = 1
      have : (c[2, 3] : Perm (Fin 3)) ≠ c[1, 2, 3] := by
        exact ne_of_beq_false rfl
      contradiction
      -- y = 2
      have : (c[2, 3] : Perm (Fin 3)) ≠ c[1, 2] := by
        exact ne_of_beq_false rfl
      contradiction
      -- y = 3
      have : (c[2, 3] : Perm (Fin 3)) ≠ c[1, 3, 2] := by
        exact ne_of_beq_false rfl
      contradiction
      -- y = 4
      exact rfl
      -- y = 5
      have : (c[2, 3] : Perm (Fin 3)) ≠ c[1, 3] := by
        exact ne_of_beq_false rfl
      contradiction
    · -- x = 5
      fin_cases y
      -- y = 0
      have : (c[1, 3] : Perm (Fin 3)) ≠ 1 := by
        exact ne_of_beq_false rfl
      contradiction
      -- y = 1
      have : (c[1, 3] : Perm (Fin 3)) ≠ c[1, 2, 3] := by
        exact ne_of_beq_false rfl
      contradiction
      -- y = 2
      have : (c[1, 3] : Perm (Fin 3)) ≠ c[1, 2] := by
        exact ne_of_beq_false rfl
      contradiction
      -- y = 3
      have : (c[1, 3] : Perm (Fin 3)) ≠ c[1, 3, 2] := by
        exact ne_of_beq_false rfl
      contradiction
      -- y = 4
      have : (c[1, 3] : Perm (Fin 3)) ≠ c[2, 3] := by
        exact ne_of_beq_false rfl
      contradiction
      -- y = 5
      exact rfl
  -- there is a bijection equiv between Fin 6 and Perm (Fin 3)
  have equiv : Fin 6 ≃ Perm (Fin 3) := by exact (Fintype.equivFinOfCardEq this).symm
  -- f is surjective
  have surj_f : Surjective f := by exact Injective.surjective_of_fintype equiv inj_f
  -- for all x in Perm (Fin 3), x ∈ {1, c[1, 2, 3], c[1, 2], c[1, 3, 2], c[2, 3], c[1, 3]}
  intro x
  -- there exists i in Fin 6 such that f i = x
  rcases surj_f x with ⟨i, hi⟩
  fin_cases i
  -- if i = 0, then x = 1
  have : x = 1 := by exact id (Eq.symm hi)
  left
  exact this
  -- if i = 1, then x = c[1, 2, 3]
  have : x = c[1, 2, 3] := by exact id (Eq.symm hi)
  right
  left
  exact this
  -- if i = 2, then x = c[1, 2]
  have : x = c[1, 2] := by exact id (Eq.symm hi)
  right
  right
  left
  exact this
  -- if i = 3, then x = c[1, 3, 2]
  have : x = c[1, 3, 2] := by exact id (Eq.symm hi)
  right
  right
  right
  left
  exact this
  -- if i = 4, then x = c[2, 3]
  have : x = c[2, 3] := by exact id (Eq.symm hi)
  right
  right
  right
  right
  left
  exact this
  -- if i = 5, then x = c[1, 3]
  have : x = c[1, 3] := by exact id (Eq.symm hi)
  right
  right
  right
  right
  right
  exact this


/-- Show that H = ⟨a, b | a ^ 3 = 1, b ^ 2 = 1, b * a = a⁻¹ * b⟩ is a presentation of S₃-/
noncomputable def presentation : PresentedGroup rels ≃* Perm (Fin 3) := by
  -- define group morphism tof : PresentedGroup rels →* Perm (Fin 3) as the lift of FreeGroup (Fin 2) →* Perm (Fin 3), where we need to verify that rels is in the kernel of the latter map
  let tof : PresentedGroup rels →* Perm (Fin 3) := by
    -- let lifttof : FreeGroup (Fin 2) →* Perm (Fin 3) be induced by gnrttof : Fin 2 → Perm (Fin 3) that sends 0 to c[1, 2, 3] and 1 to c[1, 2]
    let lifttof : FreeGroup (Fin 2) →* Perm (Fin 3) := by
      -- define gnrttof : Fin 2 → Perm (Fin 3) by gnrttof 0 = c[1, 2, 3] and gnrttof 1 = c[1, 2]
      let gnrttof : (Fin 2) → Perm (Fin 3) := ![c[(1 : Fin 3), 2, 3], c[1, 2]]
      exact FreeGroup.lift gnrttof
    -- prove that the normal closure of rels is in the kernel of lifttof
    have Nleker : Subgroup.normalClosure rels ≤ lifttof.ker := by
      -- suffices to prove that rels is in the kernel of lifttof
      apply Subgroup.normalClosure_subset_iff.mp
      intro g gin
      -- suffices to prove that lifttof g = 1 for all g in rels
      apply MonoidHom.mem_ker.mpr
      rcases gin with geq | geq | geq
      · -- if g = a * a * a, then lifttof g = 1
        simp only [Fin.isValue, Cycle.formPerm_coe, List.formPerm_cons_cons, List.formPerm_singleton, mul_one, geq, map_mul, lifttof]
        -- suffices to show c[1, 2, 3] * c[1, 2, 3] * c[1, 2, 3] = 1
        show c[(1 : Fin 3), 2, 3] * c[(1 : Fin 3), 2, 3] * c[(1 : Fin 3), 2, 3] = 1
        rw [mul_assoc, ← pow_three]
        have threecycle : Perm.IsThreeCycle c[(1 : Fin 3), 2, 3] := by exact rfl
        apply Perm.IsThreeCycle.orderOf at threecycle
        rw [← pow_orderOf_eq_one c[(1 : Fin 3), 2, 3]]
        rw [threecycle]
      · -- if g = b * b, then lifttof g = 1
        simp only [Fin.isValue, Cycle.formPerm_coe, List.formPerm_cons_cons, List.formPerm_singleton, mul_one, geq, map_mul, lifttof]
        -- suffices to show c[1, 2] * c[1, 2] = 1
        show c[(1 : Fin 3), 2] * c[(1 : Fin 3), 2] = 1
        refine Perm.support_eq_empty_iff.mp ?_
        exact rfl
      · -- if g = a * b * a * b⁻¹, then lifttof g = 1
        rw [Set.mem_singleton_iff] at geq
        simp only [Fin.isValue, Cycle.formPerm_coe, List.formPerm_cons_cons, List.formPerm_singleton, mul_one, geq, map_mul, lifttof]
        -- suffices to show c[1, 2, 3] * c[1, 2] * c[1, 2, 3] * c[1, 2]⁻¹ = 1
        show c[(1 : Fin 3), 2, 3] * c[(1 : Fin 3), 2] * c[(1 : Fin 3), 2, 3] * c[(1 : Fin 3), 2]⁻¹ = 1
        ext i
        fin_cases i
        simp only [Fin.isValue, Cycle.formPerm_coe, List.formPerm_cons_cons, List.formPerm_singleton, mul_one, swap_inv, Fin.zero_eta, Perm.coe_mul, comp_apply, swap_apply_self, Fin.val_zero, Perm.coe_one, id_eq]
        simp only [Fin.isValue, Cycle.formPerm_coe, List.formPerm_cons_cons, List.formPerm_singleton, mul_one, swap_inv, Fin.zero_eta, Perm.coe_mul, comp_apply, swap_apply_self, Fin.val_zero, Perm.coe_one, id_eq]
        simp only [Fin.isValue, Cycle.formPerm_coe, List.formPerm_cons_cons, List.formPerm_singleton, mul_one, swap_inv, Fin.zero_eta, Perm.coe_mul, comp_apply, swap_apply_self, Fin.val_zero, Perm.coe_one, id_eq]
    -- since rels is in the normal closure of rels, gnrttof induces the group morphism lifttof : H →* Perm (Fin 3)
    exact QuotientGroup.lift (Subgroup.normalClosure rels) lifttof Nleker
  -- prove that tof is bijective, so that PresentedGroup rels ≃* Perm (Fin 3). define g as the inverse of tof
  have bij_tof : Bijective tof := by
    -- suffices to prove that tof has an inverse
    refine bijective_iff_has_inverse.mpr ?_
    -- define g : Perm (Fin 3) → PresentedGroup rels by g c[1, 2, 3] = a', g c[1, 2] = b', g c[1, 3, 2] = a' * a', g c[2, 3] = b' * a', g c[1, 3] = b' * a' * a'
    let g : Perm (Fin 3) → PresentedGroup rels := by
      intro x
      if x1 : x = 1 then
        exact 1
      else if x2 : x = c[1, 2, 3] then
        exact a'
      else if x3 : x = c[1, 2] then
        exact b'
      else if x4 : x = c[1, 3, 2] then
        exact a' * a'
      else if x5 : x = c[2, 3] then
        exact b' * a'
      else if x6 : x = c[1, 3] then
        exact b' * a' * a'
      else
        absurd x6
        rcases elemsperm x with hx | hx | hx | hx | hx | hx
        contradiction
        contradiction
        contradiction
        contradiction
        contradiction
        exact hx
    -- prove that g is an inverse of tof
    use g
    -- tof a' = c[1, 2, 3]
    have fa : tof a' = c[1, 2, 3] := by exact rfl
    -- tof b' = c[1, 2]
    have fb : tof b' = c[1, 2] := by exact rfl
    -- tof (a' * a') = c[1, 3, 2]
    have faa : tof (a' * a') = c[1, 3, 2] := by
      rw [map_mul, fa]
      ext i
      fin_cases i
      exact rfl
      exact rfl
      exact rfl
    -- tof (b' * a') = c[2, 3]
    have fba : tof (b' * a') = c[2, 3] := by
      rw [map_mul, fa, fb]
      ext i
      fin_cases i
      exact rfl
      exact rfl
      exact rfl
    -- tof (b' * a' * a') = c[1, 3]
    have fbaa : tof (b' * a' * a') = c[1, 3] := by
      rw [map_mul, fba, fa]
      ext i
      fin_cases i
      exact rfl
      exact rfl
      exact rfl
    constructor
    · -- g is a left inverse of tof
      intro x
      -- g (tof x) = x for all x in H = {1, a', b', a' * a', b' * a', b' * a' * a'}
      rcases elemspre x with hx | hx | hx | hx | hx | hx
      -- x = 1
      simp only [Fin.isValue, Cycle.formPerm_coe, List.formPerm_cons_cons, List.formPerm_singleton, mul_one, hx, map_one, ↓reduceDIte, g, tof]
      -- x = a'
      rw [hx, fa]
      exact rfl
      -- x = b'
      rw [hx, fb]
      exact rfl
      -- x = a' * a'
      rw [hx, faa]
      exact rfl
      -- x = b' * a'
      rw [hx, fba]
      exact rfl
      -- x = b' * a' * a'
      rw [hx, fbaa]
      exact rfl
    · -- g is a right inverse of tof
      intro x
      rcases elemsperm x with hx | hx | hx | hx | hx | hx
      -- x = 1
      rw [hx]
      exact rfl
      -- x = c[1, 2, 3]
      rw [hx]
      exact rfl
      -- x = c[1, 2]
      rw [hx]
      exact rfl
      -- x = c[1, 3, 2]
      have gaa : g c[1, 3, 2] = a' * a' := by exact rfl
      rw [hx, gaa, faa]
      -- x = c[2, 3]
      have gba : g c[2, 3] = b' * a' := by exact rfl
      rw [hx, gba, fba]
      -- x = c[1, 3]
      have gbaa : g c[1, 3] = b' * a' * a' := by exact rfl
      rw [hx, gbaa, fbaa]
  -- construct an equivalence equiv : PresentedGroup rels ≃ Perm (Fin 3) using tof
  let equiv : PresentedGroup rels ≃ Perm (Fin 3) := by
    exact ofBijective (⇑tof) bij_tof
  -- prove that equiv is a group isomorphism
  refine MulEquiv.mk' equiv ?_
  intro x y
  -- tof (x * y) = tof x * tof y for all x, y in H
  show tof (x * y) = tof x * tof y
  exact MonoidHom.map_mul tof x y



/-! Informal proof:
ESS","data":{"total":3,"list":[{"created":"2025-05-21 22:16:33","updated":"2025-05-22 15:48:01","id":9034,"questionId":3277,"taskId":2510,"jobId":7007,"userId":420,"judgeUserId":351,"answer":{"informalProof":null,"formalProof":"import Mathlib
/-11. Show that the presentation
\[
\left(a, b: a^{3}=1, b^{2}=1, b a=a^{2} b\right)
\]
gives (up to isomorphism) the only nonabelian group of order 6 , and hence gives a group isomorphic to $S_{3}$.-/

open Equiv
open Function
/-- define the elements a of the free group F₂ -/
def a := FreeGroup.mk [((0 : Fin 2), true)]
/-- define the element b of the free group F₂ -/
def b := FreeGroup.mk [((1 : Fin 2), true)]
/-- define rels, the relations of the presentation H -/
def rels : Set (FreeGroup (Fin 2)) := {a * a * a, b * b, a * b * a * b⁻¹}

/-- define the elements a' of H -/
def a' : (PresentedGroup rels) := QuotientGroup.mk a
/-- define the elements b' of H -/
def b' : (PresentedGroup rels) := QuotientGroup.mk b
/-- a' * a' * a' = 1 in H -/
lemma eqapow : a' * a' * a' = 1 := by
  show QuotientGroup.mk (a * a * a) = 1
  refine (QuotientGroup.eq_one_iff (a * a * a)).mpr ?_
  -- a * a * a ∈ rels
  have ain : a * a * a ∈ rels := by
    left
    exact rfl
  have relsle : rels ≤ Subgroup.normalClosure rels := by refine Set.le_iff_subset.mpr ?_; exact Subgroup.subset_normalClosure
  exact relsle ain
/-- b' * b' = 1 in H -/
lemma eqbpow : b' * b' = 1 := by
  show QuotientGroup.mk (b * b) = 1
  refine (QuotientGroup.eq_one_iff (b * b)).mpr ?_
  -- b * b ∈ rels
  have bin : b * b ∈ rels := by
    right
    left
    exact rfl
  have relsle : rels ≤ Subgroup.normalClosure rels := by refine Set.le_iff_subset.mpr ?_; exact Subgroup.subset_normalClosure
  exact relsle bin
/-- a'⁻¹ = a' * a' in H -/
lemma eqainv : a'⁻¹ = a' * a' := by
  refine inv_eq_of_mul_eq_one_left ?h
  exact eqapow
/-- b⁻¹ '= b' -/
lemma eqbinv : b'⁻¹ = b' := by
  refine DivisionMonoid.inv_eq_of_mul b' b' ?_
  exact eqbpow
/-- a' * b' = b' * a' * a' -/
lemma eqab : a' * b' = b' * a' * a' := by
  have mid : a' * b' * a' * b'⁻¹ = 1 := by
    show QuotientGroup.mk (a * b * a * b⁻¹) = 1
    refine (QuotientGroup.eq_one_iff (a * b * a * b⁻¹)).mpr ?_
    -- a * b * a * b⁻¹ ∈ rels, so a' * b' * a' * b'⁻¹ = 1 in H
    have cin : a * b * a * b⁻¹ ∈ rels := by
      right
      right
      exact rfl
    have relsle : rels ≤ Subgroup.normalClosure rels := by refine Set.le_iff_subset.mpr ?_; exact Subgroup.subset_normalClosure
    exact relsle cin
  -- by some algebraic manipulation, we can show that a' * b' = b' * a' * a'
  rw [← mul_one (a' * b'), ← eqapow, ← mul_assoc, ← mul_assoc, ← mul_one (a' * b' * a'), ← eqbpow, ← mul_assoc]
  nth_rw 2 [← eqbinv]
  rw [mid, one_mul]
/-- a' * a' * b' = b' * a' -/
lemma eqaab : a' * a' * b' = b' * a' := by
  rw [mul_assoc a', eqab, ← mul_assoc, ← mul_assoc, eqab, mul_assoc b', mul_assoc b', eqapow, mul_one]

/-- H has only six elements 1, a', b', a' * a', b' * a', b' * a' * a' -/
lemma elemspre : ∀ x : PresentedGroup rels, x ∈ ({1, a', b', a' * a', b' * a', b' * a' * a'} : Set (PresentedGroup rels)) := by
  intro _
  -- we prove that x ∈ {1, a', b', a' * a', b' * a', b' * a' * a'} by proving that for all z in F₂, z / ⟨rels⟩ ∈ {1, a', b', a' * a', b' * a', b' * a' * a'}
  apply QuotientGroup.induction_on
  intro _
  -- we prove that z / ⟨rels⟩ ∈ {1, a', b', a' * a', b' * a', b' * a' * a'} by free group induction
  apply @FreeGroup.induction_on (Fin 2) (fun y ↦ (QuotientGroup.mk y : PresentedGroup rels) ∈ ({1, a', b', a' * a', b' * a', b' * a' * a'} : Set (PresentedGroup rels))) _
  · -- base case: z = 1 ∈ {1, a', b', a' * a', b' * a', b' * a' * a'}
    exact Set.mem_insert 1 {a', b', a' * a', b' * a', b' * a' * a'}
  · -- base case: z = a ∈ {1, a', b', a' * a', b' * a', b' * a' * a'} or z = b ∈ {1, a', b', a' * a', b' * a', b' * a' * a'}
    intro i
    fin_cases i
    -- z = a
    right
    left
    exact rfl
    -- z = b
    right
    right
    left
    exact rfl
  · -- base case: z = a⁻¹ ∈ {1, a', b', a' * a', b' * a', b' * a' * a'} or z = b⁻¹ ∈ {1, a', b', a' * a', b' * a', b' * a' * a'}
    intro i hi
    fin_cases i
    -- z = a⁻¹
    right
    right
    right
    left
    exact eqainv
    -- z = b⁻¹
    right
    right
    left
    exact eqbinv
  · -- induction step: if x and y are in {1, a', b', a' * a', b' * a', b' * a' * a'}, then x * y is in {1, a', b', a' * a', b' * a', b' * a' * a'}
    intro x y xeq yeq
    have xyeq : @QuotientGroup.mk (FreeGroup (Fin 2)) FreeGroup.instGroup (Subgroup.normalClosure rels) (x * y) = (@QuotientGroup.mk (FreeGroup (Fin 2)) FreeGroup.instGroup (Subgroup.normalClosure rels) x) * (@QuotientGroup.mk (FreeGroup (Fin 2)) FreeGroup.instGroup (Subgroup.normalClosure rels) y) := by exact rfl
    rcases xeq with xeq | xeq | xeq | xeq | xeq | xeq
    · -- x = 1
      rw [xyeq, xeq, one_mul]
      exact yeq
    · -- x = a'
      rcases yeq with yeq | yeq | yeq | yeq | yeq | yeq
      · -- y = 1
        rw [xyeq, xeq, yeq, mul_one]
        right
        left
        exact rfl
      · -- y = a'
        rw [xyeq, xeq, yeq]
        right
        right
        right
        left
        exact rfl
      · -- y = b'
        rw [xyeq, xeq, yeq, eqab]
        right
        right
        right
        right
        right
        exact rfl
      · -- y = a' * a'
        rw [xyeq, xeq, yeq, ← mul_assoc, eqapow]
        exact Set.mem_insert 1 {a', b', a' * a', b' * a', b' * a' * a'}
      · -- y = b' * a'
        rw [xyeq, xeq, yeq, ← mul_assoc, eqab, mul_assoc, mul_assoc, eqapow, mul_one]
        right
        right
        left
        exact rfl
      · -- y = b' * a' * a'
        rw [xyeq, xeq, yeq, ← mul_assoc, ← mul_assoc, eqab, mul_assoc (b' * a'), mul_assoc (b' * a'), eqapow, mul_one]
        right
        right
        right
        right
        left
        exact rfl
    · -- x = b'
      rcases yeq with yeq | yeq | yeq | yeq | yeq | yeq
      · -- y = 1
        rw [xyeq, xeq, yeq, mul_one]
        right
        right
        left
        exact rfl
      · -- y = a'
        rw [xyeq, xeq, yeq]
        right
        right
        right
        right
        left
        exact rfl
      · -- y = b'
        rw [xyeq, xeq, yeq, eqbpow]
        exact Set.mem_insert 1 {a', b', a' * a', b' * a', b' * a' * a'}
      · -- y = a' * a'
        rw [xyeq, xeq, yeq, ← mul_assoc]
        right
        right
        right
        right
        right
        exact rfl
      · -- y = b' * a'
        rw [xyeq, xeq, yeq, ← mul_assoc, eqbpow, one_mul]
        right
        exact Set.mem_insert a' {b', a' * a', b' * a', b' * a' * a'}
      · -- y = b' * a' * a'
        rw [xyeq, xeq, yeq, ← mul_assoc, ← mul_assoc, eqbpow, one_mul]
        right
        right
        right
        exact Set.mem_insert (a' * a') {b' * a', b' * a' * a'}
    · -- x = a' * a'
      rcases yeq with yeq | yeq | yeq | yeq | yeq | yeq
      · -- y = 1
        rw [xyeq, xeq, yeq, mul_one]
        right
        right
        right
        exact Set.mem_insert (a' * a') {b' * a', b' * a' * a'}
      · -- y = a'
        rw [xyeq, xeq, yeq, eqapow]
        exact Set.mem_insert 1 {a', b', a' * a', b' * a', b' * a' * a'}
      · -- y = b'
        rw [xyeq, xeq, yeq, eqaab]
        right
        right
        right
        right
        exact Set.mem_insert (b' * a') {b' * (a' * a')}
      · -- y = a' * a'
        rw [xyeq, xeq, yeq, ← mul_assoc, eqapow, one_mul]
        right
        exact Set.mem_insert a' {b', a' * a', b' * a', b' * a' * a'}
      · -- y = b' * a'
        rw [xyeq, xeq, yeq, ← mul_assoc, eqaab]
        right
        right
        right
        right
        right
        exact rfl
      · -- y = b' * a' * a'
        rw [xyeq, xeq, yeq, ← mul_assoc, ← mul_assoc, eqaab, mul_assoc, mul_assoc, eqapow, mul_one]
        right
        right
        exact Set.mem_insert b' {a' * a', b' * a', b' * (a' * a')}
    · -- x = b' * a'
      rcases yeq with yeq | yeq | yeq | yeq | yeq | yeq
      · -- y = 1
        rw [xyeq, xeq, yeq, mul_one]
        right
        right
        right
        right
        exact Set.mem_insert (b' * a') {b' * a' * a'}
      · -- y = a'
        rw [xyeq, xeq, yeq]
        right
        right
        right
        right
        right
        exact rfl
      · -- y = b'
        rw [xyeq, xeq, yeq, mul_assoc b' a' b', eqab, ← mul_assoc, ← mul_assoc, eqbpow, one_mul]
        right
        right
        right
        exact Set.mem_insert (a' * a') {b' * a', b' * a' * a'}
      · -- y = a' * a'
        rw [xyeq, xeq, yeq, mul_assoc b' a' (a' * a'), ← mul_assoc a', eqapow, mul_one]
        right
        right
        exact Set.mem_insert b' {a' * a', b' * a', b' * a' * a'}
      · -- y = b' * a'
        rw [xyeq, xeq, yeq, ← mul_assoc, mul_assoc b' a' b', eqab, ← mul_assoc, ← mul_assoc, eqbpow, one_mul, eqapow]
        exact Set.mem_insert 1 {a', b', a' * a', b' * a', b' * a' * a'}
      · -- y = b' * a' * a'
        rw [xyeq, xeq, yeq, ← mul_assoc, ← mul_assoc, mul_assoc b' a' b', eqab, ← mul_assoc, ← mul_assoc, eqbpow, one_mul, eqapow, one_mul]
        right
        exact Set.mem_insert a' {b', a' * a', b' * a', b' * a' * a'}
    · -- x = b' * a' * a'
      rcases yeq with yeq | yeq | yeq | yeq | yeq | yeq
      · -- y = 1
        rw [xyeq, xeq, yeq, mul_one]
        right
        right
        right
        right
        right
        exact rfl
      · -- y = a'
        rw [xyeq, xeq, yeq, mul_assoc, mul_assoc, eqapow, mul_one]
        right
        right
        exact Set.mem_insert b' {a' * a', b' * a', b' * (a' * a')}
      · -- y = b'
        rw [xyeq, xeq, yeq, mul_assoc, mul_assoc, eqaab, ← mul_assoc b' b', eqbpow, one_mul]
        right
        exact Set.mem_insert a' {b', a' * a', b' * a', b' * (a' * a')}
      · -- y = a' * a'
        rw [xyeq, xeq, yeq, ← mul_assoc, mul_assoc, mul_assoc b', eqapow, mul_one]
        right
        right
        right
        right
        exact Set.mem_insert (b' * a') {b' * (a' * a')}
      · -- y = b' * a'
        rw [xyeq, xeq, yeq, ← mul_assoc, mul_assoc, mul_assoc b', eqaab, ← mul_assoc b' b', eqbpow, one_mul]
        right
        right
        right
        exact Set.mem_insert (a' * a') {b' * a', b' * (a' * a')}
      · -- y = b' * a' * a'
        rw [xyeq, xeq, yeq, ← mul_assoc, ← mul_assoc, mul_assoc b', mul_assoc b', eqaab, ← mul_assoc, ← mul_assoc, eqbpow, one_mul, eqapow]
        exact Set.mem_insert 1 {a', b', a' * a', b' * a', b' * a' * a'}

/-- Perm (Fin 3) has only six elements 1, c[1, 2, 3], c[1, 2], c[1, 3, 2], c[2, 3], c[1, 3] -/
lemma elemsperm : ∀ x : Perm (Fin 3), x ∈ ({1, c[1, 2, 3], c[1, 2], c[1, 3, 2], c[2, 3], c[1, 3]} : Set (Perm (Fin 3))) := by
  -- the cardinality of Perm (Fin 3) is 6
  have : Fintype.card (Perm (Fin 3)) = 6 := by
    exact rfl
  -- define f : Fin 6 → Perm (Fin 3) by f 0 = 1, f 1 = c[1, 2, 3], f 2 = c[1, 2], f 3 = c[1, 3, 2], f 4 = c[2, 3], f 5 = c[1, 3]
  let f : Fin 6 → Perm (Fin 3) := ![1, c[1, 2, 3], c[1, 2], c[1, 3, 2], c[2, 3], c[1, 3]]
  -- f is injective
  have inj_f : Injective f := by
    intro x y hxy
    -- we prove that f x = f y → x = y for:
    fin_cases x
    · -- x = 0
      fin_cases y
      -- y = 0
      exact rfl
      -- y = 1
      have : (1 : Perm (Fin 3)) ≠ c[1, 2, 3] := by
        exact ne_of_beq_false rfl
      contradiction
      -- y = 2
      have : (1 : Perm (Fin 3)) ≠ c[1, 2] := by
        exact ne_of_beq_false rfl
      contradiction
      -- y = 3
      have : (1 : Perm (Fin 3)) ≠ c[1, 3, 2] := by
        exact ne_of_beq_false rfl
      contradiction
      -- y = 4
      have : (1 : Perm (Fin 3)) ≠ c[2, 3] := by
        exact ne_of_beq_false rfl
      contradiction
      -- y = 5
      have : (1 : Perm (Fin 3)) ≠ c[1, 3] := by
        exact ne_of_beq_false rfl
      contradiction
    · -- x = 1
      fin_cases y
      -- y = 0
      have : (c[1, 2, 3] : Perm (Fin 3)) ≠ 1 := by
        exact ne_of_beq_false rfl
      contradiction
      -- y = 1
      exact rfl
      -- y = 2
      have : (c[1, 2, 3] : Perm (Fin 3)) ≠ c[1, 2] := by
        exact ne_of_beq_false rfl
      contradiction
      -- y = 3
      have : (c[1, 2, 3] : Perm (Fin 3)) ≠ c[1, 3, 2] := by
        exact ne_of_beq_false rfl
      contradiction
      -- y = 4
      have : (c[1, 2, 3] : Perm (Fin 3)) ≠ c[2, 3] := by
        exact ne_of_beq_false rfl
      contradiction
      -- y = 5
      have : (c[1, 2, 3] : Perm (Fin 3)) ≠ c[1, 3] := by
        exact ne_of_beq_false rfl
      contradiction
    · -- x = 2
      fin_cases y
      -- y = 0
      have : (c[1, 2] : Perm (Fin 3)) ≠ 1 := by
        exact ne_of_beq_false rfl
      contradiction
      -- y = 1
      have : (c[1, 2] : Perm (Fin 3)) ≠ c[1, 2, 3] := by
        exact ne_of_beq_false rfl
      contradiction
      -- y = 2
      exact rfl
      -- y = 3
      have : (c[1, 2] : Perm (Fin 3)) ≠ c[1, 3, 2] := by
        exact ne_of_beq_false rfl
      contradiction
      -- y = 4
      have : (c[1, 2] : Perm (Fin 3)) ≠ c[2, 3] := by
        exact ne_of_beq_false rfl
      contradiction
      -- y = 5
      have : (c[1, 2] : Perm (Fin 3)) ≠ c[1, 3] := by
        exact ne_of_beq_false rfl
      contradiction
    · -- x = 3
      fin_cases y
      -- y = 0
      have : (c[1, 3, 2] : Perm (Fin 3)) ≠ 1 := by
        exact ne_of_beq_false rfl
      contradiction
      -- y = 1
      have : (c[1, 3, 2] : Perm (Fin 3)) ≠ c[1, 2, 3] := by
        exact ne_of_beq_false rfl
      contradiction
      -- y = 2
      have : (c[1, 3, 2] : Perm (Fin 3)) ≠ c[1, 2] := by
        exact ne_of_beq_false rfl
      contradiction
      -- y = 3
      exact rfl
      -- y = 4
      have : (c[1, 3, 2] : Perm (Fin 3)) ≠ c[2, 3] := by
        exact ne_of_beq_false rfl
      contradiction
      -- y = 5
      have : (c[1, 3, 2] : Perm (Fin 3)) ≠ c[1, 3] := by
        exact ne_of_beq_false rfl
      contradiction
    · -- x = 4
      fin_cases y
      -- y = 0
      have : (c[2, 3] : Perm (Fin 3)) ≠ 1 := by
        exact ne_of_beq_false rfl
      contradiction
      -- y = 1
      have : (c[2, 3] : Perm (Fin 3)) ≠ c[1, 2, 3] := by
        exact ne_of_beq_false rfl
      contradiction
      -- y = 2
      have : (c[2, 3] : Perm (Fin 3)) ≠ c[1, 2] := by
        exact ne_of_beq_false rfl
      contradiction
      -- y = 3
      have : (c[2, 3] : Perm (Fin 3)) ≠ c[1, 3, 2] := by
        exact ne_of_beq_false rfl
      contradiction
      -- y = 4
      exact rfl
      -- y = 5
      have : (c[2, 3] : Perm (Fin 3)) ≠ c[1, 3] := by
        exact ne_of_beq_false rfl
      contradiction
    · -- x = 5
      fin_cases y
      -- y = 0
      have : (c[1, 3] : Perm (Fin 3)) ≠ 1 := by
        exact ne_of_beq_false rfl
      contradiction
      -- y = 1
      have : (c[1, 3] : Perm (Fin 3)) ≠ c[1, 2, 3] := by
        exact ne_of_beq_false rfl
      contradiction
      -- y = 2
      have : (c[1, 3] : Perm (Fin 3)) ≠ c[1, 2] := by
        exact ne_of_beq_false rfl
      contradiction
      -- y = 3
      have : (c[1, 3] : Perm (Fin 3)) ≠ c[1, 3, 2] := by
        exact ne_of_beq_false rfl
      contradiction
      -- y = 4
      have : (c[1, 3] : Perm (Fin 3)) ≠ c[2, 3] := by
        exact ne_of_beq_false rfl
      contradiction
      -- y = 5
      exact rfl
  -- there is a bijection equiv between Fin 6 and Perm (Fin 3)
  have equiv : Fin 6 ≃ Perm (Fin 3) := by exact (Fintype.equivFinOfCardEq this).symm
  -- f is surjective
  have surj_f : Surjective f := by exact Injective.surjective_of_fintype equiv inj_f
  -- for all x in Perm (Fin 3), x ∈ {1, c[1, 2, 3], c[1, 2], c[1, 3, 2], c[2, 3], c[1, 3]}
  intro x
  -- there exists i in Fin 6 such that f i = x
  rcases surj_f x with ⟨i, hi⟩
  fin_cases i
  -- if i = 0, then x = 1
  have : x = 1 := by exact id (Eq.symm hi)
  left
  exact this
  -- if i = 1, then x = c[1, 2, 3]
  have : x = c[1, 2, 3] := by exact id (Eq.symm hi)
  right
  left
  exact this
  -- if i = 2, then x = c[1, 2]
  have : x = c[1, 2] := by exact id (Eq.symm hi)
  right
  right
  left
  exact this
  -- if i = 3, then x = c[1, 3, 2]
  have : x = c[1, 3, 2] := by exact id (Eq.symm hi)
  right
  right
  right
  left
  exact this
  -- if i = 4, then x = c[2, 3]
  have : x = c[2, 3] := by exact id (Eq.symm hi)
  right
  right
  right
  right
  left
  exact this
  -- if i = 5, then x = c[1, 3]
  have : x = c[1, 3] := by exact id (Eq.symm hi)
  right
  right
  right
  right
  right
  exact this

/-- Show that H = ⟨a, b | a ^ 3 = 1, b ^ 2 = 1, b * a = a⁻¹ * b⟩ is a presentation of S₃-/
noncomputable def presentation : PresentedGroup rels ≃* Perm (Fin 3) := by
  -- define group morphism tof : PresentedGroup rels →* Perm (Fin 3) as the lift of FreeGroup (Fin 2) →* Perm (Fin 3), where we need to verify that rels is in the kernel of the latter map
  let tof : PresentedGroup rels →* Perm (Fin 3) := by
    -- let lifttof : FreeGroup (Fin 2) →* Perm (Fin 3) be induced by gnrttof : Fin 2 → Perm (Fin 3) that sends 0 to c[1, 2, 3] and 1 to c[1, 2]
    let lifttof : FreeGroup (Fin 2) →* Perm (Fin 3) := by
      -- define gnrttof : Fin 2 → Perm (Fin 3) by gnrttof 0 = c[1, 2, 3] and gnrttof 1 = c[1, 2]
      let gnrttof : (Fin 2) → Perm (Fin 3) := ![c[(1 : Fin 3), 2, 3], c[1, 2]]
      exact FreeGroup.lift gnrttof
    -- prove that the normal closure of rels is in the kernel of lifttof
    have Nleker : Subgroup.normalClosure rels ≤ lifttof.ker := by
      -- suffices to prove that rels is in the kernel of lifttof
      apply Subgroup.normalClosure_subset_iff.mp
      intro g gin
      -- suffices to prove that lifttof g = 1 for all g in rels
      apply MonoidHom.mem_ker.mpr
      rcases gin with geq | geq | geq
      · -- if g = a * a * a, then lifttof g = 1
        simp only [Fin.isValue, Cycle.formPerm_coe, List.formPerm_cons_cons, List.formPerm_singleton, mul_one, geq, map_mul, lifttof]
        -- suffices to show c[1, 2, 3] * c[1, 2, 3] * c[1, 2, 3] = 1
        show c[(1 : Fin 3), 2, 3] * c[(1 : Fin 3), 2, 3] * c[(1 : Fin 3), 2, 3] = 1
        rw [mul_assoc, ← pow_three]
        have threecycle : Perm.IsThreeCycle c[(1 : Fin 3), 2, 3] := by exact rfl
        apply Perm.IsThreeCycle.orderOf at threecycle
        rw [← pow_orderOf_eq_one c[(1 : Fin 3), 2, 3]]
        rw [threecycle]
      · -- if g = b * b, then lifttof g = 1
        simp only [Fin.isValue, Cycle.formPerm_coe, List.formPerm_cons_cons, List.formPerm_singleton, mul_one, geq, map_mul, lifttof]
        -- suffices to show c[1, 2] * c[1, 2] = 1
        show c[(1 : Fin 3), 2] * c[(1 : Fin 3), 2] = 1
        refine Perm.support_eq_empty_iff.mp ?_
        exact rfl
      · -- if g = a * b * a * b⁻¹, then lifttof g = 1
        rw [Set.mem_singleton_iff] at geq
        simp only [Fin.isValue, Cycle.formPerm_coe, List.formPerm_cons_cons, List.formPerm_singleton, mul_one, geq, map_mul, lifttof]
        -- suffices to show c[1, 2, 3] * c[1, 2] * c[1, 2, 3] * c[1, 2]⁻¹ = 1
        show c[(1 : Fin 3), 2, 3] * c[(1 : Fin 3), 2] * c[(1 : Fin 3), 2, 3] * c[(1 : Fin 3), 2]⁻¹ = 1
        ext i
        fin_cases i
        simp only [Fin.isValue, Cycle.formPerm_coe, List.formPerm_cons_cons, List.formPerm_singleton, mul_one, swap_inv, Fin.zero_eta, Perm.coe_mul, comp_apply, swap_apply_self, Fin.val_zero, Perm.coe_one, id_eq]
        simp only [Fin.isValue, Cycle.formPerm_coe, List.formPerm_cons_cons, List.formPerm_singleton, mul_one, swap_inv, Fin.zero_eta, Perm.coe_mul, comp_apply, swap_apply_self, Fin.val_zero, Perm.coe_one, id_eq]
        simp only [Fin.isValue, Cycle.formPerm_coe, List.formPerm_cons_cons, List.formPerm_singleton, mul_one, swap_inv, Fin.zero_eta, Perm.coe_mul, comp_apply, swap_apply_self, Fin.val_zero, Perm.coe_one, id_eq]
    -- since rels is in the normal closure of rels, gnrttof induces the group morphism lifttof : H →* Perm (Fin 3)
    exact QuotientGroup.lift (Subgroup.normalClosure rels) lifttof Nleker
  -- prove that tof is bijective, so that PresentedGroup rels ≃* Perm (Fin 3). define g as the inverse of tof
  have bij_tof : Bijective tof := by
    -- suffices to prove that tof has an inverse
    refine bijective_iff_has_inverse.mpr ?_
    -- define g : Perm (Fin 3) → PresentedGroup rels by g c[1, 2, 3] = a', g c[1, 2] = b', g c[1, 3, 2] = a' * a', g c[2, 3] = b' * a', g c[1, 3] = b' * a' * a'
    let g : Perm (Fin 3) → PresentedGroup rels := by
      intro x
      if x1 : x = 1 then
        exact 1
      else if x2 : x = c[1, 2, 3] then
        exact a'
      else if x3 : x = c[1, 2] then
        exact b'
      else if x4 : x = c[1, 3, 2] then
        exact a' * a'
      else if x5 : x = c[2, 3] then
        exact b' * a'
      else if x6 : x = c[1, 3] then
        exact b' * a' * a'
      else
        absurd x6
        rcases elemsperm x with hx | hx | hx | hx | hx | hx
        contradiction
        contradiction
        contradiction
        contradiction
        contradiction
        exact hx
    -- prove that g is an inverse of tof
    use g
    -- tof a' = c[1, 2, 3]
    have fa : tof a' = c[1, 2, 3] := by exact rfl
    -- tof b' = c[1, 2]
    have fb : tof b' = c[1, 2] := by exact rfl
    -- tof (a' * a') = c[1, 3, 2]
    have faa : tof (a' * a') = c[1, 3, 2] := by
      rw [map_mul, fa]
      ext i
      fin_cases i
      exact rfl
      exact rfl
      exact rfl
    -- tof (b' * a') = c[2, 3]
    have fba : tof (b' * a') = c[2, 3] := by
      rw [map_mul, fa, fb]
      ext i
      fin_cases i
      exact rfl
      exact rfl
      exact rfl
    -- tof (b' * a' * a') = c[1, 3]
    have fbaa : tof (b' * a' * a') = c[1, 3] := by
      rw [map_mul, fba, fa]
      ext i
      fin_cases i
      exact rfl
      exact rfl
      exact rfl
    constructor
    · -- g is a left inverse of tof
      intro x
      -- g (tof x) = x for all x in H = {1, a', b', a' * a', b' * a', b' * a' * a'}
      rcases elemspre x with hx | hx | hx | hx | hx | hx
      -- x = 1
      simp only [Fin.isValue, Cycle.formPerm_coe, List.formPerm_cons_cons, List.formPerm_singleton, mul_one, hx, map_one, ↓reduceDIte, g, tof]
      -- x = a'
      rw [hx, fa]
      exact rfl
      -- x = b'
      rw [hx, fb]
      exact rfl
      -- x = a' * a'
      rw [hx, faa]
      exact rfl
      -- x = b' * a'
      rw [hx, fba]
      exact rfl
      -- x = b' * a' * a'
      rw [hx, fbaa]
      exact rfl
    · -- g is a right inverse of tof
      intro x
      rcases elemsperm x with hx | hx | hx | hx | hx | hx
      -- x = 1
      rw [hx]
      exact rfl
      -- x = c[1, 2, 3]
      rw [hx]
      exact rfl
      -- x = c[1, 2]
      rw [hx]
      exact rfl
      -- x = c[1, 3, 2]
      have gaa : g c[1, 3, 2] = a' * a' := by exact rfl
      rw [hx, gaa, faa]
      -- x = c[2, 3]
      have gba : g c[2, 3] = b' * a' := by exact rfl
      rw [hx, gba, fba]
      -- x = c[1, 3]
      have gbaa : g c[1, 3] = b' * a' * a' := by exact rfl
      rw [hx, gbaa, fbaa]
  -- construct an equivalence equiv : PresentedGroup rels ≃ Perm (Fin 3) using tof
  let equiv : PresentedGroup rels ≃ Perm (Fin 3) := by
    exact ofBijective (⇑tof) bij_tof
  -- prove that equiv is a group isomorphism
  refine MulEquiv.mk' equiv ?_
  intro x y
  -- tof (x * y) = tof x * tof y for all x, y in H
  show tof (x * y) = tof x * tof y
  exact MonoidHom.map_mul tof x y
","formalStatement":null,"suggestion":null,"comment":"<p>希望升为hard</p>"},"judgement":{"result":"resubmit","score":5,"suggestion":"<p>题目要求证明的是六阶非交换群在同构意义下可以唯一表示成这样，且证明其同构于S3</p>","feedbackAction":"resubmit","comment":""},"stepInfo":null,"userInfo":{"id":420,"username":"nizixi","nickname":"Move fast","avatar":"//p1-arco.byteimg.com/tos-cn-i-uwbnlip3yd/a8c8cdb109cb051163646151a4a5083b.png~tplv-uwbnlip3yd-webp.webp","email":"821345763@qq.com"},"judgeUserInfo":{"id":351,"username":"Yuxintao","nickname":"Yuxintao","avatar":"//p1-arco.byteimg.com/tos-cn-i-uwbnlip3yd/a8c8cdb109cb051163646151a4a5083b.png~tplv-uwbnlip3yd-webp.webp","email":"1472388812@qq.com"}},{"created":"2025-05-23 01:49:21","updated":"2025-05-23 14:34:07","id":9122,"questionId":3277,"taskId":2510,"jobId":7007,"userId":420,"judgeUserId":351,"answer":{"informalProof":null,"formalProof":"import Mathlib
import Mathlib.Tactic
import Mathlib.Data.Fintype.Basic
import Mathlib.GroupTheory.Perm.Cycle.Concrete
import Mathlib.GroupTheory.Perm.Subgroup

set_option maxHeartbeats 0
open Equiv
open Function
open Equiv Function
/- **Step 1**If G is a nonabelian group of order 6, prove that G ≃ S₃ -/
/-- A useful lemma-/
lemma eqtwoofne (n : Fin 3) : n ≠ 0 → n ≠ 1 → n = 2 := by
  intro n0 n1
  fin_omega
/-- A useful lemma-/
lemma eqsixofne (n : Fin 7) : n ≠ 0 → n ≠ 1 → n ≠ 2 → n ≠ 3 → n ≠ 4 → n ≠ 5 → n = 6 := by
  intro n0 n1 n2 n3 n4 n5
  fin_omega
variable {G : Type*} [Group G] [Fintype G] {hcard : Fintype.card G = 6} {a b : G} {hab : a * b ≠ b * a}
-- the following tedious arguments are to show that 1, a, b, ab, ba are five distinct elements of G,
-- and except them there is only one element left.
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

/-- for G and noncommutative pairs a, b, we first prove that if a²≠1 then G ≃* S₃ 
via map a ↦ c[1, 2, 3] and b ↦ c[1, 2],  then prove the same when both a²=b²=1. 
So first we introduce the following intermediate lemma-/
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

open Equiv Function
/-**Step 2**Prove that the presentation
\[
\left(a, b: a^{3}=1, b^{2}=1, b a=a^{2} b\right)
\]
gives (up to isomorphism) the only nonabelian group of order 6.-/
/- let a, b represent (123) and (12) respectively, and let rels be the relations {a ^ 3 = b ^ 2 = 1, a * b * a * b⁻¹ = 1}. We show that {a, b} generates S_3 and rels is the relation (that is, S_3 is presented by rels) -/
/-- define the elements a of the free group F₂ -/
def a1 := FreeGroup.mk [((0 : Fin 2), true)]
/-- define the element b of the free group F₂ -/
def b1 := FreeGroup.mk [((1 : Fin 2), true)]
/-- define rels, the relations of the presentation H -/
def rels : Set (FreeGroup (Fin 2)) := {a1 * a1 * a1, b1 * b1, a1 * b1 * a1 * (b1)⁻¹}

/-- define the elements a' of H -/
def a' : (PresentedGroup rels) := QuotientGroup.mk a1
/-- define the elements b' of H -/
def b' : (PresentedGroup rels) := QuotientGroup.mk b1
/-- a' * a' * a' = 1 in H -/
lemma eqapow : a' * a' * a' = 1 := by
  show QuotientGroup.mk (a1 * a1 * a1) = 1
  refine (QuotientGroup.eq_one_iff (a1 * a1 * a1)).mpr ?_
  -- a * a * a ∈ rels
  have ain : a1 * a1 * a1 ∈ rels := by
    left
    exact rfl
  have relsle : rels ≤ Subgroup.normalClosure rels := by refine Set.le_iff_subset.mpr ?_; exact Subgroup.subset_normalClosure
  exact relsle ain
/-- b' * b' = 1 in H -/
lemma eqbpow : b' * b' = 1 := by
  show QuotientGroup.mk (b1 * b1) = 1
  refine (QuotientGroup.eq_one_iff (b1 * b1)).mpr ?_
  -- b * b ∈ rels
  have bin : b1 * b1 ∈ rels := by
    right
    left
    exact rfl
  have relsle : rels ≤ Subgroup.normalClosure rels := by refine Set.le_iff_subset.mpr ?_; exact Subgroup.subset_normalClosure
  exact relsle bin
/-- a'⁻¹ = a' * a' in H -/
lemma eqainv : a'⁻¹ = a' * a' := by
  refine inv_eq_of_mul_eq_one_left ?h
  exact eqapow
/-- b⁻¹ '= b' -/
lemma eqbinv : b'⁻¹ = b' := by
  refine DivisionMonoid.inv_eq_of_mul b' b' ?_
  exact eqbpow
/-- a' * b' = b' * a' * a' -/
lemma eqab : a' * b' = b' * a' * a' := by
  have mid : a' * b' * a' * b'⁻¹ = 1 := by
    show QuotientGroup.mk (a1 * b1 * a1 * (b1)⁻¹) = 1
    refine (QuotientGroup.eq_one_iff (a1 * b1 * a1 * (b1)⁻¹)).mpr ?_
    -- a * b * a * b⁻¹ ∈ rels, so a' * b' * a' * b'⁻¹ = 1 in H
    have cin : a1 * b1 * a1 * (b1)⁻¹ ∈ rels := by
      right
      right
      exact rfl
    have relsle : rels ≤ Subgroup.normalClosure rels := by refine Set.le_iff_subset.mpr ?_; exact Subgroup.subset_normalClosure
    exact relsle cin
  -- by some algebraic manipulation, we can show that a' * b' = b' * a' * a'
  rw [← mul_one (a' * b'), ← eqapow, ← mul_assoc, ← mul_assoc, ← mul_one (a' * b' * a'), ← eqbpow, ← mul_assoc]
  nth_rw 2 [← eqbinv]
  rw [mid, one_mul]
/-- a' * a' * b' = b' * a' -/
lemma eqaab : a' * a' * b' = b' * a' := by
  rw [mul_assoc a', eqab, ← mul_assoc, ← mul_assoc, eqab, mul_assoc b', mul_assoc b', eqapow, mul_one]

/-- H has only six elements 1, a', b', a' * a', b' * a', b' * a' * a' -/
lemma elemspre : ∀ x : PresentedGroup rels, x ∈ ({1, a', b', a' * a', b' * a', b' * a' * a'} : Set (PresentedGroup rels)) := by
  intro _
  -- we prove that x ∈ {1, a', b', a' * a', b' * a', b' * a' * a'} by proving that for all z in F₂, z / ⟨rels⟩ ∈ {1, a', b', a' * a', b' * a', b' * a' * a'}
  apply QuotientGroup.induction_on
  intro _
  -- we prove that z / ⟨rels⟩ ∈ {1, a', b', a' * a', b' * a', b' * a' * a'} by free group induction
  apply @FreeGroup.induction_on (Fin 2) (fun y ↦ (QuotientGroup.mk y : PresentedGroup rels) ∈ ({1, a', b', a' * a', b' * a', b' * a' * a'} : Set (PresentedGroup rels))) _
  · -- base case: z = 1 ∈ {1, a', b', a' * a', b' * a', b' * a' * a'}
    exact Set.mem_insert 1 {a', b', a' * a', b' * a', b' * a' * a'}
  · -- base case: z = a ∈ {1, a', b', a' * a', b' * a', b' * a' * a'} or z = b ∈ {1, a', b', a' * a', b' * a', b' * a' * a'}
    intro i
    fin_cases i
    -- z = a
    right
    left
    exact rfl
    -- z = b
    right
    right
    left
    exact rfl
  · -- base case: z = a⁻¹ ∈ {1, a', b', a' * a', b' * a', b' * a' * a'} or z = b⁻¹ ∈ {1, a', b', a' * a', b' * a', b' * a' * a'}
    intro i hi
    fin_cases i
    -- z = a⁻¹
    right
    right
    right
    left
    exact eqainv
    -- z = b⁻¹
    right
    right
    left
    exact eqbinv
  · -- induction step: if x and y are in {1, a', b', a' * a', b' * a', b' * a' * a'}, then x * y is in {1, a', b', a' * a', b' * a', b' * a' * a'}
    intro x y xeq yeq
    have xyeq : @QuotientGroup.mk (FreeGroup (Fin 2)) FreeGroup.instGroup (Subgroup.normalClosure rels) (x * y) = (@QuotientGroup.mk (FreeGroup (Fin 2)) FreeGroup.instGroup (Subgroup.normalClosure rels) x) * (@QuotientGroup.mk (FreeGroup (Fin 2)) FreeGroup.instGroup (Subgroup.normalClosure rels) y) := by exact rfl
    rcases xeq with xeq | xeq | xeq | xeq | xeq | xeq
    · -- x = 1
      rw [xyeq, xeq, one_mul]
      exact yeq
    · -- x = a'
      rcases yeq with yeq | yeq | yeq | yeq | yeq | yeq
      · -- y = 1
        rw [xyeq, xeq, yeq, mul_one]
        right
        left
        exact rfl
      · -- y = a'
        rw [xyeq, xeq, yeq]
        right
        right
        right
        left
        exact rfl
      · -- y = b'
        rw [xyeq, xeq, yeq, eqab]
        right
        right
        right
        right
        right
        exact rfl
      · -- y = a' * a'
        rw [xyeq, xeq, yeq, ← mul_assoc, eqapow]
        exact Set.mem_insert 1 {a', b', a' * a', b' * a', b' * a' * a'}
      · -- y = b' * a'
        rw [xyeq, xeq, yeq, ← mul_assoc, eqab, mul_assoc, mul_assoc, eqapow, mul_one]
        right
        right
        left
        exact rfl
      · -- y = b' * a' * a'
        rw [xyeq, xeq, yeq, ← mul_assoc, ← mul_assoc, eqab, mul_assoc (b' * a'), mul_assoc (b' * a'), eqapow, mul_one]
        right
        right
        right
        right
        left
        exact rfl
    · -- x = b'
      rcases yeq with yeq | yeq | yeq | yeq | yeq | yeq
      · -- y = 1
        rw [xyeq, xeq, yeq, mul_one]
        right
        right
        left
        exact rfl
      · -- y = a'
        rw [xyeq, xeq, yeq]
        right
        right
        right
        right
        left
        exact rfl
      · -- y = b'
        rw [xyeq, xeq, yeq, eqbpow]
        exact Set.mem_insert 1 {a', b', a' * a', b' * a', b' * a' * a'}
      · -- y = a' * a'
        rw [xyeq, xeq, yeq, ← mul_assoc]
        right
        right
        right
        right
        right
        exact rfl
      · -- y = b' * a'
        rw [xyeq, xeq, yeq, ← mul_assoc, eqbpow, one_mul]
        right
        exact Set.mem_insert a' {b', a' * a', b' * a', b' * a' * a'}
      · -- y = b' * a' * a'
        rw [xyeq, xeq, yeq, ← mul_assoc, ← mul_assoc, eqbpow, one_mul]
        right
        right
        right
        exact Set.mem_insert (a' * a') {b' * a', b' * a' * a'}
    · -- x = a' * a'
      rcases yeq with yeq | yeq | yeq | yeq | yeq | yeq
      · -- y = 1
        rw [xyeq, xeq, yeq, mul_one]
        right
        right
        right
        exact Set.mem_insert (a' * a') {b' * a', b' * a' * a'}
      · -- y = a'
        rw [xyeq, xeq, yeq, eqapow]
        exact Set.mem_insert 1 {a', b', a' * a', b' * a', b' * a' * a'}
      · -- y = b'
        rw [xyeq, xeq, yeq, eqaab]
        right
        right
        right
        right
        exact Set.mem_insert (b' * a') {b' * (a' * a')}
      · -- y = a' * a'
        rw [xyeq, xeq, yeq, ← mul_assoc, eqapow, one_mul]
        right
        exact Set.mem_insert a' {b', a' * a', b' * a', b' * a' * a'}
      · -- y = b' * a'
        rw [xyeq, xeq, yeq, ← mul_assoc, eqaab]
        right
        right
        right
        right
        right
        exact rfl
      · -- y = b' * a' * a'
        rw [xyeq, xeq, yeq, ← mul_assoc, ← mul_assoc, eqaab, mul_assoc, mul_assoc, eqapow, mul_one]
        right
        right
        exact Set.mem_insert b' {a' * a', b' * a', b' * (a' * a')}
    · -- x = b' * a'
      rcases yeq with yeq | yeq | yeq | yeq | yeq | yeq
      · -- y = 1
        rw [xyeq, xeq, yeq, mul_one]
        right
        right
        right
        right
        exact Set.mem_insert (b' * a') {b' * a' * a'}
      · -- y = a'
        rw [xyeq, xeq, yeq]
        right
        right
        right
        right
        right
        exact rfl
      · -- y = b'
        rw [xyeq, xeq, yeq, mul_assoc b' a' b', eqab, ← mul_assoc, ← mul_assoc, eqbpow, one_mul]
        right
        right
        right
        exact Set.mem_insert (a' * a') {b' * a', b' * a' * a'}
      · -- y = a' * a'
        rw [xyeq, xeq, yeq, mul_assoc b' a' (a' * a'), ← mul_assoc a', eqapow, mul_one]
        right
        right
        exact Set.mem_insert b' {a' * a', b' * a', b' * a' * a'}
      · -- y = b' * a'
        rw [xyeq, xeq, yeq, ← mul_assoc, mul_assoc b' a' b', eqab, ← mul_assoc, ← mul_assoc, eqbpow, one_mul, eqapow]
        exact Set.mem_insert 1 {a', b', a' * a', b' * a', b' * a' * a'}
      · -- y = b' * a' * a'
        rw [xyeq, xeq, yeq, ← mul_assoc, ← mul_assoc, mul_assoc b' a' b', eqab, ← mul_assoc, ← mul_assoc, eqbpow, one_mul, eqapow, one_mul]
        right
        exact Set.mem_insert a' {b', a' * a', b' * a', b' * a' * a'}
    · -- x = b' * a' * a'
      rcases yeq with yeq | yeq | yeq | yeq | yeq | yeq
      · -- y = 1
        rw [xyeq, xeq, yeq, mul_one]
        right
        right
        right
        right
        right
        exact rfl
      · -- y = a'
        rw [xyeq, xeq, yeq, mul_assoc, mul_assoc, eqapow, mul_one]
        right
        right
        exact Set.mem_insert b' {a' * a', b' * a', b' * (a' * a')}
      · -- y = b'
        rw [xyeq, xeq, yeq, mul_assoc, mul_assoc, eqaab, ← mul_assoc b' b', eqbpow, one_mul]
        right
        exact Set.mem_insert a' {b', a' * a', b' * a', b' * (a' * a')}
      · -- y = a' * a'
        rw [xyeq, xeq, yeq, ← mul_assoc, mul_assoc, mul_assoc b', eqapow, mul_one]
        right
        right
        right
        right
        exact Set.mem_insert (b' * a') {b' * (a' * a')}
      · -- y = b' * a'
        rw [xyeq, xeq, yeq, ← mul_assoc, mul_assoc, mul_assoc b', eqaab, ← mul_assoc b' b', eqbpow, one_mul]
        right
        right
        right
        exact Set.mem_insert (a' * a') {b' * a', b' * (a' * a')}
      · -- y = b' * a' * a'
        rw [xyeq, xeq, yeq, ← mul_assoc, ← mul_assoc, mul_assoc b', mul_assoc b', eqaab, ← mul_assoc, ← mul_assoc, eqbpow, one_mul, eqapow]
        exact Set.mem_insert 1 {a', b', a' * a', b' * a', b' * a' * a'}

/-- Perm (Fin 3) has only six elements 1, c[1, 2, 3], c[1, 2], c[1, 3, 2], c[2, 3], c[1, 3] -/
lemma elemsperm : ∀ x : Perm (Fin 3), x ∈ ({1, c[1, 2, 3], c[1, 2], c[1, 3, 2], c[2, 3], c[1, 3]} : Set (Perm (Fin 3))) := by
  -- the cardinality of Perm (Fin 3) is 6
  have : Fintype.card (Perm (Fin 3)) = 6 := by
    exact rfl
  -- define f : Fin 6 → Perm (Fin 3) by f 0 = 1, f 1 = c[1, 2, 3], f 2 = c[1, 2], f 3 = c[1, 3, 2], f 4 = c[2, 3], f 5 = c[1, 3]
  let f : Fin 6 → Perm (Fin 3) := ![1, c[1, 2, 3], c[1, 2], c[1, 3, 2], c[2, 3], c[1, 3]]
  -- f is injective
  have inj_f : Injective f := by
    intro x y hxy
    -- we prove that f x = f y → x = y for:
    fin_cases x
    · -- x = 0
      fin_cases y
      -- y = 0
      exact rfl
      -- y = 1
      have : (1 : Perm (Fin 3)) ≠ c[1, 2, 3] := by
        exact ne_of_beq_false rfl
      contradiction
      -- y = 2
      have : (1 : Perm (Fin 3)) ≠ c[1, 2] := by
        exact ne_of_beq_false rfl
      contradiction
      -- y = 3
      have : (1 : Perm (Fin 3)) ≠ c[1, 3, 2] := by
        exact ne_of_beq_false rfl
      contradiction
      -- y = 4
      have : (1 : Perm (Fin 3)) ≠ c[2, 3] := by
        exact ne_of_beq_false rfl
      contradiction
      -- y = 5
      have : (1 : Perm (Fin 3)) ≠ c[1, 3] := by
        exact ne_of_beq_false rfl
      contradiction
    · -- x = 1
      fin_cases y
      -- y = 0
      have : (c[1, 2, 3] : Perm (Fin 3)) ≠ 1 := by
        exact ne_of_beq_false rfl
      contradiction
      -- y = 1
      exact rfl
      -- y = 2
      have : (c[1, 2, 3] : Perm (Fin 3)) ≠ c[1, 2] := by
        exact ne_of_beq_false rfl
      contradiction
      -- y = 3
      have : (c[1, 2, 3] : Perm (Fin 3)) ≠ c[1, 3, 2] := by
        exact ne_of_beq_false rfl
      contradiction
      -- y = 4
      have : (c[1, 2, 3] : Perm (Fin 3)) ≠ c[2, 3] := by
        exact ne_of_beq_false rfl
      contradiction
      -- y = 5
      have : (c[1, 2, 3] : Perm (Fin 3)) ≠ c[1, 3] := by
        exact ne_of_beq_false rfl
      contradiction
    · -- x = 2
      fin_cases y
      -- y = 0
      have : (c[1, 2] : Perm (Fin 3)) ≠ 1 := by
        exact ne_of_beq_false rfl
      contradiction
      -- y = 1
      have : (c[1, 2] : Perm (Fin 3)) ≠ c[1, 2, 3] := by
        exact ne_of_beq_false rfl
      contradiction
      -- y = 2
      exact rfl
      -- y = 3
      have : (c[1, 2] : Perm (Fin 3)) ≠ c[1, 3, 2] := by
        exact ne_of_beq_false rfl
      contradiction
      -- y = 4
      have : (c[1, 2] : Perm (Fin 3)) ≠ c[2, 3] := by
        exact ne_of_beq_false rfl
      contradiction
      -- y = 5
      have : (c[1, 2] : Perm (Fin 3)) ≠ c[1, 3] := by
        exact ne_of_beq_false rfl
      contradiction
    · -- x = 3
      fin_cases y
      -- y = 0
      have : (c[1, 3, 2] : Perm (Fin 3)) ≠ 1 := by
        exact ne_of_beq_false rfl
      contradiction
      -- y = 1
      have : (c[1, 3, 2] : Perm (Fin 3)) ≠ c[1, 2, 3] := by
        exact ne_of_beq_false rfl
      contradiction
      -- y = 2
      have : (c[1, 3, 2] : Perm (Fin 3)) ≠ c[1, 2] := by
        exact ne_of_beq_false rfl
      contradiction
      -- y = 3
      exact rfl
      -- y = 4
      have : (c[1, 3, 2] : Perm (Fin 3)) ≠ c[2, 3] := by
        exact ne_of_beq_false rfl
      contradiction
      -- y = 5
      have : (c[1, 3, 2] : Perm (Fin 3)) ≠ c[1, 3] := by
        exact ne_of_beq_false rfl
      contradiction
    · -- x = 4
      fin_cases y
      -- y = 0
      have : (c[2, 3] : Perm (Fin 3)) ≠ 1 := by
        exact ne_of_beq_false rfl
      contradiction
      -- y = 1
      have : (c[2, 3] : Perm (Fin 3)) ≠ c[1, 2, 3] := by
        exact ne_of_beq_false rfl
      contradiction
      -- y = 2
      have : (c[2, 3] : Perm (Fin 3)) ≠ c[1, 2] := by
        exact ne_of_beq_false rfl
      contradiction
      -- y = 3
      have : (c[2, 3] : Perm (Fin 3)) ≠ c[1, 3, 2] := by
        exact ne_of_beq_false rfl
      contradiction
      -- y = 4
      exact rfl
      -- y = 5
      have : (c[2, 3] : Perm (Fin 3)) ≠ c[1, 3] := by
        exact ne_of_beq_false rfl
      contradiction
    · -- x = 5
      fin_cases y
      -- y = 0
      have : (c[1, 3] : Perm (Fin 3)) ≠ 1 := by
        exact ne_of_beq_false rfl
      contradiction
      -- y = 1
      have : (c[1, 3] : Perm (Fin 3)) ≠ c[1, 2, 3] := by
        exact ne_of_beq_false rfl
      contradiction
      -- y = 2
      have : (c[1, 3] : Perm (Fin 3)) ≠ c[1, 2] := by
        exact ne_of_beq_false rfl
      contradiction
      -- y = 3
      have : (c[1, 3] : Perm (Fin 3)) ≠ c[1, 3, 2] := by
        exact ne_of_beq_false rfl
      contradiction
      -- y = 4
      have : (c[1, 3] : Perm (Fin 3)) ≠ c[2, 3] := by
        exact ne_of_beq_false rfl
      contradiction
      -- y = 5
      exact rfl
  -- there is a bijection equiv between Fin 6 and Perm (Fin 3)
  have equiv : Fin 6 ≃ Perm (Fin 3) := by exact (Fintype.equivFinOfCardEq this).symm
  -- f is surjective
  have surj_f : Surjective f := by exact Injective.surjective_of_fintype equiv inj_f
  -- for all x in Perm (Fin 3), x ∈ {1, c[1, 2, 3], c[1, 2], c[1, 3, 2], c[2, 3], c[1, 3]}
  intro x
  -- there exists i in Fin 6 such that f i = x
  rcases surj_f x with ⟨i, hi⟩
  fin_cases i
  -- if i = 0, then x = 1
  have : x = 1 := by exact id (Eq.symm hi)
  left
  exact this
  -- if i = 1, then x = c[1, 2, 3]
  have : x = c[1, 2, 3] := by exact id (Eq.symm hi)
  right
  left
  exact this
  -- if i = 2, then x = c[1, 2]
  have : x = c[1, 2] := by exact id (Eq.symm hi)
  right
  right
  left
  exact this
  -- if i = 3, then x = c[1, 3, 2]
  have : x = c[1, 3, 2] := by exact id (Eq.symm hi)
  right
  right
  right
  left
  exact this
  -- if i = 4, then x = c[2, 3]
  have : x = c[2, 3] := by exact id (Eq.symm hi)
  right
  right
  right
  right
  left
  exact this
  -- if i = 5, then x = c[1, 3]
  have : x = c[1, 3] := by exact id (Eq.symm hi)
  right
  right
  right
  right
  right
  exact this

/-- now we prove that H ≃* S₃ -/
noncomputable def presentation : PresentedGroup rels ≃* Perm (Fin 3) := by
  -- define group morphism tof : PresentedGroup rels →* Perm (Fin 3) as the lift of FreeGroup (Fin 2) →* Perm (Fin 3), where we need to verify that rels is in the kernel of the latter map
  let tof : PresentedGroup rels →* Perm (Fin 3) := by
    -- let lifttof : FreeGroup (Fin 2) →* Perm (Fin 3) be induced by gnrttof : Fin 2 → Perm (Fin 3) that sends 0 to c[1, 2, 3] and 1 to c[1, 2]
    let lifttof : FreeGroup (Fin 2) →* Perm (Fin 3) := by
      -- define gnrttof : Fin 2 → Perm (Fin 3) by gnrttof 0 = c[1, 2, 3] and gnrttof 1 = c[1, 2]
      let gnrttof : (Fin 2) → Perm (Fin 3) := ![c[(1 : Fin 3), 2, 3], c[1, 2]]
      exact FreeGroup.lift gnrttof
    -- prove that the normal closure of rels is in the kernel of lifttof
    have Nleker : Subgroup.normalClosure rels ≤ lifttof.ker := by
      -- suffices to prove that rels is in the kernel of lifttof
      apply Subgroup.normalClosure_subset_iff.mp
      intro g gin
      -- suffices to prove that lifttof g = 1 for all g in rels
      apply MonoidHom.mem_ker.mpr
      rcases gin with geq | geq | geq
      · -- if g = a * a * a, then lifttof g = 1
        simp only [Fin.isValue, Cycle.formPerm_coe, List.formPerm_cons_cons, List.formPerm_singleton, mul_one, geq, map_mul, lifttof]
        -- suffices to show c[1, 2, 3] * c[1, 2, 3] * c[1, 2, 3] = 1
        show c[(1 : Fin 3), 2, 3] * c[(1 : Fin 3), 2, 3] * c[(1 : Fin 3), 2, 3] = 1
        rw [mul_assoc, ← pow_three]
        have threecycle : Perm.IsThreeCycle c[(1 : Fin 3), 2, 3] := by 
          exact card_support_eq_three_iff.mp rfl
        apply Perm.IsThreeCycle.orderOf at threecycle
        rw [← pow_orderOf_eq_one c[(1 : Fin 3), 2, 3]]
        rw [threecycle]
      · -- if g = b * b, then lifttof g = 1
        simp only [Fin.isValue, Cycle.formPerm_coe, List.formPerm_cons_cons, List.formPerm_singleton, mul_one, geq, map_mul, lifttof]
        -- suffices to show c[1, 2] * c[1, 2] = 1
        show c[(1 : Fin 3), 2] * c[(1 : Fin 3), 2] = 1
        refine Perm.support_eq_empty_iff.mp ?_
        exact rfl
      · -- if g = a * b * a * b⁻¹, then lifttof g = 1
        rw [Set.mem_singleton_iff] at geq
        simp only [Fin.isValue, Cycle.formPerm_coe, List.formPerm_cons_cons, List.formPerm_singleton, mul_one, geq, map_mul, lifttof]
        -- suffices to show c[1, 2, 3] * c[1, 2] * c[1, 2, 3] * c[1, 2]⁻¹ = 1
        show c[(1 : Fin 3), 2, 3] * c[(1 : Fin 3), 2] * c[(1 : Fin 3), 2, 3] * c[(1 : Fin 3), 2]⁻¹ = 1
        ext i
        fin_cases i
        simp only [Fin.isValue, Cycle.formPerm_coe, List.formPerm_cons_cons, List.formPerm_singleton, mul_one, swap_inv, Fin.zero_eta, Perm.coe_mul, comp_apply, swap_apply_self, Fin.val_zero, Perm.coe_one, id_eq]
        simp only [Fin.isValue, Cycle.formPerm_coe, List.formPerm_cons_cons, List.formPerm_singleton, mul_one, swap_inv, Fin.zero_eta, Perm.coe_mul, comp_apply, swap_apply_self, Fin.val_zero, Perm.coe_one, id_eq]
        simp only [Fin.isValue, Cycle.formPerm_coe, List.formPerm_cons_cons, List.formPerm_singleton, mul_one, swap_inv, Fin.zero_eta, Perm.coe_mul, comp_apply, swap_apply_self, Fin.val_zero, Perm.coe_one, id_eq]
    -- since rels is in the normal closure of rels, gnrttof induces the group morphism lifttof : H →* Perm (Fin 3)
    exact QuotientGroup.lift (Subgroup.normalClosure rels) lifttof Nleker
  -- prove that tof is bijective, so that PresentedGroup rels ≃* Perm (Fin 3). define g as the inverse of tof
  have bij_tof : Bijective tof := by
    -- suffices to prove that tof has an inverse
    refine bijective_iff_has_inverse.mpr ?_
    -- define g : Perm (Fin 3) → PresentedGroup rels by g c[1, 2, 3] = a', g c[1, 2] = b', g c[1, 3, 2] = a' * a', g c[2, 3] = b' * a', g c[1, 3] = b' * a' * a'
    let g : Perm (Fin 3) → PresentedGroup rels := by
      intro x
      if x1 : x = 1 then
        exact 1
      else if x2 : x = c[1, 2, 3] then
        exact a'
      else if x3 : x = c[1, 2] then
        exact b'
      else if x4 : x = c[1, 3, 2] then
        exact a' * a'
      else if x5 : x = c[2, 3] then
        exact b' * a'
      else if x6 : x = c[1, 3] then
        exact b' * a' * a'
      else
        absurd x6
        rcases elemsperm x with hx | hx | hx | hx | hx | hx
        contradiction
        contradiction
        contradiction
        contradiction
        contradiction
        exact hx
    -- prove that g is an inverse of tof
    use g
    -- tof a' = c[1, 2, 3]
    have fa : tof a' = c[1, 2, 3] := by exact rfl
    -- tof b' = c[1, 2]
    have fb : tof b' = c[1, 2] := by exact rfl
    -- tof (a' * a') = c[1, 3, 2]
    have faa : tof (a' * a') = c[1, 3, 2] := by
      rw [map_mul, fa]
      ext i
      fin_cases i
      exact rfl
      exact rfl
      exact rfl
    -- tof (b' * a') = c[2, 3]
    have fba : tof (b' * a') = c[2, 3] := by
      rw [map_mul, fa, fb]
      ext i
      fin_cases i
      exact rfl
      exact rfl
      exact rfl
    -- tof (b' * a' * a') = c[1, 3]
    have fbaa : tof (b' * a' * a') = c[1, 3] := by
      rw [map_mul, fba, fa]
      ext i
      fin_cases i
      exact rfl
      exact rfl
      exact rfl
    constructor
    · -- g is a left inverse of tof
      intro x
      -- g (tof x) = x for all x in H = {1, a', b', a' * a', b' * a', b' * a' * a'}
      rcases elemspre x with hx | hx | hx | hx | hx | hx
      -- x = 1
      simp only [Fin.isValue, Cycle.formPerm_coe, List.formPerm_cons_cons, List.formPerm_singleton, mul_one, hx, map_one, ↓reduceDIte, g, tof]
      -- x = a'
      rw [hx, fa]
      exact rfl
      -- x = b'
      rw [hx, fb]
      exact rfl
      -- x = a' * a'
      rw [hx, faa]
      exact rfl
      -- x = b' * a'
      rw [hx, fba]
      exact rfl
      -- x = b' * a' * a'
      rw [hx, fbaa]
      exact rfl
    · -- g is a right inverse of tof
      intro x
      rcases elemsperm x with hx | hx | hx | hx | hx | hx
      -- x = 1
      rw [hx]
      exact rfl
      -- x = c[1, 2, 3]
      rw [hx]
      exact rfl
      -- x = c[1, 2]
      rw [hx]
      exact rfl
      -- x = c[1, 3, 2]
      have gaa : g c[1, 3, 2] = a' * a' := by exact rfl
      rw [hx, gaa, faa]
      -- x = c[2, 3]
      have gba : g c[2, 3] = b' * a' := by exact rfl
      rw [hx, gba, fba]
      -- x = c[1, 3]
      have gbaa : g c[1, 3] = b' * a' * a' := by exact rfl
      rw [hx, gbaa, fbaa]
  -- construct an equivalence equiv : PresentedGroup rels ≃ Perm (Fin 3) using tof
  let equiv : PresentedGroup rels ≃ Perm (Fin 3) := by
    exact ofBijective (⇑tof) bij_tof
  -- prove that equiv is a group isomorphism
  refine MulEquiv.mk' equiv ?_
  intro x y
  -- tof (x * y) = tof x * tof y for all x, y in H
  show tof (x * y) = tof x * tof y
  exact MonoidHom.map_mul tof x y
","formalStatement":null,"suggestion":null,"comment":"<p>这里Step1我先证明了所有的6阶非交换群一定是同构于S_3的，Step2证明了在同构意义下6阶非交换群可以表示为题目所述的定义关系。</p>"},"judgement":{"result":"resubmit","score":5,"suggestion":"<p>提交的答案不能通过</p><p><br></p><p><span style=\"color: rgb(86, 156, 214);\">#lint</span><span style=\"color: rgb(204, 204, 204);\"> docBlameThm</span>编译，需要修改。</p><pre style=\"text-align: start;\"><code>-- Found 10 errors in 27 declarations (plus 46 automatically generated ones) in the current file with 16 linters
/- The `docBlameThm` linter reports:
THEOREMS ARE MISSING DOCUMENTATION STRINGS: -/
#check @aneone /- theorem missing documentation string -/
#check @bneone /- theorem missing documentation string -/
#check @aneb /- theorem missing documentation string -/
#check @aneab /- theorem missing documentation string -/
#check @aneba /- theorem missing documentation string -/
#check @bneab /- theorem missing documentation string -/
#check @bneba /- theorem missing documentation string -/
#check @abneone /- theorem missing documentation string -/
#check @baneone /- theorem missing documentation string -/
#check @abneba /- theorem missing documentation string -/</code></pre><p><br></p>","feedbackAction":"resubmit","comment":""},"stepInfo":null,"userInfo":{"id":420,"username":"nizixi","nickname":"Move fast","avatar":"//p1-arco.byteimg.com/tos-cn-i-uwbnlip3yd/a8c8cdb109cb051163646151a4a5083b.png~tplv-uwbnlip3yd-webp.webp","email":"821345763@qq.com"},"judgeUserInfo":{"id":351,"username":"Yuxintao","nickname":"Yuxintao","avatar":"//p1-arco.byteimg.com/tos-cn-i-uwbnlip3yd/a8c8cdb109cb051163646151a4a5083b.png~tplv-uwbnlip3yd-webp.webp","email":"1472388812@qq.com"}},{"created":"2025-05-23 14:47:00","updated":"2025-05-23 16:07:15","id":9137,"questionId":3277,"taskId":2510,"jobId":7007,"userId":420,"judgeUserId":351,"answer":{"informalProof":null,"formalProof":"import Mathlib
import Mathlib.Tactic
import Mathlib.Data.Fintype.Basic
import Mathlib.GroupTheory.Perm.Cycle.Concrete
import Mathlib.GroupTheory.Perm.Subgroup

set_option maxHeartbeats 0
open Equiv
open Function
open Equiv Function
/- **Step 1**If G is a nonabelian group of order 6, prove that G ≃ S₃ -/
/-- A useful lemma-/
lemma eqtwoofne (n : Fin 3) : n ≠ 0 → n ≠ 1 → n = 2 := by
  intro n0 n1
  fin_omega
/-- A useful lemma-/
lemma eqsixofne (n : Fin 7) : n ≠ 0 → n ≠ 1 → n ≠ 2 → n ≠ 3 → n ≠ 4 → n ≠ 5 → n = 6 := by
  intro n0 n1 n2 n3 n4 n5
  fin_omega
variable {G : Type*} [Group G] [Fintype G] {hcard : Fintype.card G = 6} {a b : G} {hab : a * b ≠ b * a}
-- the following tedious arguments are to show that 1, a, b, ab, ba are five distinct elements of G,
-- and except them there is only one element left.
omit [Fintype G] in 
/--a≠ 1-/
theorem aneone (hab : a * b ≠ b * a) : a ≠ 1 := by
    by_contra aeqone
    rw [aeqone, mul_one, one_mul] at hab
    exact hab rfl
omit [Fintype G] in 
/-- b ≠ 1 -/
theorem bneone (hab : a * b ≠ b * a) : b ≠ 1 := by
    by_contra beqone
    rw [beqone, mul_one, one_mul] at hab
    exact hab rfl
omit [Fintype G] in 
/-- a ≠ b-/
theorem aneb (hab : a * b ≠ b * a) : a ≠ b := by
    by_contra aeqb
    rw [aeqb] at hab
    exact hab rfl
omit [Fintype G] in 
/-- a ≠ a * b-/
theorem aneab (hab : a * b ≠ b * a) : a ≠ a * b := by
    by_contra aeqab
    symm at aeqab
    apply mul_right_eq_self.mp at aeqab
    exact bneone hab aeqab
omit [Fintype G] in 
/-- a ≠ b * a-/
theorem aneba (hab : a * b ≠ b * a) : a ≠ b * a := by
    by_contra aeqba
    symm at aeqba
    apply mul_left_eq_self.mp at aeqba
    exact bneone hab aeqba
omit [Fintype G] in 
/-- b ≠ a * b-/
theorem bneab (hab : a * b ≠ b * a) : b ≠ a * b := by
    by_contra beqab
    symm at beqab
    apply mul_left_eq_self.mp at beqab
    exact aneone hab beqab
omit [Fintype G] in 
/-- b ≠ b * a-/
theorem bneba (hab : a * b ≠ b * a) : b ≠ b * a := by
    by_contra beqba
    symm at beqba
    apply mul_right_eq_self.mp at beqba
    exact aneone hab beqba
omit [Fintype G] in 
/-- a * b ≠ 1-/
theorem abneone (hab : a * b ≠ b * a) : a * b ≠ 1 := by
    by_contra abeqone
    have inv : a = b⁻¹ := by exact eq_inv_of_mul_eq_one_left abeqone
    rw [inv, mul_inv_cancel, inv_mul_cancel] at hab
    exact hab rfl
omit [Fintype G] in 
/-- b * a ≠ 1-/
theorem baneone (hab : a * b ≠ b * a) : b * a ≠ 1 := by
    by_contra baeqone
    have inv : a = b⁻¹ := by exact Eq.symm (DivisionMonoid.inv_eq_of_mul b a baeqone)
    rw [inv, mul_inv_cancel, inv_mul_cancel] at hab
    exact hab rfl
omit [Fintype G] in 
/-- a * b ≠ b * a -/
theorem abneba (hab : a * b ≠ b * a) : a * b ≠ b * a := hab

/-- for G and noncommutative pairs a, b, we first prove that if a²≠1 then G ≃* S₃ 
via map a ↦ c[1, 2, 3] and b ↦ c[1, 2],  then prove the same when both a²=b²=1. 
So first we introduce the following intermediate lemma-/
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

open Equiv Function
/-**Step 2**Prove that the presentation
\[
\left(a, b: a^{3}=1, b^{2}=1, b a=a^{2} b\right)
\]
gives (up to isomorphism) the only nonabelian group of order 6.-/
/- let a, b represent (123) and (12) respectively, and let rels be the relations {a ^ 3 = b ^ 2 = 1, a * b * a * b⁻¹ = 1}. We show that {a, b} generates S_3 and rels is the relation (that is, S_3 is presented by rels) -/
/-- define the elements a of the free group F₂ -/
def a1 := FreeGroup.mk [((0 : Fin 2), true)]
/-- define the element b of the free group F₂ -/
def b1 := FreeGroup.mk [((1 : Fin 2), true)]
/-- define rels, the relations of the presentation H -/
def rels : Set (FreeGroup (Fin 2)) := {a1 * a1 * a1, b1 * b1, a1 * b1 * a1 * (b1)⁻¹}

/-- define the elements a' of H -/
def a' : (PresentedGroup rels) := QuotientGroup.mk a1
/-- define the elements b' of H -/
def b' : (PresentedGroup rels) := QuotientGroup.mk b1
/-- a' * a' * a' = 1 in H -/
lemma eqapow : a' * a' * a' = 1 := by
  show QuotientGroup.mk (a1 * a1 * a1) = 1
  refine (QuotientGroup.eq_one_iff (a1 * a1 * a1)).mpr ?_
  -- a * a * a ∈ rels
  have ain : a1 * a1 * a1 ∈ rels := by
    left
    exact rfl
  have relsle : rels ≤ Subgroup.normalClosure rels := by refine Set.le_iff_subset.mpr ?_; exact Subgroup.subset_normalClosure
  exact relsle ain
/-- b' * b' = 1 in H -/
lemma eqbpow : b' * b' = 1 := by
  show QuotientGroup.mk (b1 * b1) = 1
  refine (QuotientGroup.eq_one_iff (b1 * b1)).mpr ?_
  -- b * b ∈ rels
  have bin : b1 * b1 ∈ rels := by
    right
    left
    exact rfl
  have relsle : rels ≤ Subgroup.normalClosure rels := by refine Set.le_iff_subset.mpr ?_; exact Subgroup.subset_normalClosure
  exact relsle bin
/-- a'⁻¹ = a' * a' in H -/
lemma eqainv : a'⁻¹ = a' * a' := by
  refine inv_eq_of_mul_eq_one_left ?h
  exact eqapow
/-- b⁻¹ '= b' -/
lemma eqbinv : b'⁻¹ = b' := by
  refine DivisionMonoid.inv_eq_of_mul b' b' ?_
  exact eqbpow
/-- a' * b' = b' * a' * a' -/
lemma eqab : a' * b' = b' * a' * a' := by
  have mid : a' * b' * a' * b'⁻¹ = 1 := by
    show QuotientGroup.mk (a1 * b1 * a1 * (b1)⁻¹) = 1
    refine (QuotientGroup.eq_one_iff (a1 * b1 * a1 * (b1)⁻¹)).mpr ?_
    -- a * b * a * b⁻¹ ∈ rels, so a' * b' * a' * b'⁻¹ = 1 in H
    have cin : a1 * b1 * a1 * (b1)⁻¹ ∈ rels := by
      right
      right
      exact rfl
    have relsle : rels ≤ Subgroup.normalClosure rels := by refine Set.le_iff_subset.mpr ?_; exact Subgroup.subset_normalClosure
    exact relsle cin
  -- by some algebraic manipulation, we can show that a' * b' = b' * a' * a'
  rw [← mul_one (a' * b'), ← eqapow, ← mul_assoc, ← mul_assoc, ← mul_one (a' * b' * a'), ← eqbpow, ← mul_assoc]
  nth_rw 2 [← eqbinv]
  rw [mid, one_mul]
/-- a' * a' * b' = b' * a' -/
lemma eqaab : a' * a' * b' = b' * a' := by
  rw [mul_assoc a', eqab, ← mul_assoc, ← mul_assoc, eqab, mul_assoc b', mul_assoc b', eqapow, mul_one]

/-- H has only six elements 1, a', b', a' * a', b' * a', b' * a' * a' -/
lemma elemspre : ∀ x : PresentedGroup rels, x ∈ ({1, a', b', a' * a', b' * a', b' * a' * a'} : Set (PresentedGroup rels)) := by
  intro _
  -- we prove that x ∈ {1, a', b', a' * a', b' * a', b' * a' * a'} by proving that for all z in F₂, z / ⟨rels⟩ ∈ {1, a', b', a' * a', b' * a', b' * a' * a'}
  apply QuotientGroup.induction_on
  intro _
  -- we prove that z / ⟨rels⟩ ∈ {1, a', b', a' * a', b' * a', b' * a' * a'} by free group induction
  apply @FreeGroup.induction_on (Fin 2) (fun y ↦ (QuotientGroup.mk y : PresentedGroup rels) ∈ ({1, a', b', a' * a', b' * a', b' * a' * a'} : Set (PresentedGroup rels))) _
  · -- base case: z = 1 ∈ {1, a', b', a' * a', b' * a', b' * a' * a'}
    exact Set.mem_insert 1 {a', b', a' * a', b' * a', b' * a' * a'}
  · -- base case: z = a ∈ {1, a', b', a' * a', b' * a', b' * a' * a'} or z = b ∈ {1, a', b', a' * a', b' * a', b' * a' * a'}
    intro i
    fin_cases i
    -- z = a
    right
    left
    exact rfl
    -- z = b
    right
    right
    left
    exact rfl
  · -- base case: z = a⁻¹ ∈ {1, a', b', a' * a', b' * a', b' * a' * a'} or z = b⁻¹ ∈ {1, a', b', a' * a', b' * a', b' * a' * a'}
    intro i hi
    fin_cases i
    -- z = a⁻¹
    right
    right
    right
    left
    exact eqainv
    -- z = b⁻¹
    right
    right
    left
    exact eqbinv
  · -- induction step: if x and y are in {1, a', b', a' * a', b' * a', b' * a' * a'}, then x * y is in {1, a', b', a' * a', b' * a', b' * a' * a'}
    intro x y xeq yeq
    have xyeq : @QuotientGroup.mk (FreeGroup (Fin 2)) FreeGroup.instGroup (Subgroup.normalClosure rels) (x * y) = (@QuotientGroup.mk (FreeGroup (Fin 2)) FreeGroup.instGroup (Subgroup.normalClosure rels) x) * (@QuotientGroup.mk (FreeGroup (Fin 2)) FreeGroup.instGroup (Subgroup.normalClosure rels) y) := by exact rfl
    rcases xeq with xeq | xeq | xeq | xeq | xeq | xeq
    · -- x = 1
      rw [xyeq, xeq, one_mul]
      exact yeq
    · -- x = a'
      rcases yeq with yeq | yeq | yeq | yeq | yeq | yeq
      · -- y = 1
        rw [xyeq, xeq, yeq, mul_one]
        right
        left
        exact rfl
      · -- y = a'
        rw [xyeq, xeq, yeq]
        right
        right
        right
        left
        exact rfl
      · -- y = b'
        rw [xyeq, xeq, yeq, eqab]
        right
        right
        right
        right
        right
        exact rfl
      · -- y = a' * a'
        rw [xyeq, xeq, yeq, ← mul_assoc, eqapow]
        exact Set.mem_insert 1 {a', b', a' * a', b' * a', b' * a' * a'}
      · -- y = b' * a'
        rw [xyeq, xeq, yeq, ← mul_assoc, eqab, mul_assoc, mul_assoc, eqapow, mul_one]
        right
        right
        left
        exact rfl
      · -- y = b' * a' * a'
        rw [xyeq, xeq, yeq, ← mul_assoc, ← mul_assoc, eqab, mul_assoc (b' * a'), mul_assoc (b' * a'), eqapow, mul_one]
        right
        right
        right
        right
        left
        exact rfl
    · -- x = b'
      rcases yeq with yeq | yeq | yeq | yeq | yeq | yeq
      · -- y = 1
        rw [xyeq, xeq, yeq, mul_one]
        right
        right
        left
        exact rfl
      · -- y = a'
        rw [xyeq, xeq, yeq]
        right
        right
        right
        right
        left
        exact rfl
      · -- y = b'
        rw [xyeq, xeq, yeq, eqbpow]
        exact Set.mem_insert 1 {a', b', a' * a', b' * a', b' * a' * a'}
      · -- y = a' * a'
        rw [xyeq, xeq, yeq, ← mul_assoc]
        right
        right
        right
        right
        right
        exact rfl
      · -- y = b' * a'
        rw [xyeq, xeq, yeq, ← mul_assoc, eqbpow, one_mul]
        right
        exact Set.mem_insert a' {b', a' * a', b' * a', b' * a' * a'}
      · -- y = b' * a' * a'
        rw [xyeq, xeq, yeq, ← mul_assoc, ← mul_assoc, eqbpow, one_mul]
        right
        right
        right
        exact Set.mem_insert (a' * a') {b' * a', b' * a' * a'}
    · -- x = a' * a'
      rcases yeq with yeq | yeq | yeq | yeq | yeq | yeq
      · -- y = 1
        rw [xyeq, xeq, yeq, mul_one]
        right
        right
        right
        exact Set.mem_insert (a' * a') {b' * a', b' * a' * a'}
      · -- y = a'
        rw [xyeq, xeq, yeq, eqapow]
        exact Set.mem_insert 1 {a', b', a' * a', b' * a', b' * a' * a'}
      · -- y = b'
        rw [xyeq, xeq, yeq, eqaab]
        right
        right
        right
        right
        exact Set.mem_insert (b' * a') {b' * (a' * a')}
      · -- y = a' * a'
        rw [xyeq, xeq, yeq, ← mul_assoc, eqapow, one_mul]
        right
        exact Set.mem_insert a' {b', a' * a', b' * a', b' * a' * a'}
      · -- y = b' * a'
        rw [xyeq, xeq, yeq, ← mul_assoc, eqaab]
        right
        right
        right
        right
        right
        exact rfl
      · -- y = b' * a' * a'
        rw [xyeq, xeq, yeq, ← mul_assoc, ← mul_assoc, eqaab, mul_assoc, mul_assoc, eqapow, mul_one]
        right
        right
        exact Set.mem_insert b' {a' * a', b' * a', b' * (a' * a')}
    · -- x = b' * a'
      rcases yeq with yeq | yeq | yeq | yeq | yeq | yeq
      · -- y = 1
        rw [xyeq, xeq, yeq, mul_one]
        right
        right
        right
        right
        exact Set.mem_insert (b' * a') {b' * a' * a'}
      · -- y = a'
        rw [xyeq, xeq, yeq]
        right
        right
        right
        right
        right
        exact rfl
      · -- y = b'
        rw [xyeq, xeq, yeq, mul_assoc b' a' b', eqab, ← mul_assoc, ← mul_assoc, eqbpow, one_mul]
        right
        right
        right
        exact Set.mem_insert (a' * a') {b' * a', b' * a' * a'}
      · -- y = a' * a'
        rw [xyeq, xeq, yeq, mul_assoc b' a' (a' * a'), ← mul_assoc a', eqapow, mul_one]
        right
        right
        exact Set.mem_insert b' {a' * a', b' * a', b' * a' * a'}
      · -- y = b' * a'
        rw [xyeq, xeq, yeq, ← mul_assoc, mul_assoc b' a' b', eqab, ← mul_assoc, ← mul_assoc, eqbpow, one_mul, eqapow]
        exact Set.mem_insert 1 {a', b', a' * a', b' * a', b' * a' * a'}
      · -- y = b' * a' * a'
        rw [xyeq, xeq, yeq, ← mul_assoc, ← mul_assoc, mul_assoc b' a' b', eqab, ← mul_assoc, ← mul_assoc, eqbpow, one_mul, eqapow, one_mul]
        right
        exact Set.mem_insert a' {b', a' * a', b' * a', b' * a' * a'}
    · -- x = b' * a' * a'
      rcases yeq with yeq | yeq | yeq | yeq | yeq | yeq
      · -- y = 1
        rw [xyeq, xeq, yeq, mul_one]
        right
        right
        right
        right
        right
        exact rfl
      · -- y = a'
        rw [xyeq, xeq, yeq, mul_assoc, mul_assoc, eqapow, mul_one]
        right
        right
        exact Set.mem_insert b' {a' * a', b' * a', b' * (a' * a')}
      · -- y = b'
        rw [xyeq, xeq, yeq, mul_assoc, mul_assoc, eqaab, ← mul_assoc b' b', eqbpow, one_mul]
        right
        exact Set.mem_insert a' {b', a' * a', b' * a', b' * (a' * a')}
      · -- y = a' * a'
        rw [xyeq, xeq, yeq, ← mul_assoc, mul_assoc, mul_assoc b', eqapow, mul_one]
        right
        right
        right
        right
        exact Set.mem_insert (b' * a') {b' * (a' * a')}
      · -- y = b' * a'
        rw [xyeq, xeq, yeq, ← mul_assoc, mul_assoc, mul_assoc b', eqaab, ← mul_assoc b' b', eqbpow, one_mul]
        right
        right
        right
        exact Set.mem_insert (a' * a') {b' * a', b' * (a' * a')}
      · -- y = b' * a' * a'
        rw [xyeq, xeq, yeq, ← mul_assoc, ← mul_assoc, mul_assoc b', mul_assoc b', eqaab, ← mul_assoc, ← mul_assoc, eqbpow, one_mul, eqapow]
        exact Set.mem_insert 1 {a', b', a' * a', b' * a', b' * a' * a'}

/-- Perm (Fin 3) has only six elements 1, c[1, 2, 3], c[1, 2], c[1, 3, 2], c[2, 3], c[1, 3] -/
lemma elemsperm : ∀ x : Perm (Fin 3), x ∈ ({1, c[1, 2, 3], c[1, 2], c[1, 3, 2], c[2, 3], c[1, 3]} : Set (Perm (Fin 3))) := by
  -- the cardinality of Perm (Fin 3) is 6
  have : Fintype.card (Perm (Fin 3)) = 6 := by
    exact rfl
  -- define f : Fin 6 → Perm (Fin 3) by f 0 = 1, f 1 = c[1, 2, 3], f 2 = c[1, 2], f 3 = c[1, 3, 2], f 4 = c[2, 3], f 5 = c[1, 3]
  let f : Fin 6 → Perm (Fin 3) := ![1, c[1, 2, 3], c[1, 2], c[1, 3, 2], c[2, 3], c[1, 3]]
  -- f is injective
  have inj_f : Injective f := by
    intro x y hxy
    -- we prove that f x = f y → x = y for:
    fin_cases x
    · -- x = 0
      fin_cases y
      -- y = 0
      exact rfl
      -- y = 1
      have : (1 : Perm (Fin 3)) ≠ c[1, 2, 3] := by
        exact ne_of_beq_false rfl
      contradiction
      -- y = 2
      have : (1 : Perm (Fin 3)) ≠ c[1, 2] := by
        exact ne_of_beq_false rfl
      contradiction
      -- y = 3
      have : (1 : Perm (Fin 3)) ≠ c[1, 3, 2] := by
        exact ne_of_beq_false rfl
      contradiction
      -- y = 4
      have : (1 : Perm (Fin 3)) ≠ c[2, 3] := by
        exact ne_of_beq_false rfl
      contradiction
      -- y = 5
      have : (1 : Perm (Fin 3)) ≠ c[1, 3] := by
        exact ne_of_beq_false rfl
      contradiction
    · -- x = 1
      fin_cases y
      -- y = 0
      have : (c[1, 2, 3] : Perm (Fin 3)) ≠ 1 := by
        exact ne_of_beq_false rfl
      contradiction
      -- y = 1
      exact rfl
      -- y = 2
      have : (c[1, 2, 3] : Perm (Fin 3)) ≠ c[1, 2] := by
        exact ne_of_beq_false rfl
      contradiction
      -- y = 3
      have : (c[1, 2, 3] : Perm (Fin 3)) ≠ c[1, 3, 2] := by
        exact ne_of_beq_false rfl
      contradiction
      -- y = 4
      have : (c[1, 2, 3] : Perm (Fin 3)) ≠ c[2, 3] := by
        exact ne_of_beq_false rfl
      contradiction
      -- y = 5
      have : (c[1, 2, 3] : Perm (Fin 3)) ≠ c[1, 3] := by
        exact ne_of_beq_false rfl
      contradiction
    · -- x = 2
      fin_cases y
      -- y = 0
      have : (c[1, 2] : Perm (Fin 3)) ≠ 1 := by
        exact ne_of_beq_false rfl
      contradiction
      -- y = 1
      have : (c[1, 2] : Perm (Fin 3)) ≠ c[1, 2, 3] := by
        exact ne_of_beq_false rfl
      contradiction
      -- y = 2
      exact rfl
      -- y = 3
      have : (c[1, 2] : Perm (Fin 3)) ≠ c[1, 3, 2] := by
        exact ne_of_beq_false rfl
      contradiction
      -- y = 4
      have : (c[1, 2] : Perm (Fin 3)) ≠ c[2, 3] := by
        exact ne_of_beq_false rfl
      contradiction
      -- y = 5
      have : (c[1, 2] : Perm (Fin 3)) ≠ c[1, 3] := by
        exact ne_of_beq_false rfl
      contradiction
    · -- x = 3
      fin_cases y
      -- y = 0
      have : (c[1, 3, 2] : Perm (Fin 3)) ≠ 1 := by
        exact ne_of_beq_false rfl
      contradiction
      -- y = 1
      have : (c[1, 3, 2] : Perm (Fin 3)) ≠ c[1, 2, 3] := by
        exact ne_of_beq_false rfl
      contradiction
      -- y = 2
      have : (c[1, 3, 2] : Perm (Fin 3)) ≠ c[1, 2] := by
        exact ne_of_beq_false rfl
      contradiction
      -- y = 3
      exact rfl
      -- y = 4
      have : (c[1, 3, 2] : Perm (Fin 3)) ≠ c[2, 3] := by
        exact ne_of_beq_false rfl
      contradiction
      -- y = 5
      have : (c[1, 3, 2] : Perm (Fin 3)) ≠ c[1, 3] := by
        exact ne_of_beq_false rfl
      contradiction
    · -- x = 4
      fin_cases y
      -- y = 0
      have : (c[2, 3] : Perm (Fin 3)) ≠ 1 := by
        exact ne_of_beq_false rfl
      contradiction
      -- y = 1
      have : (c[2, 3] : Perm (Fin 3)) ≠ c[1, 2, 3] := by
        exact ne_of_beq_false rfl
      contradiction
      -- y = 2
      have : (c[2, 3] : Perm (Fin 3)) ≠ c[1, 2] := by
        exact ne_of_beq_false rfl
      contradiction
      -- y = 3
      have : (c[2, 3] : Perm (Fin 3)) ≠ c[1, 3, 2] := by
        exact ne_of_beq_false rfl
      contradiction
      -- y = 4
      exact rfl
      -- y = 5
      have : (c[2, 3] : Perm (Fin 3)) ≠ c[1, 3] := by
        exact ne_of_beq_false rfl
      contradiction
    · -- x = 5
      fin_cases y
      -- y = 0
      have : (c[1, 3] : Perm (Fin 3)) ≠ 1 := by
        exact ne_of_beq_false rfl
      contradiction
      -- y = 1
      have : (c[1, 3] : Perm (Fin 3)) ≠ c[1, 2, 3] := by
        exact ne_of_beq_false rfl
      contradiction
      -- y = 2
      have : (c[1, 3] : Perm (Fin 3)) ≠ c[1, 2] := by
        exact ne_of_beq_false rfl
      contradiction
      -- y = 3
      have : (c[1, 3] : Perm (Fin 3)) ≠ c[1, 3, 2] := by
        exact ne_of_beq_false rfl
      contradiction
      -- y = 4
      have : (c[1, 3] : Perm (Fin 3)) ≠ c[2, 3] := by
        exact ne_of_beq_false rfl
      contradiction
      -- y = 5
      exact rfl
  -- there is a bijection equiv between Fin 6 and Perm (Fin 3)
  have equiv : Fin 6 ≃ Perm (Fin 3) := by exact (Fintype.equivFinOfCardEq this).symm
  -- f is surjective
  have surj_f : Surjective f := by exact Injective.surjective_of_fintype equiv inj_f
  -- for all x in Perm (Fin 3), x ∈ {1, c[1, 2, 3], c[1, 2], c[1, 3, 2], c[2, 3], c[1, 3]}
  intro x
  -- there exists i in Fin 6 such that f i = x
  rcases surj_f x with ⟨i, hi⟩
  fin_cases i
  -- if i = 0, then x = 1
  have : x = 1 := by exact id (Eq.symm hi)
  left
  exact this
  -- if i = 1, then x = c[1, 2, 3]
  have : x = c[1, 2, 3] := by exact id (Eq.symm hi)
  right
  left
  exact this
  -- if i = 2, then x = c[1, 2]
  have : x = c[1, 2] := by exact id (Eq.symm hi)
  right
  right
  left
  exact this
  -- if i = 3, then x = c[1, 3, 2]
  have : x = c[1, 3, 2] := by exact id (Eq.symm hi)
  right
  right
  right
  left
  exact this
  -- if i = 4, then x = c[2, 3]
  have : x = c[2, 3] := by exact id (Eq.symm hi)
  right
  right
  right
  right
  left
  exact this
  -- if i = 5, then x = c[1, 3]
  have : x = c[1, 3] := by exact id (Eq.symm hi)
  right
  right
  right
  right
  right
  exact this

/-- now we prove that H ≃* S₃ -/
noncomputable def presentation : PresentedGroup rels ≃* Perm (Fin 3) := by
  -- define group morphism tof : PresentedGroup rels →* Perm (Fin 3) as the lift of FreeGroup (Fin 2) →* Perm (Fin 3), where we need to verify that rels is in the kernel of the latter map
  let tof : PresentedGroup rels →* Perm (Fin 3) := by
    -- let lifttof : FreeGroup (Fin 2) →* Perm (Fin 3) be induced by gnrttof : Fin 2 → Perm (Fin 3) that sends 0 to c[1, 2, 3] and 1 to c[1, 2]
    let lifttof : FreeGroup (Fin 2) →* Perm (Fin 3) := by
      -- define gnrttof : Fin 2 → Perm (Fin 3) by gnrttof 0 = c[1, 2, 3] and gnrttof 1 = c[1, 2]
      let gnrttof : (Fin 2) → Perm (Fin 3) := ![c[(1 : Fin 3), 2, 3], c[1, 2]]
      exact FreeGroup.lift gnrttof
    -- prove that the normal closure of rels is in the kernel of lifttof
    have Nleker : Subgroup.normalClosure rels ≤ lifttof.ker := by
      -- suffices to prove that rels is in the kernel of lifttof
      apply Subgroup.normalClosure_subset_iff.mp
      intro g gin
      -- suffices to prove that lifttof g = 1 for all g in rels
      apply MonoidHom.mem_ker.mpr
      rcases gin with geq | geq | geq
      · -- if g = a * a * a, then lifttof g = 1
        simp only [Fin.isValue, Cycle.formPerm_coe, List.formPerm_cons_cons, List.formPerm_singleton, mul_one, geq, map_mul, lifttof]
        -- suffices to show c[1, 2, 3] * c[1, 2, 3] * c[1, 2, 3] = 1
        show c[(1 : Fin 3), 2, 3] * c[(1 : Fin 3), 2, 3] * c[(1 : Fin 3), 2, 3] = 1
        rw [mul_assoc, ← pow_three]
        have threecycle : Perm.IsThreeCycle c[(1 : Fin 3), 2, 3] := by 
          exact card_support_eq_three_iff.mp rfl
        apply Perm.IsThreeCycle.orderOf at threecycle
        rw [← pow_orderOf_eq_one c[(1 : Fin 3), 2, 3]]
        rw [threecycle]
      · -- if g = b * b, then lifttof g = 1
        simp only [Fin.isValue, Cycle.formPerm_coe, List.formPerm_cons_cons, List.formPerm_singleton, mul_one, geq, map_mul, lifttof]
        -- suffices to show c[1, 2] * c[1, 2] = 1
        show c[(1 : Fin 3), 2] * c[(1 : Fin 3), 2] = 1
        refine Perm.support_eq_empty_iff.mp ?_
        exact rfl
      · -- if g = a * b * a * b⁻¹, then lifttof g = 1
        rw [Set.mem_singleton_iff] at geq
        simp only [Fin.isValue, Cycle.formPerm_coe, List.formPerm_cons_cons, List.formPerm_singleton, mul_one, geq, map_mul, lifttof]
        -- suffices to show c[1, 2, 3] * c[1, 2] * c[1, 2, 3] * c[1, 2]⁻¹ = 1
        show c[(1 : Fin 3), 2, 3] * c[(1 : Fin 3), 2] * c[(1 : Fin 3), 2, 3] * c[(1 : Fin 3), 2]⁻¹ = 1
        ext i
        fin_cases i
        simp only [Fin.isValue, Cycle.formPerm_coe, List.formPerm_cons_cons, List.formPerm_singleton, mul_one, swap_inv, Fin.zero_eta, Perm.coe_mul, comp_apply, swap_apply_self, Fin.val_zero, Perm.coe_one, id_eq]
        simp only [Fin.isValue, Cycle.formPerm_coe, List.formPerm_cons_cons, List.formPerm_singleton, mul_one, swap_inv, Fin.zero_eta, Perm.coe_mul, comp_apply, swap_apply_self, Fin.val_zero, Perm.coe_one, id_eq]
        simp only [Fin.isValue, Cycle.formPerm_coe, List.formPerm_cons_cons, List.formPerm_singleton, mul_one, swap_inv, Fin.zero_eta, Perm.coe_mul, comp_apply, swap_apply_self, Fin.val_zero, Perm.coe_one, id_eq]
    -- since rels is in the normal closure of rels, gnrttof induces the group morphism lifttof : H →* Perm (Fin 3)
    exact QuotientGroup.lift (Subgroup.normalClosure rels) lifttof Nleker
  -- prove that tof is bijective, so that PresentedGroup rels ≃* Perm (Fin 3). define g as the inverse of tof
  have bij_tof : Bijective tof := by
    -- suffices to prove that tof has an inverse
    refine bijective_iff_has_inverse.mpr ?_
    -- define g : Perm (Fin 3) → PresentedGroup rels by g c[1, 2, 3] = a', g c[1, 2] = b', g c[1, 3, 2] = a' * a', g c[2, 3] = b' * a', g c[1, 3] = b' * a' * a'
    let g : Perm (Fin 3) → PresentedGroup rels := by
      intro x
      if x1 : x = 1 then
        exact 1
      else if x2 : x = c[1, 2, 3] then
        exact a'
      else if x3 : x = c[1, 2] then
        exact b'
      else if x4 : x = c[1, 3, 2] then
        exact a' * a'
      else if x5 : x = c[2, 3] then
        exact b' * a'
      else if x6 : x = c[1, 3] then
        exact b' * a' * a'
      else
        absurd x6
        rcases elemsperm x with hx | hx | hx | hx | hx | hx
        contradiction
        contradiction
        contradiction
        contradiction
        contradiction
        exact hx
    -- prove that g is an inverse of tof
    use g
    -- tof a' = c[1, 2, 3]
    have fa : tof a' = c[1, 2, 3] := by exact rfl
    -- tof b' = c[1, 2]
    have fb : tof b' = c[1, 2] := by exact rfl
    -- tof (a' * a') = c[1, 3, 2]
    have faa : tof (a' * a') = c[1, 3, 2] := by
      rw [map_mul, fa]
      ext i
      fin_cases i
      exact rfl
      exact rfl
      exact rfl
    -- tof (b' * a') = c[2, 3]
    have fba : tof (b' * a') = c[2, 3] := by
      rw [map_mul, fa, fb]
      ext i
      fin_cases i
      exact rfl
      exact rfl
      exact rfl
    -- tof (b' * a' * a') = c[1, 3]
    have fbaa : tof (b' * a' * a') = c[1, 3] := by
      rw [map_mul, fba, fa]
      ext i
      fin_cases i
      exact rfl
      exact rfl
      exact rfl
    constructor
    · -- g is a left inverse of tof
      intro x
      -- g (tof x) = x for all x in H = {1, a', b', a' * a', b' * a', b' * a' * a'}
      rcases elemspre x with hx | hx | hx | hx | hx | hx
      -- x = 1
      simp only [Fin.isValue, Cycle.formPerm_coe, List.formPerm_cons_cons, List.formPerm_singleton, mul_one, hx, map_one, ↓reduceDIte, g, tof]
      -- x = a'
      rw [hx, fa]
      exact rfl
      -- x = b'
      rw [hx, fb]
      exact rfl
      -- x = a' * a'
      rw [hx, faa]
      exact rfl
      -- x = b' * a'
      rw [hx, fba]
      exact rfl
      -- x = b' * a' * a'
      rw [hx, fbaa]
      exact rfl
    · -- g is a right inverse of tof
      intro x
      rcases elemsperm x with hx | hx | hx | hx | hx | hx
      -- x = 1
      rw [hx]
      exact rfl
      -- x = c[1, 2, 3]
      rw [hx]
      exact rfl
      -- x = c[1, 2]
      rw [hx]
      exact rfl
      -- x = c[1, 3, 2]
      have gaa : g c[1, 3, 2] = a' * a' := by exact rfl
      rw [hx, gaa, faa]
      -- x = c[2, 3]
      have gba : g c[2, 3] = b' * a' := by exact rfl
      rw [hx, gba, fba]
      -- x = c[1, 3]
      have gbaa : g c[1, 3] = b' * a' * a' := by exact rfl
      rw [hx, gbaa, fbaa]
  -- construct an equivalence equiv : PresentedGroup rels ≃ Perm (Fin 3) using tof
  let equiv : PresentedGroup rels ≃ Perm (Fin 3) := by
    exact ofBijective (⇑tof) bij_tof
  -- prove that equiv is a group isomorphism
  refine MulEquiv.mk' equiv ?_
  intro x y
  -- tof (x * y) = tof x * tof y for all x, y in H
  show tof (x * y) = tof x * tof y
  exact MonoidHom.map_mul tof x y","formalStatement":null,"suggestion":null,"comment":"<p>这里Step1我先证明了所有的6阶非交换群一定是同构于S_3的，Step2证明了在同构意义下6阶非交换群可以表示为题目所述的定义关系。</p><p>已增加未注释部分</p>"},"judgement":{"result":"done","score":5,"suggestion":"<p>证明通顺，逻辑严密，完全正确，再接再厉！</p>","feedbackAction":"done","comment":null},"stepInfo":null,"userInfo":{"id":420,"username":"nizixi","nickname":"Move fast","avatar":"//p1-arco.byteimg.com/tos-cn-i-uwbnlip3yd/a8c8cdb109cb051163646151a4a5083b.png~tplv-uwbnlip3yd-webp.webp","email":"821345763@qq.com"},"judgeUserInfo":{"id":351,"username":"Yuxintao","nickname":"Yuxintao","avatar":"//p1-arco.byteimg.com/tos-cn-i-uwbnlip3yd/a8c8cdb109cb051163646151a4a5083b.png~tplv-uwbnlip3yd-webp.webp","email":"1472388812@qq.com"}}]},"errorCode":0
-/
