import Mathlib
/-! Question:
4. If $n=2 k$ is even and $n \geq 4$, show that $z=r^{k}$ is an element of order 2 which commutes with all elements of $D_{2 n}$. Show also that $z$ is the only nonidentity element of $D_{2 n}$ which commutes with all elements of $D_{2 n}$. 
-/
/--
  $r^k$ is the only nontrival element in center of $D_{2 k}$ if $k \ge 2$
-/
theorem center_of_D_2k_if_k_ge_2 (k : ℕ) (hk : k ≥ 2) :
    (Subgroup.center (DihedralGroup (2 * k)) : Set (DihedralGroup (2 * k))) = {1, (DihedralGroup.r k)} := by
  -- discuss the element in center of $D_{2 k}$
  ext x
  simp [Subgroup.mem_center_iff]
  letI : NeZero k := by exact NeZero.of_gt hk
  letI : NeZero (2 * k) := by
    apply NeZero.mul
  constructor
  · intro h
    -- show that only $1, r^k$ are in the center
    match x with
    | DihedralGroup.r s =>
      -- use $s$ in the commutation condition
      specialize h (DihedralGroup.sr 1)
      simp at h
      rw [show 1 = DihedralGroup.r 0 from rfl]
      simp
      apply eq_sub_of_add_eq' at h
      simp at h
      symm at h
      rw [ZMod.neg_eq_self_iff] at h
      simp at h
      rw [show s.val = k <-> s = k by
          nth_rw 2 [show k = (k : ZMod (2 * k)).val by refine Eq.symm (ZMod.val_natCast_of_lt (by omega))]
          -- do some boring transformation about ZMod
          convert Function.Injective.eq_iff (f := ZMod.val (n := 2 * k)) (I := by
            apply ZMod.val_injective (2 * k)
            )
      ] at h
      exact h
    | DihedralGroup.sr s =>
      -- use $r$ in the commutation condition
      specialize h (DihedralGroup.r 1)
      simp at h
      -- h already gives contradiction
      apply eq_add_of_sub_eq at h
      ring_nf at h
      symm at h
      apply eq_sub_of_add_eq at h
      simp at h
      -- it' s terrible that Lean automatically use `ofNat` for literal but `natCast` for a variable. At the same time, all lemmas are related to `natCast`
      have : (Nat.cast 2 : ZMod (2 * k)) = (Nat.cast 0) := by
        convert h
        simp
      rw [ZMod.natCast_eq_natCast_iff'] at this
      -- finally we need to get 2 <= 2 * k, which gives contradiction
      simp at this
      have := Nat.le_of_mod_lt (by
        rw [this]
        omega
      )
      omega
  · -- the other direction is simple. just let lean to verify it
    intro h g
    apply DihedralGroup.casesOn (motive := fun g => g * x = x * g) <;> rcases h with h | h <;> simp [h]
    -- again we need to manually prove equality of ZMod
    · intro a
      rw [add_comm]
    · intro a
      apply eq_sub_of_add_eq
      rw [add_assoc]
      simp
      norm_cast -- move casts using `norm_cast`
      rw [show k + k = 2 * k by exact Eq.symm (Nat.two_mul k)]
      exact ZMod.natCast_self (2 * k)

