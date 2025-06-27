import Mathlib
/-! Question:
设 G 为 $Z$ 或 $Z_m(m>=2)$，证明 $G$ 上的自同态环与 $G$ 同构。
-/

-- To show that the endomorphism ring on $G$ is isomorphic to $G$, we construct specific mappings that identify each endomorphism with a single element of $G$​.

-- For any endomorphism $f$ on $\Z$, we have $f (n) = n \cdot f(1)$.
lemma l_z_end_apply (f : AddMonoid.End ℤ) : ∀ n, f n = n * f 1 := by
  unfold AddMonoid.End at f
  apply AddMonoidHom.apply_int

-- aux lemma for l_zmod_end_apply, to convert the induction to be apply in ℕ rather than ZMod m
lemma l_zmod_end_apply_aux [NeZero m] (p : ZMod m → Prop) : (∀ n : ℕ, p n) → (∀ n : ZMod m, p n) := by
  intro h n
  convert h n.val
  rw [eq_comm, ZMod.natCast_zmod_val]

-- For any endomorphism $f$ on  $\Z_m$, we have $f (n) = n \cdot f(1)$.
lemma l_zmod_end_apply [NeZero m] (f : AddMonoid.End (ZMod m)) : ∀ n, f n = n * f 1 := by
  apply l_zmod_end_apply_aux
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    simp [add_mul, ih]


-- for G = ℤ
example : AddMonoid.End ℤ ≃+* ℤ where

  -- We can map each endomorphism $f$ to the element $f(1)$ in $G$.
  toFun f := f 1

  -- Conversely, given an element $n$ in $G$, we construct an endomorphism $f$ where $f (x) = n \cdot x$.
  invFun n := {
    toFun := fun x => n * x
    map_zero' := by simp
    map_add' := by intros; ring }

  -- verify that these mappings are inverses of each other
  left_inv f := by
    unfold AddMonoid.End
    ext
    simp

  right_inv n := by
    unfold AddMonoid.End
    simp

  -- verify that these mappings preserve addition and multiplication
  map_mul' f g := by
    simp [l_z_end_apply f (g 1), mul_comm]

  map_add' f g := by
    simp
    rfl


-- for G = ℤₘ
example (m : ℕ) (hm : 2 ≤ m) : AddMonoid.End (ZMod m) ≃+* (ZMod m) where

  -- We can map each endomorphism $f$ to the element $f(1)$ in $G$.
  toFun f := f 1

  -- Conversely, given an element $n$ in $G$, we construct an endomorphism $f$ where $f (x) = n \cdot x$.
  invFun n := {
    toFun := fun x => x * n
    map_zero' := by simp
    map_add' := by intros; ring }

  -- verify that these mappings are inverses of each other
  left_inv f := by
    unfold AddMonoid.End
    ext n
    have : NeZero m := by exact NeZero.of_gt hm
    simp [this, l_zmod_end_apply f n]

  right_inv n := by
    unfold AddMonoid.End
    simp

  -- verify that these mappings preserve addition and multiplication
  map_mul' f g := by
    have : NeZero m := by exact NeZero.of_gt hm
    simp [this, l_zmod_end_apply f (g 1), mul_comm]

  map_add' f g := by
    simp
    rfl

/-! Informal proof:
To show that the endomorphism ring on $G$ is isomorphic to $G$, we construct specific mappings that identify each endomorphism with a single element of $G$​.

For any endomorphism $f$ on $G$ (either $\Z$ or $\Z_m$ with $m \ge 2$), we have $f (n) = n \cdot f(1)$.
So We can map each endomorphism $f$ to the element $f(1)$ in $G$.
Conversely, given an element $n$ in $G$, we construct an endomorphism $f$ where $f (x) = n \cdot x$. 
Finally, verify that these mappings are inverses of each other, and these mappings preserve addition and multiplication.

-/
