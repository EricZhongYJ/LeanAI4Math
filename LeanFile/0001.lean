import Mathlib
/-! Question:
Prove that each of the following is a subring of the indicated ring:
$1\{x+\sqrt{3} y: x, y \cong z\}$ is a subring of $\mathbb{R}$.
$2\left\{x+2^{1 / 3} y+2^{2 / 3} z: x, y, z \in z\right\}$ is a subring of $\mathbb{R}$.
$3\left\{x 2^{y}: x, y \in z\right\}$ is a subring of $\mathbb{R}$.
-/

/- **Q1.** We show that $S=\{x+\sqrt{3}y|x,y\in\mathbb{Z}\}$ is a subring of  $\mathbb{R}$ by checking that $0,1\in S$ and $S$ is closed under addition, multiplication and taking opposite number.-/
def Q1 : Subring ℝ := {
  carrier := {z : ℝ | ∃ x y : ℤ, z = x + √3 * y}
  -- (1) $0\in S$, choose $x=0,y=0$ .
  zero_mem' := by use 0, 0; norm_num
  -- (2) $1\in S$, choose $x=1,y=0$ .
  one_mem' := by
    use 1, 0
    norm_num
  --(3) $S$ is closed under addition. For $x+y\sqrt{3},z+w\sqrt{3}\in S$, it is obvious that
  --$$ (x+y\sqrt{3}) + (z+w\sqrt{3}) = (x+z)+(y+w)\sqrt{3}\in S \textrm{ .}$$
  add_mem' := by
    rintro a b ⟨x, y, ha⟩ ⟨z, w, hb⟩
    use x + z, y + w
    push_cast
    linear_combination ha + hb
  --(4) $S$ is closed under multiplication. For $x+y\sqrt{3},z+w\sqrt{3}\in S$, it is obvious that
  --$$ (x+y\sqrt{3}) (z+w\sqrt{3}) = (xz+3yw)+(xw+yz)\sqrt{3}\in S \textrm{ .}$$
  mul_mem' := by
    rintro a b ⟨x, y, ha⟩ ⟨z, w, hb⟩
    use x * z + 3 * y * w, x * w + y * z
    push_cast
    rw [ha, hb]
    ring_nf
    rw [show √3 ^ 2 = 3 from Real.sq_sqrt (by norm_num)]
    ring
  --(5) $S$ is closed under taking opposite number. For $x+y\sqrt{3}\in S$, it is obvious that
  --$$-(x+y\sqrt{3})=(-x)+(-y)\sqrt{3}\in S \textrm{ .}$$
  neg_mem' := by
    rintro a ⟨x, y, ha⟩
    use -x, -y
    push_cast
    linear_combination -ha
} --From (1),(2),(3),(4),(5) we can conclude that $S$ is a subring of $\mathbb{R}$.

/- **Q2.** We show that $S=\{x+\sqrt[3]{2}y+\sqrt[3]{4}z| x,y,z\in\mathbb{Z}\}$ is a subring of $\mathbb{R}$ by checking that $0,1\in S$ and $S$ is closed under addition, multiplication and taking opposite number.-/
def Q2 : Subring ℝ := {
  carrier := {w : ℝ | ∃ x y z : ℤ, w = x + Real.rpow 2 (1 / 3) * y + Real.rpow 2 (2 / 3) * z}
  -- (1) $0\in S$, choose $x=0,y=0,z=0$ .
  zero_mem' := by
    use 0, 0, 0
    norm_num
  -- (2) $1\in S$, choose $x=1,y=0,z=0$ .
  one_mem' := by
    use 1, 0, 0
    norm_num
  --(3) $S$ is closed under addition. For $x_1+y_1\sqrt[3]{2}+z_1\sqrt[3]{4},x_2+y_2\sqrt[3]{2}+z_2\sqrt[3]{4}\in S$, it is obvious that
  --$$ (x_1+y_1\sqrt[3]{2}+z_1\sqrt[3]{4}) + (x_2+y_2\sqrt[3]{2}+z_2\sqrt[3]{4}) = (x_1+x_2)+(y_1+y_2)\sqrt[3]{2}+(z_1+z_2)\sqrt[3]{4}\in S \textrm{ .}$$
  add_mem' := by
    rintro a b ⟨x1, y1, z1, ha⟩ ⟨x2, y2, z2, hb⟩
    use x1 + x2, y1 + y2, z1 + z2
    push_cast
    linear_combination ha + hb
  --(4) $S$ is closed under multiplication. For $x_1+y_1\sqrt[3]{2}+z_1\sqrt[3]{4},x_2+y_2\sqrt[3]{2}+z_2\sqrt[3]{4}\in S$, it is obvious that
  --$$ (x_1+y_1\sqrt[3]{2}+z_1\sqrt[3]{4}) (x_2+y_2\sqrt[3]{2}+z_2\sqrt[3]{4}) = (x_1x_2+2y_1z_2+2z_1y_2)+(x_1y_2+y_1x_2+2z_1z_2)\sqrt[3]{2}+(x_1z_2+y_1y_2+z_1x_2)\sqrt[3]{4}\in S \textrm{ .}$$
  mul_mem' := by
    have cube_cbrt : (Real.rpow 2 (1 / 3)) ^ 3 = 2 := by
      rw [← Real.rpow_natCast, Real.rpow_eq_pow, ← Real.rpow_mul (by norm_num)]
      norm_num
    have pow4_cbrt : (Real.rpow 2 (1 / 3)) ^ 4 = 2 * Real.rpow 2 (1 / 3) := by
      rw [show 4 = 3 + 1 from rfl, pow_succ, cube_cbrt]
    rintro a b ⟨x1, y1, z1, ha⟩ ⟨x2, y2, z2, hb⟩
    use x1 * x2 + 2 * y1 * z2 + 2 * z1 * y2
    use x1 * y2 + y1 * x2 + 2 * z1 * z2
    use x1 * z2 + y1 * y2 + z1 * x2
    push_cast
    have : Real.rpow 2 (2 / 3) = Real.rpow 2 (1 / 3) ^ 2 := by
      rw [← Real.rpow_natCast, Real.rpow_eq_pow, Real.rpow_eq_pow, ← Real.rpow_mul (by norm_num)]
      norm_num
    rw [ha, hb, this]
    ring_nf
    rw [cube_cbrt, pow4_cbrt]
    ring
  --(5) $S$ is closed under taking opposite number. For $x+y\sqrt[3]{2}+z\sqrt[3]{4}\in S$, it is obvious that
  --$$-(x+y\sqrt[3]{2}+z\sqrt[3]{4})=(-x)+(-y)\sqrt[3]{2}+(-z)\sqrt[3]{4}\in S \textrm{ .}$$
  neg_mem' := by
    rintro a ⟨x, y, z, ha⟩
    use -x, -y, -z
    push_cast
    linear_combination -ha
} -- From (1),(2),(3),(4),(5) we can conclude that $S$ is a subring of $\mathbb{R}$.

/- **Q3.** We show that $S=\{x2^y|x,y\in\mathbb{Z}\}$ is a subring of  $\mathbb{R}$ by checking that $0,1\in S$ and $S$ is closed under addition, multiplication and taking opposite number.-/
def Q3 : Subring ℝ := {
  carrier := {z : ℝ | ∃ x y : ℤ, z = x * 2 ^ y}
  -- (1) $0\in S$, choose $x=0,y=1$ .
  zero_mem' := by
    use 0, 1
    norm_num
  -- (2) $1\in S$, choose $x=1,y=0$ .
  one_mem' := by
    use 1, 0
    norm_num
  -- (3) $S$ is closed under addition. For $x2^y,z2^w\in S$, we split into two cases:
  add_mem' := by
    have cast_zpow_sub {a b : ℤ} (hab : a ≤ b) : (2 : ℝ) ^ (b - a).natAbs = (2 : ℝ) ^ ((b : ℝ) - (a : ℝ)) := by
      rw [← Int.cast_sub]
      nth_rw 2 [show b - a = |b - a| by rw [abs_of_nonneg (by linarith)]]
      rw [show |b - a| = (b - a).natAbs from Int.abs_eq_natAbs (b - a)]
      norm_cast
    rintro a b ⟨x, y, ha⟩ ⟨z, w, hb⟩
    rcases le_or_lt w y with hwy | hyw
    -- *case (i):* $y \geq w$, we have :
    -- $$ x2^y+z2^w=(x2^{y-w}+z)2^w\in S \textrm{ .}$$
    . use x * 2 ^ (y - w).natAbs + z, w
      push_cast
      rw [cast_zpow_sub hwy, ← Real.rpow_intCast, add_mul, mul_assoc,
        ← Real.rpow_add (by norm_num), sub_add_cancel, Real.rpow_intCast, Real.rpow_intCast]
      linear_combination ha + hb
    -- *case (ii):* $y < w$, we have:
    -- $$ x2^y+z2^w=(x+z2^{w-y})2^y\in S \textrm{ .}$$
    use x + z * 2 ^ (w - y).natAbs, y
    push_cast
    rw [cast_zpow_sub hyw.le, ← Real.rpow_intCast, add_mul, mul_assoc,
      ← Real.rpow_add (by norm_num), sub_add_cancel, Real.rpow_intCast, Real.rpow_intCast]
    linear_combination ha + hb
  --(4) $S$ is closed under multiplication. For $x2^y,z2^w\in S$, it is obvious that
  --$$ (x2^y) (z2^w) = (xz)2^{y+w}\in S \textrm{ .}$$
  mul_mem' := by
    rintro a b ⟨x, y, ha⟩ ⟨z, w, hb⟩
    use x * z, y + w
    rw [ha, hb]
    conv_rhs => rhs; rw [← Real.rpow_intCast, Int.cast_add, Real.rpow_add (by norm_num)]
    rw [← Real.rpow_intCast, ← Real.rpow_intCast]
    push_cast
    ring
  -- (5) $S$ is closed under taking the opposite number. For $x2^y\in S$, it is obvious that
  -- $$-(x2^y)=(-x)2^y\in S \textrm{ .}$$
  neg_mem' := by
    rintro a ⟨x, y, ha⟩
    use -x, y
    push_cast
    linear_combination -ha
} -- From (1),(2),(3),(4),(5) we can conclude that $S$ is a subring of $\mathbb{R}$.

/-! Informal proof:
**Q1.** We show that $S=\{x+\sqrt{3}y|x,y\in\mathbb{Z}\}$ is a subring of  $\mathbb{R}$ by checking that $0,1\in S$ and $S$ is closed under addition, multiplication and taking opposite number.
(1) $0\in S$, choose $x=0,y=0$ .
(2) $1\in S$, choose $x=1,y=0$ .
(3) $S$ is closed under addition. For $x+y\sqrt{3},z+w\sqrt{3}\in S$, it is obvious that
$$ (x+y\sqrt{3}) + (z+w\sqrt{3}) = (x+z)+(y+w)\sqrt{3}\in S \textrm{ .}$$
(4) $S$ is closed under multiplication. For $x+y\sqrt{3},z+w\sqrt{3}\in S$, it is obvious that
$$ (x+y\sqrt{3}) (z+w\sqrt{3}) = (xz+3yw)+(xw+yz)\sqrt{3}\in S \textrm{ .}$$
(5) $S$ is closed under taking opposite number. For $x+y\sqrt{3}\in S$, it is obvious that
$$-(x+y\sqrt{3})=(-x)+(-y)\sqrt{3}\in S \textrm{ .}$$
From (1),(2),(3),(4),(5) we can conclude that $S$ is a subring of $\mathbb{R}$.
**Q2.** We show that $S=\{x+\sqrt[3]{2}y+\sqrt[3]{4}z| x,y,z\in\mathbb{Z}\}$ is a subring of $\mathbb{R}$ by checking that $0,1\in S$ and $S$ is closed under addition, multiplication and taking opposite number.
(1) $0\in S$, choose $x=0,y=0,z=0$ .
(2) $1\in S$, choose $x=1,y=0,z=0$ .
(3) $S$ is closed under addition. For $x_1+y_1\sqrt[3]{2}+z_1\sqrt[3]{4},x_2+y_2\sqrt[3]{2}+z_2\sqrt[3]{4}\in S$, it is obvious that
$$ (x_1+y_1\sqrt[3]{2}+z_1\sqrt[3]{4}) + (x_2+y_2\sqrt[3]{2}+z_2\sqrt[3]{4}) = (x_1+x_2)+(y_1+y_2)\sqrt[3]{2}+(z_1+z_2)\sqrt[3]{4}\in S \textrm{ .}$$
(4) $S$ is closed under multiplication. For $x_1+y_1\sqrt[3]{2}+z_1\sqrt[3]{4},x_2+y_2\sqrt[3]{2}+z_2\sqrt[3]{4}\in S$, it is obvious that
$$ (x_1+y_1\sqrt[3]{2}+z_1\sqrt[3]{4}) (x_2+y_2\sqrt[3]{2}+z_2\sqrt[3]{4}) = (x_1x_2+2y_1z_2+2z_1y_2)+(x_1y_2+y_1x_2+2z_1z_2)\sqrt[3]{2}+(x_1z_2+y_1y_2+z_1x_2)\sqrt[3]{4}\in S \textrm{ .}$$
(5) $S$ is closed under taking opposite number. For $x+y\sqrt[3]{2}+z\sqrt[3]{4}\in S$, it is obvious that
$$-(x+y\sqrt[3]{2}+z\sqrt[3]{4})=(-x)+(-y)\sqrt[3]{2}+(-z)\sqrt[3]{4}\in S \textrm{ .}$$
From (1),(2),(3),(4),(5) we can conclude that $S$ is a subring of $\mathbb{R}$.
**Q3.** We show that $S=\{x2^y|x,y\in\mathbb{Z}\}$ is a subring of  $\mathbb{R}$ by checking that $0,1\in S$ and $S$ is closed under addition, multiplication and taking opposite number.
(1) $0\in S$, choose $x=0,y=1$ .
(2) $1\in S$, choose $x=1,y=0$ .
(3) $S$ is closed under addition. For $x2^y,z2^w\in S$, we split into two cases:
  
*case (i):* $y \geq w$, we have :
$$ x2^y+z2^w=(x2^{y-w}+z)2^w\in S \textrm{ .}$$
*case (ii):* $y < w$, we have:
$$ x2^y+z2^w=(x+z2^{w-y})2^y\in S \textrm{ .}$$
(4) $S$ is closed under multiplication. For $x2^y,z2^w\in S$, it is obvious that
$$ (x2^y) (z2^w) = (xz)2^{y+w}\in S \textrm{ .}$$
(5) $S$ is closed under taking the opposite number. For $x2^y\in S$, it is obvious that
$$-(x2^y)=(-x)2^y\in S \textrm{ .}$$
From (1),(2),(3),(4),(5) we can conclude that $S$ is a subring of $\mathbb{R}$.
-/
