import Mathlib
/-! Question:
6. (The Postage Stamp Problem) Let $a$ and $b$ be two relatively prime positive integers. Prove that every sufficiently large positive integer $N$ can be written as a linear combination $a x+b y$ of $a$ and $b$ where $x$ and $y$ are both nonnegative, i.e., there is an integer $N_{0}$ such that for all $N \geq N_{0}$ the equation $a x+b y=N$ can be solved with both $x$ and $y$ nonnegative integers. Prove in fact that the integer $a b-a-b$ cannot be written as a positive linear combination of $a$ and $b$ but that every integer greater than $a b-a-b$ is a positive linear combination of $a$ and $b$ (so every \"postage\" greater than $a b-a-b$ can be obtained using only stamps in denominations $a$ and $b$ ).
-/
set_option maxHeartbeats 0

section UnexploredExercise_1453
namespace UnexploredExercise_1453

-- begin{引理部分}

/-- 关于自然数和整数减法转换的引理 -/
lemma pnat_sub_cast_eq_int_sub (a b : ℕ+) (h : b < a) :
  ((a - b).val : ℤ) = (a.val : ℤ) - (b.val : ℤ) := by
  simp only [PNat.sub_coe, h, ↓reduceIte]
  exact Nat.cast_sub h.le

lemma pnat_sub_cast_eq_int_sub' (a b : ℕ+) (h : b.val < a.val) :
  ((a - b).val : ℤ) = (a.val : ℤ) - (b.val : ℤ) := by
  simp only [PNat.sub_coe, h, ↓reduceIte]
  simp only [(PNat.coe_lt_coe b a).mp h, ↓reduceIte]
  exact Mathlib.Tactic.Zify.Nat.cast_sub_of_lt h

lemma pnat_sub_cast_eq_int_sub'' (a b : ℕ) (h : b < a) :
  @Nat.cast ℤ instNatCastInt (a - b) = (a : ℤ) - (b : ℤ) := by
  exact Mathlib.Tactic.Zify.Nat.cast_sub_of_lt h

/-- 对于互质的正整数 a,b, 如果 x,y 均小于等于 b, 且 x ≠ y, 则 xa 和 ya 模 b 的余数一定不相等 -/
lemma residue_distinct {a b : ℕ+} [h : Fact (a.Coprime b)]
  {x y : ℕ+} (hx : x.val ≤ b.val) (hxy : y < x) :
  ¬(x.val * a.val ≡ y.val * a.val [MOD b.val]) := by
  intro hmod
  have h1 : b.val ∣ (x.val * a.val - y.val * a.val) := by
    apply (Nat.modEq_iff_dvd' ?_).mp (Nat.ModEq.symm hmod)
    simp only [PNat.pos, mul_le_mul_right, PNat.coe_le_coe, hxy.le]
  rw [← Nat.mul_sub_right_distrib] at h1
  have h2 : b.val ∣ (x.val - y.val) := by
    apply (@Nat.Coprime.dvd_mul_right (x.val - y.val) a b ?_).mp h1
    simp only [PNat.coprime_coe, h.out.symm]
  have h3 : b.val ≤ (x.val - y.val) := by
    apply Nat.le_of_dvd ?_ h2
    simp only [Nat.sub_pos_iff_lt, PNat.coe_lt_coe, hxy]
  have h4 : (x.val - y.val) < b.val := by
    apply Nat.le_trans ?_ (Nat.sub_lt (PNat.pos b) Nat.one_pos)
    exact Nat.succ_le_succ (Nat.le_trans (Nat.sub_le_sub_left NeZero.one_le x.val) (Nat.sub_le_sub_right hx 1))
  linarith

lemma residue_distinct' {a b : ℕ+} [h : Fact (a.Coprime b)]
  {x y : ℕ+} (hx : x.val ≤ b.val) (hy : y.val ≤ b.val) (hxy : x ≠ y) :
  ¬(x.val * a.val ≡ y.val * a.val [MOD b.val]) := by
  match Decidable.em (y < x) with
  | .inl case =>
    exact residue_distinct hx case
  | .inr case =>
    rw [not_lt, Ne.le_iff_lt hxy] at case
    rw [Nat.ModEq.comm]
    exact residue_distinct hy case

noncomputable def residue_Bij (a b : ℕ+) [h : Fact (a.Coprime b)] : Finset.Icc 1 (b.val) ≃ Fin b.val := by
  apply Equiv.ofBijective ?f ?hf
  . exact fun k => @Nat.cast (Fin b.1) (@Fin.instNatCast b.1 (NeZero.of_pos b.2)) (k.1 * a.1 % b.1)
  . apply (Fintype.bijective_iff_injective_and_card _).mpr
    constructor
    . intro x y hxy
      simp only [Fin.ext_iff, Fin.val_natCast, dvd_refl, Nat.mod_mod_of_dvd] at hxy
      replace hxy : x.1 * a.1 ≡ y.1 * a.1 [MOD b.1] := by exact hxy
      have : 0 < x.1 ∧ 0 < y.1 := by exact ⟨(Finset.mem_Icc.mp x.2).1, (Finset.mem_Icc.mp y.2).1⟩
      have := @residue_distinct' a b h ⟨x.1, this.1⟩ ⟨y.1, this.2⟩ (Finset.mem_Icc.mp x.2).2 (Finset.mem_Icc.mp y.2).2
      rw [PNat.mk_coe, ne_eq, Subtype.mk.injEq, Subtype.coe_inj] at this
      contrapose! this
      exact ⟨this, hxy⟩
    . rw [Fintype.card_coe, Nat.card_Icc, add_tsub_cancel_right, Fintype.card_fin]

/-- 每个余数都可以表示为某个k*a的形式 -/
lemma residue_complete {a b : ℕ+} [h : Fact (a.Coprime b)]
  (r : Fin b.val) :
  ∃ k : Finset.Icc 1 (b.val), r ≡ (k * a) [MOD b.val] := by
  obtain ⟨k, hk⟩ := (Equiv.bijective (@residue_Bij a b h)).surjective r
  use k
  simp only [residue_Bij, Equiv.ofBijective_apply, Fin.ext_iff, Fin.val_natCast, dvd_refl, Nat.mod_mod_of_dvd] at hk
  exact ((Nat.mod_eq_of_lt r.2).symm ▸ hk).symm

/-- 完全剩余系定理: 对于互质的正整数 a,b, {ka ∣ 1≤ k ≤ b}构成模 b 的完全剩余系. -/
theorem complete_residue_system {a b : ℕ+} [h : Fact (a.Coprime b)] :
    ∀ n : ℕ, ∃ k : Finset.Icc 1 (b.val), n ≡ (k * a) [MOD b.val] := by
  intro n
  obtain ⟨k, hk⟩ := @residue_complete a b h n
  use k
  unfold Nat.ModEq at hk
  simp only [Fin.val_natCast, dvd_refl, Nat.mod_mod_of_dvd] at hk
  exact hk

/-- 当 n ≥ ka 且 n ≡ ka (mod b) 时, 存在自然数 y 使得 ak + by = n-/
lemma sylvester_theorem_case_one {a b : ℕ+} [Fact (a.Coprime b)]
  {n : ℕ} {k : Finset.Icc 1 (b.val)} (h : n ≥ k * a) (hk_cong : n ≡ k * a [MOD b]) :
  ∃ y : ℕ, a * k.val + b * y = n := by
  rcases Nat.ModEq.dvd hk_cong.symm with ⟨y, hy⟩
  use Int.toNat y
  have hy_nonneg : 0 ≤ y := by
    apply @Int.le_of_mul_le_mul_left (b.val : ℤ) 0 y ?_ (Int.ofNat_pos.mpr b.2)
    exact (mul_zero (b.val : ℤ)).symm ▸ hy ▸ (Int.sub_nonneg_of_le (Nat.cast_le.mpr h))
  rw [← Int.toNat_of_nonneg hy_nonneg] at hy
  zify at hy ⊢
  rw [add_comm, ← eq_sub_iff_add_eq, mul_comm _ (k.val : ℤ), hy]

/-- 当 n < ka 且 n ≡ ka (mod b) 时, 存在正整数 y 使得 ak - by = n-/
lemma sylvester_theorem_case_two {a b : ℕ+} [Fact (a.Coprime b)]
  {n : ℕ} {k : Finset.Icc 1 (b.val)} (h : n < a.val * k.val) (hk_cong : n ≡ a * k.val [MOD b]):
  ∃ y : ℕ+, a * k.val - b * y = n := by
  rcases Nat.ModEq.dvd hk_cong with ⟨y, hy⟩
  zify at hy
  have ypos : 0 < y := by
    have : 0 < (a * k.val : ℤ) - (n : ℤ) := Int.sub_pos_of_lt (Nat.cast_lt.mpr h)
    rw [hy] at this
    exact lt_of_nsmul_lt_nsmul_right b.val this
  have : 0 < (Int.toNat y) := by
    apply Int.lt_toNat.mpr ypos
  use ⟨y.toNat, this⟩
  rw [← Int.toNat_of_nonneg (Int.le_of_lt ypos), ← Nat.cast_mul, ← Mathlib.Tactic.Zify.Nat.cast_sub_of_lt h, Int.ofNat_mul_out, Int.natCast_inj] at hy
  rw [PNat.mk_coe, ← hy, Nat.sub_sub_self h.le]

/-- 对于互质的正整数 a,b, 如果 ac = bd 且 d > 0,则 a ≤ d-/
lemma lt_of_mul_eq_mul_coprime {a b : ℕ+} {c d : ℤ} (h : a.Coprime b) (heq : a * c = b * d) (hd : 0 < d):
  a ≤ d := by
  have hdvd : (a.val : ℤ) ∣ d := by
    have : (a.val : ℤ) ∣ b.val * d := by
      rw [← heq]
      exact dvd_mul_right _ _
    rw [← PNat.coprime_coe, ← Nat.isCoprime_iff_coprime] at h
    exact IsCoprime.dvd_of_dvd_mul_left h this
  rw [Int.dvd_def] at hdvd
  obtain ⟨k, hk⟩ := hdvd
  rw [hk]
  have this_1 : 0 < (a : ℤ) * k := by
      rw [← hk]
      exact hd
  have this_2 : 0 < (a : ℤ) := by
    simp only [Nat.cast_pos, PNat.pos]
  rw [le_mul_iff_one_le_right ((Nat.cast_pos (α := ℤ)).mpr (PNat.pos a))]
  have : 0 < k := by
    exact (pos_iff_pos_of_mul_pos this_1).mp this_2
  exact this

-- end{引理部分}

-- begin{正文部分}

/-- Sylvester定理的边界情况: 对于任意的互质整数 a,b, 不可能存在非负整数 x, y 满足 ax + by = ab -a -b. -/
theorem sylvester_theorem_edge_case {a b : ℕ+} [h : Fact (a.Coprime b)] :
  ¬ ∃ (x y : ℕ), (a : ℤ) * x + b * y = a * b - a - b := by
  -- 假设存在自然数 $x$ 和 $y$ 使得 $a * x + b * y = a * b - a - b$.
  rintro ⟨x, y, hxy⟩
  have hay : (a.val : ℤ) ≤ (y + 1) := by
    -- 从等式 $a \cdot x + b \cdot y = a \cdot b - a - b$ 推导出 $a \cdot (b - x - 1) = b \cdot (y + 1)$.
    have : (a : ℤ) * (b.val - x - 1) = b.val * (y + 1) := by
      rw [sub_sub, eq_sub_iff_add_eq] at hxy
      simp only [mul_sub_left_distrib, mul_one, ← hxy]
      ring
    -- 由于 $a, b$互素, 因此 $a \mid y + 1$, 进而 $a \leq y + 1$.
    exact lt_of_mul_eq_mul_coprime h.out this (Int.succ_ofNat_pos y)
  -- 类似地, 成立 $b \leq x + 1$.
  have hbx : (b.val : ℤ) ≤ (x + 1) := by
    have : (b : ℤ) * (a.val - y - 1) = a.val * (x + 1) := by
      rw [sub_sub, eq_sub_iff_add_eq] at hxy
      simp only [mul_sub_left_distrib, mul_one, mul_comm (b : ℤ) (a : ℤ), ← hxy]
      ring
    exact lt_of_mul_eq_mul_coprime h.out.symm this (Int.succ_ofNat_pos x)
  have : 2 * a.val * b.val ≤ a.val * b.val := by
    -- 重写条件式为 $ab = a(x + 1) + b(y + 1)$.
    have : a.val * b.val = a.val * (x + 1) + b.val * (y + 1) := by
      rw [sub_sub, eq_sub_iff_add_eq] at hxy
      zify
      rw [← hxy]
      ring
    rw [this]
    -- 计算有$2ab = ab + ba ≤ a(x + 1) + b(y + 1) = ab$.
    calc
      _ = a.val * b.val + a.val * b.val := by ring
      _ ≤ a.val * (x + 1) + a.val * b.val := by
        simp only [add_le_add_iff_right, gt_iff_lt, PNat.pos, mul_le_mul_left]
        zify
        exact hbx
      _ ≤ _ := by
        simp only [mul_comm a.val, add_le_add_iff_left, gt_iff_lt, PNat.pos, mul_le_mul_left]
        zify
        exact hay
  -- 这和 $a, b$ 是自然数矛盾.
  contrapose! this
  norm_num

/-- Sylvester定理: 对于互质的正整数 a 和 b,任何大于 ab - a - b 的自然数 n 都可以表示为 n = ax + by, 其中 x,y 为非负整数.-/
theorem sylvester_theorem {a b : ℕ+} [h : Fact (a.Coprime b)] :
  ∀ n : ℕ, n > a * b - a - b → ∃ x y : ℕ, a * x + b * y = n := by
  -- 选取任意自然数 $n$,
  intro n hn
  -- -- 由完全剩余系定理，存在自然数 $k ∈ [1,b]$ 使得 $n ≡ k·a (mod b)$.
  obtain ⟨k, hk⟩ := @complete_residue_system a b h n
  -- 分类讨论 $n ≥ k·a$ 和 $n < k·a$ 两种情况.
  by_cases case : n ≥ k * a
  · use k -- 当 $n ≥ k·a$ 时, 由同余关系，存在自然数 $y$ 使得 $a·k + b·y = n$.
    exact sylvester_theorem_case_one case hk
  · simp only [ge_iff_le, not_le] at case
    rw [mul_comm] at case hk
    -- 当 $n < k·a$ 时, 由同余关系，存在正整数 $y$ 使得 $a·k - b·y = n$.
    obtain ⟨y, hy⟩ := sylvester_theorem_case_two case hk
    -- 分类讨论 $k = b$ 和 $k < b$.
    by_cases casek : k = b.val
    . rw [casek] at hy case
      use 0, a.val - y.val -- 当 $k = b$ 时, $a·0 + b·(a - y) = n$.
      rw [mul_comm a.val] at hy
      rw [Nat.mul_sub_left_distrib, mul_zero, zero_add, hy]
    . -- 当 $k < b$, 亦即 $k ≤ b - 1$ 时,
      replace casek : k.val ≤ (b.val - 1) := by
        let z := k.2
        rw [Finset.mem_Icc] at z
        replace z := z.2
        simp only [Nat.le_iff_lt_or_eq, casek, or_false] at z
        exact Nat.le_sub_one_of_lt z
      -- 考虑反证法, 假设存在非负整数 $x, y$ 使得 $a·x + b·y = n$, 现证明 $n ≤ ab - a - b$, 进而导出矛盾.
      contrapose! hn
      clear case hn hk
      -- 亦即说明 $n = a·k - b·y ≤ ab - a - b$.
      rw [← hy]
      calc
        -- 由于$a·k - b·y ≤ a·(b - 1) - b·1 = ab - a - b$, 因此确有待证不等式成立. 证明结束.
        _ ≤ a.val * (b.val - 1) - b.val * y.val := by
          apply Nat.sub_le_sub_right ?_ (b.val * y.val)
          simp only [mul_le_mul_left (PNat.pos a), casek]
        _ ≤ _ := by
          rw [Nat.mul_sub_left_distrib, mul_one]
          apply Nat.sub_le_sub_left
          exact Nat.le_mul_of_pos_right b.val y.2

-- end{正文部分}

end UnexploredExercise_1453
end UnexploredExercise_1453


/-! Informal proof:
1. Sylvester定理的边界情况: 对于任意的互质整数 a,b, 不可能存在非负整数 x, y 满足 ax + by = ab -a -b.
  - 假设存在自然数 $x$ 和 $y$ 使得 $a * x + b * y = a * b - a - b$.
  - 从等式 $a \cdot x + b \cdot y = a \cdot b - a - b$ 推导出 $a \cdot (b - x - 1) = b \cdot (y + 1)$.由于 $a, b$互素, 因此 $a \mid y + 1$, 进而 $a \leq y + 1$. 类似地, 成立 $b \leq x + 1$.
  - 重写条件式为 $ab = a(x + 1) + b(y + 1)$. 计算有$2ab = ab + ba ≤ a(x + 1) + b(y + 1) = ab$. 这和 $a, b$ 是自然数矛盾.
2. Sylvester定理: 对于互质的正整数 a 和 b,任何大于 ab - a - b 的自然数 n 都可以表示为 n = ax + by, 其中 x,y 为非负整数.
  - 选取任意自然数 $n$, 由于对于互质的正整数 $a,b$, $\{ka ∣ 1≤ k ≤ b\}$ 构成模 $b$ 的完全剩余系, 因此存在自然数 $k ∈ [1,b]$ 使得 $n ≡ k·a (\mod b)$.
  - 分类讨论 $n ≥ k·a$ 和 $n < k·a$ 两种情况. 当 $n ≥ k·a$ 时, 由同余关系，存在自然数 $y$ 使得 $a·k + b·y = n$.
  - 当 $n < k·a$ 时, 由同余关系，存在正整数 $y$ 使得 $a·k - b·y = n$. 
  - 分类讨论 $k = b$ 和 $k < b$. 当 $k = b$ 时, $a·0 + b·(a - y) = n$.
  - 当 $k < b$, 亦即 $k ≤ b - 1$ 时, 考虑反证法, 假设存在非负整数 $x, y$ 使得 $a·x + b·y = n$, 现证明 $n ≤ ab - a - b$, 进而导出矛盾. 亦即说明 $n = a·k - b·y ≤ ab - a - b$. 由于$a·k - b·y ≤ a·(b - 1) - b·1 = ab - a - b$, 因此确有待证不等式成立. 证明结束.
-/
