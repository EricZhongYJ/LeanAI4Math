import Mathlib
/-! Question:
(3) Let $a$ and $b$ be integers. Prove that if $a \mid b$ and $b \mid a$, then $|a|=|b|$.
-/

-- Let $a$ and $b$ be integers. Prove that if $a \\mid b$ and $b \\mid a$, then $|a|=|b|$.
example (a : ℤ) (b : ℤ) : (∃k, b = k * a) ∧ (∃k, a = k * b) → |a| = |b| := by
  intro h
  -- 引入 $k$ 使 $b = k * a$ 和 $q$ 使 $a = q * b$
  cases h.left with
  | intro k hk =>
    cases h.right with
    | intro q hq =>
      -- 带入 $b = k * a$ 得 $a = q * (k * a)$
      rw [hk] at hq
      -- 分情讨论，如果 a = 0, 经过简单运算直接得证
      if ha : a = 0 then
        rw [ha]
        rw [ha] at hk
        simp at hk
        rw [hk]
      -- 如果 a != 0
      else
        rw [← mul_assoc] at hq
        have hqq : a * (q * k) = a * 1 := by
          symm
          simp
          rw [mul_comm]
          exact hq
        -- 消去等式 $a * (q * k) = a$ 两边的 $a$ 得 $q * k = 1$
        apply Int.eq_of_mul_eq_mul_left ha at hqq
        -- 得到 $(q = 1 ∧ k = 1) ∨ (q = -1 ∧ k = -1)$
        apply Int.eq_one_or_neg_one_of_mul_eq_one' at hqq
        -- 分别带入，得证
        cases hqq with
        | inl l =>
          rw [l.right] at hk
          simp at hk
          exact hk ▸ rfl
        | inr r =>
          rw [r.right] at hk
          have hkk := congrArg abs hk
          simp at hkk
          symm
          exact hkk


/-! Informal proof:
引入 $k$ 使 $b = k * a$ 和 $q$ 使 $a = q * b$
带入 $b = k * a$ 得 $a = q * (k * a)$
分情讨论，如果 a = 0, 经过简单运算直接得证
如果 $a \
eq 0$
消去等式 $a * (q * k) = a$ 两边的 $a$ 得 $q * k = 1$
得到 $(q = 1 ∧ k = 1) ∨ (q = -1 ∧ k = -1)$
分别带入 $q$ 和 $k$，得证
-/
