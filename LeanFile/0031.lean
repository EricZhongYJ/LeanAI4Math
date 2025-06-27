import Mathlib
/-! Question:
(4) Let $a$ and $b$ be positive integers, and suppose that $a \mid b$. Prove that $(a+1) \left\lvert\,\left(b+\frac{b}{a}\right)\right.$.
-/

-- Let $a$ and $b$ be positive integers, and suppose that $a \\mid b$. Prove that $(a+1) \\left\\lvert\\,\\left(b+\\frac{b}{a}\\right)\\right.$.
example (a : ℕ) (b : ℕ) (ha : a > 0) (hb : b > 0) (h : ∃k, b = k * a) : ∃q, (b + b / a) = q * (a + 1) := by
  -- 引入 k 使 b = k * a
  cases h with
  | intro d hd =>
    -- 使用 b = k * a 写到改写一下公式
    rw [hd]
    -- 证明 d * a / a = d
    have inv : d * a / a = d := by
      rw [Nat.mul_div_left]
      exact ha
    rw [inv]
    -- 另 q = d，得证
    exists d


/-! Informal proof:
1. 设 $k$ 使 $b = k * a$
2. 需要证明存在 $q$ 使 $b + \frac{b}{a} = q * (a+1)$
3. 带入 $b = k * a$ 得 $k * a + \frac{k * a}{a} = q * (a+1)$
4. 因为 $a > 0$, 化简得$k*(a+1) = q * (a+1)$
5. $q$ 即为 $k$ 得证
-/
