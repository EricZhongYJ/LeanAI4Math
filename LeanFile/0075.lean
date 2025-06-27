import Mathlib
/-! Question:
14. Show that $\left(x \in D_{2 n} \mid x^{2}=1\right\}$ is not a subgroup of $D_{2 n}$ (here $n \geq 3$ ).
-/
set_option maxHeartbeats 0
open DihedralGroup

example (n : ℕ) (hn : 3 ≤ n) :
  ¬ IsSubgroup {x : DihedralGroup n | x^2 = 1} := by 
  -- 考虑反证法. 将推出 $n ≤ 2$, 进而矛盾于 $3 ≤ n$.
  intro h
  -- 首先, $s$ 和 $sr$ 按定义均位于集合中.
  have hs_in : (@sr n 0) ∈ {x : DihedralGroup n | x^2 = 1} := by 
    simp only [Set.mem_setOf_eq, pow_two, sr_mul_self]
  have hsr1_in : (@sr n 1) ∈ {x : DihedralGroup n | x^2 = 1} := by 
    simp only [Set.mem_setOf_eq, pow_two, sr_mul_self]
  -- 于是 $s * sr = r$ 根据运算封闭性, 同样位于位于集合中.
  haveI := Set.mem_setOf_eq ▸ (sub_zero (1 : ZMod n)) ▸ sr_mul_sr _ _ ▸ (h.mul_mem hs_in hsr1_in)
  -- 因此 $r$ 的阶小于等于 $2$, 另一方面, 熟知二面体群中 $r$ 的阶为 $n$. 故而 $n ≤ 2$. 证明结束.
  replace : orderOf (@r n 1) ≤ 2 := orderOf_le_of_pow_eq_one (by norm_num) this
  rw [@orderOf_r n (NeZero.of_gt hn) 1, ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (Nat.lt_of_succ_lt hn), Nat.gcd_one_right, Nat.div_one] at this
  linarith

example (n : ℕ) (hn : 3 ≤ n) (G : Subgroup (DihedralGroup n)) :
  ¬ G.carrier = {x : DihedralGroup n | x^2 = 1} := by
  intro h
  have : (@sr n 0) ∈ G.carrier ∧ (@sr n 1) ∈ G.carrier := by
    simp only [h, Set.mem_setOf_eq, pow_two, sr_mul_self, and_self]
  replace := Set.mem_setOf_eq ▸ h ▸ Subgroup.mem_carrier.2 ((sub_zero (1 : ZMod n)) ▸ sr_mul_sr _ _ ▸ (G.mul_mem this.1 this.2))
  replace := orderOf_r_one ▸ orderOf_le_of_pow_eq_one (by norm_num) this
  linarith

/-! Informal proof:
1. 考虑反证法. 将推出 $n ≤ 2$, 进而矛盾于 $3 ≤ n$.
2. 首先, $s$ 和 $sr$ 按定义均位于集合中. 于是 $s * sr = r$ 根据运算封闭性, 同样位于位于集合中.
3. 因此 $r$ 的阶小于等于 $2$, 另一方面, 熟知二面体群中 $r$ 的阶为 $n$. 故而 $n ≤ 2$. 证明结束.
-/
