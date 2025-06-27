import Mathlib
/-! Question:
20. Let $p$ be a prime and let $n$ be a positive integer. Show that if $x$ is an element of the group $G$ such that $x^{p^{n}}=1$ then $|x|=p^{m}$ for some $m \leq n$.
-/

variable {G : Type*} [Group G] (x : G) {p : ℕ} {n : ℕ} [hp : Fact (Nat.Prime p)]

example (h : x ^ p ^ n = 1) : ∃ m ≤ n, orderOf x = p ^ m := by
  obtain ⟨m, hm⟩ := exists_orderOf_eq_prime_pow_iff.2 ⟨n, h⟩
  --By a theorem in Mathlib4, $\exist m, |x| = p ^ m$
  have h₁ := hm ▸ orderOf_le_of_pow_eq_one (Nat.pow_pos (Nat.Prime.pos hp.elim)) h
  --Since $x ^ {p ^ n} = 1, p ^ m = |x| \le p ^ n.$
  have := (Nat.pow_le_pow_iff_right (Nat.Prime.one_lt hp.elim)).1 h₁
  --Since $p > 1, p ^ m \le p ^ n\Rightarrow m \le n$
  exact ⟨m, this, hm⟩
  --Now $m$ is what we need
/-! Informal proof:
By a theorem in Mathlib4, $\exist \ m, |x| = p ^ m$
Since $x ^ {p ^ n} = 1, p ^ m = |x| \le p ^ n.$
Since $p > 1, p ^ m \le p ^ n\Rightarrow m \le n$
Now $m$ is what we need.

-/
