import Mathlib
/-! Question:
3.3.11*. 设 $a, b \in F_{2^{n}}, n$ 是奇数. 若 $a^{2}+b^{2}+a b=0$, 则 $a=b=0$.
-/
import Mathlib.Tactic

/- Let a, b∈F_{2ⁿ}, n odd. If a²+b²+ab=0, then a=b=0 -/

example {F : Type*} [Field F] (n : ℕ) (hn : Odd n) [Fintype F] (hchar : CharP F 2) (hcard : Fintype.card F = 2 ^ n) (a b : F) (h : a ^ 2 + b ^ 2 + a * b = 0) : a = 0 ∧ b = 0 := by
  constructor
  -- If a≠0, then (a^2+b^2+ab)/a^2=1+c^2+c=0, where c=b/a, and c^3-1=0.
  by_contra ha
  have h' : (a ^ 2 + b ^ 2 + a * b) / a ^ 2 = 0 := by
    rw [h]
    exact zero_div (a ^ 2)
  rw [add_div, add_div, div_self, ← div_pow, pow_two a, mul_div_mul_left b a ha] at h'
  set c := b / a with hc
  have h'' : (1 + c ^ 2 + c) * (c - 1) = 0 := by
    rw [h', zero_mul]
  have h''' : c ^ 3 - 1 = (1 + c ^ 2 + c) * (c - 1) := by
    ring
  rw [h'', sub_eq_zero] at h'''
  have hcnzero : c ≠ 0 := by
    by_contra hczero
    rw [hczero] at h'''
    simp at h'''
  -- Since F is a finite field with cardinality 2^n, c^{2^n}=c
  have hcpow : c ^ (2 ^ n) = c := by
    rw [← hcard]
    exact FiniteField.pow_card c
  rcases hn with ⟨k, hk⟩
  -- since n is odd and 3 ∣ 2^n-2, c^2=c, so c=1.
  have hmod : 2 ^ n % 3 = 2 := by
    rw [hk, pow_add, pow_one, pow_mul]
    norm_num
    rw [Nat.mul_mod, Nat.pow_mod]
    norm_num
  have hmod' : (2 ^ n + 1) % 3 = 0 := by
    rw [Nat.add_mod, hmod]
  have : 3 ∣ 2 ^ n + 1 := by exact Nat.dvd_of_mod_eq_zero hmod'
  rcases this with ⟨i, hi⟩
  have isucc : 0 < i := by
    by_contra izero
    apply Nat.eq_zero_of_not_pos at izero
    rw [izero, mul_zero] at hi
    linarith
  apply Nat.exists_eq_add_one.mpr at isucc
  rcases isucc with ⟨j, hj⟩
  rw [hj] at hi
  simp [mul_add] at hi
  rw [hi, pow_add, pow_mul, h''', one_pow, one_mul, pow_two] at hcpow
  apply (mul_eq_right₀ hcnzero).mp at hcpow
  -- apply c=1 to 1+c^2+c=1, we get 3=0. But Char F=2, so 1=0, a contradiction
  rw [hcpow] at h'
  simp at h'
  rw [one_add_one_eq_two] at h'
  rw [CharTwo.two_eq_zero] at h'
  simp at h'
  exact pow_ne_zero 2 ha
  -- same for b≠0
  by_contra hb
  have h' : (a ^ 2 + b ^ 2 + a * b) / b ^ 2 = 0 := by
    rw [h]
    exact zero_div (b ^ 2)
  rw [add_div, add_div, div_self, ← div_pow, pow_two b, mul_div_mul_right a b hb] at h'
  set c := a / b with hc
  have h'' : (c ^ 2 + 1 + c) * (c - 1) = 0 := by
    rw [h', zero_mul]
  have h''' : c ^ 3 - 1 = (c ^ 2 + 1 + c) * (c - 1) := by
    ring
  rw [h'', sub_eq_zero] at h'''
  have hcnzero : c ≠ 0 := by
    by_contra hczero
    rw [hczero] at h'''
    simp at h'''
  -- Since F is a finite field with cardinality 2^n, c^{2^n}=c
  have hcpow : c ^ (2 ^ n) = c := by
    rw [← hcard]
    exact FiniteField.pow_card c
  rcases hn with ⟨k, hk⟩
  -- since n is odd and 3 ∣ 2^n-2, c^2=c, so c=1.
  have hmod : 2 ^ n % 3 = 2 := by
    rw [hk, pow_add, pow_one, pow_mul]
    norm_num
    rw [Nat.mul_mod, Nat.pow_mod]
    norm_num
  have hmod' : (2 ^ n + 1) % 3 = 0 := by
    rw [Nat.add_mod, hmod]
  have : 3 ∣ 2 ^ n + 1 := by exact Nat.dvd_of_mod_eq_zero hmod'
  rcases this with ⟨i, hi⟩
  have isucc : 0 < i := by
    by_contra izero
    apply Nat.eq_zero_of_not_pos at izero
    rw [izero, mul_zero] at hi
    linarith
  apply Nat.exists_eq_add_one.mpr at isucc
  rcases isucc with ⟨j, hj⟩
  rw [hj] at hi
  simp [mul_add] at hi
  rw [hi, pow_add, pow_mul, h''', one_pow, one_mul, pow_two] at hcpow
  apply (mul_eq_right₀ hcnzero).mp at hcpow
  -- apply c=1 to 1+c^2+c=1, we get 3=0. But Char F=2, so 1=0, a contradiction
  rw [hcpow] at h'
  simp at h'
  rw [one_add_one_eq_two] at h'
  rw [CharTwo.two_eq_zero] at h'
  simp at h'
  exact pow_ne_zero 2 hb


/-! Informal proof:
If a≠0, then (a^2+b^2+ab)/a^2=1+c^2+c=0, where c=b/a, and c^3-1=0.
Since F is a finite field with cardinality 2^n, c^{2^n}=c.
Since n is odd and 3 | 2^n-2, c^2=c, so c=1.
Apply c=1 to 1+c^2+c=1, we get 3=0. But Char F=2, so 1=0, a contradiction.
Same for b≠0.
-/
