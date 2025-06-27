import Mathlib
/-! Question:
15. (a) Suppose $G$ is a finite group and $a \in G$. Show that $a^{|G|}=1$.
(b) Now provide another proof for Fermat's Little Theorem 8.7: If $p$ is prime and $0<x<p$, then $x^{p-1} \equiv 1(\bmod p)$.
(c) For any positive integer $n, \phi(n)$ is defined to be the number of positive integers less than $n$ that are also relatively prime to $n$. (This is called Euler's phi function.) So, $\phi(6)=2$ because only 1 and 5 are less than 6 and also relatively prime to 6 . Note that if $p$ is prime, $\phi(p)=p-1$. Show that if $a$ is relatively prime to $n$, then
\[
a^{\phi(n)}=1(\bmod n) .
\]

This generalization of Fermat's Little Theorem 8.7 is called Euler's Theorem.
-/

open Nat

-- **Question(a)** Suppose $G$ is a finite group and $a\in G$. Show that $a^{|G|}=1$.
theorem Qa {G : Type*} [Group G] [Fintype G] (a : G) : a ^ Fintype.card G = 1 := by
  -- **Solution(a)** This is a standard result in Mathlib which can be proved by coset decomposition.
  exact pow_card_eq_one

-- **Question(b)** If $p$ is prime and $0 < x < p$, then $x^{p-1}\equiv 1\pmod{p}$.
theorem Qb {p : ℕ} (hp : p.Prime) {x : ℕ} (hx : 0 < x ∧ x < p) : x ^ (p - 1) ≡ 1 [MOD p] := by
  -- **Solution(b)** We transform the statement in terms of `ZMod p`.
  rw [← ZMod.eq_iff_modEq_nat]
  push_cast
  have : Fact p.Prime := ⟨hp⟩
  have : (x : ZMod p) ≠ 0 := by
    rw [← ZMod.val_ne_zero, ZMod.val_natCast, Nat.mod_eq_of_lt hx.2]
    exact hx.1.ne'
  -- Then this is a standard result in Mathlib which is obvious since the order of $\mathbb{Z}_p^{\times}$ is $p-1$.
  exact ZMod.pow_card_sub_one_eq_one this

-- **Question(c)** For any given positive integer $n$, show that if $a$ is relatively prime to $n$, then $a^{\phi(n)}\equiv 1\pmod{n}$.
theorem Qc {a n : ℕ} (h : Nat.Coprime a n) : a ^ φ n ≡ 1 [MOD n] := by
  -- **Solution(c)** This is a standard result in Mathlib which is obvious since the order of $\mathbb{Z}_n^{\times}$ is $\phi(n)$.
  exact Nat.ModEq.pow_totient h


/-! Informal proof:
**Question(a)** Suppose $G$ is a finite group and $a\in G$. Show that $a^{|G|}=1$.
**Solution(a)** This is a standard result in Mathlib which can be proved by coset decomposition.
**Question(b)** If $p$ is prime and $0 < x < p$, then $x^{p-1}\equiv 1\pmod{p}$.
**Solution(b)** We transform the statement in terms of `ZMod p`. Then this is a standard result in Mathlib which is obvious since the order of $\mathbb{Z}_p^{\times}$ is $p-1$.
**Question(c)** For any given positive integer $n$, show that if $a$ is relatively prime to $n$, then $a^{\phi(n)}\equiv 1\pmod{n}$.
**Solution(c)** This is a standard result in Mathlib which is obvious since the order of $\mathbb{Z}_n^{\times}$ is $\phi(n)$.
-/
