import Mathlib
/-! Question:
21. Let $G$ be a finite group and let $x$ be an element of $G$ of order $n$. Prove that if $n$ is odd, then $x=\left(x^{2}\right)^{k}$ for some $\mathrm{k}$.
-/

variable {G : Type*} [Group G] (x : G) {n : ℕ} (hn : Odd n)

example (h : orderOf x = n) : ∃ k : ℕ, x = (x ^ 2) ^ k := by
  obtain ⟨k, hk⟩ := hn
  --Since $n$ is odd, $\exists k, n = 2 k + 1$
  use k + 1
  --Next we prove that $x = (x ^ 2) ^ {k + 1}$
  have := hk ▸ h ▸ pow_orderOf_eq_one x
  --Since $|x| = n, x ^ {|x|} = x ^ n = x ^ {2k + 1} = 1$
  nth_rw 1 [← one_mul x, ← this]
  group
  --Then $x = x \cdot x ^ {2k + 1} = x ^ {2k + 2} = (x ^ 2) ^ {k + 1}$


/-! Informal proof:
Since $n$ is odd, $\exists \  k, n = 2 k + 1$
Next we prove that $x = (x ^ 2) ^ {k + 1}$
Since $|x| = n, x ^ {|x|} = x ^ n = x ^ {2k + 1} = 1$
Then $x = x \cdot x ^ {2k + 1} = x ^ {2k + 2} = (x ^ 2) ^ {k + 1}$
-/
