import Mathlib
/-! Question:
9. This exercise outlines a proof of Cauchy's Theorem due to James McKay (Another proof of Cauchy's group theorem, Amer. Math. Monthly, 66(1959), p. 119). Let $G$ be a finite group and let $p$ be a prime dividing $|G|$. Let $\mathcal{S}$ denote the set of $p$-tuples of elements of $G$ the product of whose coordinates is 1:
\[
\mathcal{S}=\left\{\left(x_{1}, x_{2}, \ldots, x_{p}\right) \mid x_{i} \in G \text { and } x_{1} x_{2} \cdots x_{p}=1\right\} .
\]
(Hint : 
Show that $\mathcal{S}$ has $|G|^{p-1}$ elements, hence has order divisible by $p$.
Define the relation $\sim$ on $\mathcal{S}$ by letting $\alpha \sim \beta$ if $\beta$ is a cyclic permutation of $\alpha$.
Show that a cyclic permutation of an element of $\mathcal{S}$ is again an element of $\mathcal{S}$.
Prove that $\sim$ is an equivalence relation on $\mathcal{S}$.
Prove that an equivalence class contains a single element if and only if it is of the form $(x, x, \ldots, x)$ with $x^{p}=1$.
)
(a) Prove that every equivalence class has order 1 or $p$ (this uses the fact that $p$ is a prime). Deduce that $|G|^{p-1}=k+p d$, where $k$ is the number of classes of size 1 and $d$ is the number of classes of size $p$.
(b) Since $\{(1,1, \ldots, 1)\}$ is an equivalence class of size 1 , conclude from (e) that there must be a nonidentity element $x$ in $G$ with $x^{p}=1$, i.e., $G$ contains an element of order $p$. [Show $p \mid k$ and so $k>1$ 1.]
-/
import Mathlib.Tactic

/- Cauchy's group theorem -/

example {G : Type*} [Group G] [Fintype G] {p : ℕ} (hprime : Nat.Prime p) (hdiv : p ∣ Fintype.card G) : ∃ x : G, x ^ p = 1 := by
  have cauchy := @exists_prime_orderOf_dvd_card G _ _ p { out := hprime } hdiv
  rcases cauchy with ⟨x, hx⟩
  use x
  refine orderOf_dvd_iff_pow_eq_one.mp ?h.a
  exact dvd_of_eq hx


/-! Informal proof:
use Mathlib theorem exists_prime_orderOf_dvd_card
-/
