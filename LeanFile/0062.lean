import Mathlib
/-! Question:
29. Let $p$ be a prime and let $G$ be a group of order $p^{\alpha}$. Prove that $G$ has a subgroup of order $p^{\beta}$, for every $\beta$ with $0 \leq \beta \leq \alpha$. [Use Theorem 8 and induction on $\alpha$.]
-/
/-Problem : Let $p$ be a prime and $G$ be a group of order $p^{\alpha}$. 
Prove that $G$ has a subgroup of order $p^{\beta}$ for every $\beta$ with $0\le \beta\le \alpha$.-/
example {G:Type*}[Fintype G][ Group G ](α :ℕ)(p :ℕ)(prime: Fact (p.Prime))(cardG: Nat.card G=p^α ):
∀(β : ℕ)(_: β≤α),∃(K : Subgroup G),(Nat.card K=p^β):=by
  intro β h
/-$0\le\beta\le\alpha$ implies $p^\beta\mid p^\alpha$-/
  have hdvd: p^β∣Nat.card G:=by
    rw[cardG]
    exact Nat.pow_dvd_pow p h
/-apply Sylow's first theorem on $G$ and $p^\beta$, 
concluding that $\exists $ subgroup $H$ of $G$ with order $p^\beta$.-/
  exact Sylow.exists_subgroup_card_pow_prime p hdvd

/-! Informal proof:
**Problem** Let $p$ be a prime and $G$ be a group of order $p^{\alpha}$. Prove that $G$ has a subgroup of order $p^{\beta}$ for every $\beta$ with $0\le \beta\le \alpha$.
**Proof**
Since $0\le\beta\le\alpha$ implies $p^\beta\mid p^\alpha$, we can apply Sylow's first theorem on $G$ and $p^\beta$, concluding that $\exists$ subgroup $H$ of $G$ with order $p^\beta$.This completes the proof.

-/
