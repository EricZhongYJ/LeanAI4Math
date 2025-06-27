import Mathlib
/-! Question:
11. Suppose as above that $\alpha$ is a real number, $p \in \mathbb{Q}[x]$ is irreducible, and $p(\alpha)=0$. Suppose also that $f \in \mathbb{Q}[x]$ with $f(\alpha)=0$. Prove that $p$ divides $f$.
-/

/-
$\alpha$ is a real number.$p \in \mathbb{Q}[x]$ is irreducible, and $p(\alpha) = 0$.
$f \in \mathbb{Q}[x]$ with $f(\alpha) = 0$.Prove: $p$ $\mid$ $f$.
1.Since $p(x)$ is an irreducible polynomial over $\mathbb{Q}$ and $p(\alpha) = 0$,
it means $p(x)$ is the minimal polynomial of $\alpha$ over $\mathbb{Q}$.
2.The minimal polynomial of a number has the property that any other polynomial with $\alpha$
 as a root must be divisible by this minimal polynomial.
3.Since $f(\alpha) = 0$, $f(x)$ has $\alpha$ as a root. Therefore, by the properties of
the minimal polynomial, $p(x)$ divides $f(x)$ in $\mathbb{Q}[x]$.
This completes the proof.
-/
lemma UnexploredExercise_3111 {α : ℝ} {p f : Polynomial ℚ} (Irreducible_p : Irreducible p) :
  (Polynomial.aeval α) p = 0 → (Polynomial.aeval α) f = 0 → p ∣ f :=

  fun p_roots f_roots ↦
  have : Associated p (minpoly ℚ (α : ℝ)) := by
    /-1.Since $p(x)$ is an irreducible polynomial over $\mathbb{Q}$ and $p(\alpha) = 0$,
    it means $p(x)$ is the minimal polynomial of $\alpha$ over $\mathbb{Q}$. -/
    have := (Irreducible.dvd_iff Irreducible_p).mp <| minpoly.dvd_iff.mpr p_roots
    have := minpoly.not_isUnit ℚ α
    /-2.The minimal polynomial of a number has the property that any other polynomial with $\alpha$
    as a root must be divisible by this minimal polynomial.-/
    tauto
  /-3.Since $f(\alpha) = 0$, $f(x)$ has $\alpha$ as a root. Therefore, by the properties of
  the minimal polynomial, $p(x)$ divides $f(x)$ in $\mathbb{Q}[x]$.
  This completes the proof.-/
  (Associated.dvd_iff_dvd_left <| id <| Associated.symm this).mp <| minpoly.dvd_iff.mpr f_roots


/-! Informal proof:
$\alpha$ is a real number.$p \in \mathbb{Q}[x]$ is irreducible, and $p(\alpha) = 0$.
$f \in \mathbb{Q}[x]$ with $f(\alpha) = 0$.Prove: $p$ $\mid$ $f$.
1.Since $p(x)$ is an irreducible polynomial over $\mathbb{Q}$ and $p(\alpha) = 0$,
it means $p(x)$ is the minimal polynomial of $\alpha$ over $\mathbb{Q}$.
2.The minimal polynomial of a number has the property that any other polynomial with $\alpha$
 as a root must be divisible by this minimal polynomial.
3.Since $f(\alpha) = 0$, $f(x)$ has $\alpha$ as a root. Therefore, by the properties of
the minimal polynomial, $p(x)$ divides $f(x)$ in $\mathbb{Q}[x]$.
This completes the proof.
-/
