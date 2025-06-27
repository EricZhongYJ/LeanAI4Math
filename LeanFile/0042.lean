import Mathlib
/-! Question:
14. Let $f \in \mathbb{Z}[x]$ and $n$ an integer. Let $g$ be the polynomial defined by $g(x)=f(x+n)$. Prove that $f$ is irreducible in $\mathbb{Z}[x]$ if and only if $g$ is irreducible in $\mathbb{Z}[x]$.
-/

open Polynomial

-- For the if part, suppose $f$ is irreducible. we verify that $g$ is irreducible by checking definition.
lemma Polynomial.irreducbile_of_add_n_irreducible {f g : ℤ[X]} {n : ℤ}
    (hfg : g = f.comp (X + C n)) (hf : Irreducible f) : Irreducible g := by
  rcases hf with ⟨hfnu, hf⟩
  constructor
  -- (1) $g$ is not unit.
  . intro hg
    -- Since $f$ is irreducible, $f$ is not unit. Thus $g(x)=f(x+n)$ is not unit.
    rw [isUnit_iff] at hg
    rcases hg with ⟨r, hr ,hrg⟩
    apply_fun (·.comp (X + C (-n))) at hrg
    rw [hfg, comp_assoc] at hrg
    simp at hrg
    have : IsUnit f := by
      rw [isUnit_iff]
      use r
      exact ⟨hr, by convert hrg⟩
    contradiction
  -- (2) If $g(x)=a(x)b(x)$, then $a(x)$ or $b(x)$ is unit.
  intro a b hab
  -- Substitute $g(x)=f(x+n)$ gives $f(x+n)=a(x)b(x)$. Transform this to $f(x)=a(x-n)b(x-n)$.
  apply_fun (·.comp (X + C (-n))) at hab
  rw [hfg, comp_assoc, mul_comp] at hab
  simp at hab
  specialize hf _ _ hab
  -- Since $f$ is irreducible, we have $a(x-n)$ or $b(x-n)$ is unit. Hence $a(x)$ or $b(x)$ is unit.
  rcases hf with hf | hf
  . rw [isUnit_iff] at hf
    rcases hf with ⟨r, hr, hra⟩
    apply_fun (·.comp (X + C n)) at hra
    rw [comp_assoc] at hra
    simp at hra
    left
    rw [isUnit_iff]
    use r
    exact ⟨hr, by convert hra⟩
  rw [isUnit_iff] at hf
  rcases hf with ⟨r, hr, hrb⟩
  apply_fun (·.comp (X + C n)) at hrb
  rw [comp_assoc] at hrb
  simp at hrb
  right
  rw [isUnit_iff]
  use r
  exact ⟨hr, by convert hrb⟩

-- **Question:** Prove that $f(x)$ is irreducible in $\mathbb{Z}[x]$ if and only if $g(x)=f(x+n)$ is irreducible in $\mathbb{Z}[x]$.
theorem Polynomial.irreducible_iff_add_n_irreducible {f g : ℤ[X]} {n : ℤ}
    (hfg : g = f.comp (X + C n)) : Irreducible f ↔ Irreducible g := by
  -- **Solution:** We split into if part and only if part.
  constructor
  . intro hf
    exact irreducbile_of_add_n_irreducible hfg hf
  -- The only if part is obvious since $f(x)=g(x+(-n))$.
  intro hg
  have hgf : f = g.comp (X + C (-n)) := by rw [hfg, comp_assoc]; simp
  exact irreducbile_of_add_n_irreducible hgf hg

/-! Informal proof:
**Question:** Prove that $f(x)$ is irreducible in $\mathbb{Z}[x]$ if and only if $g(x)=f(x+n)$ is irreducible in $\mathbb{Z}[x]$.
**Solution:** We split into if part and only if part.
For the if part, suppose $f$ is irreducible. we verify that $g$ is irreducible by checking definition.
(1) $g$ is not unit. 
Since $f$ is irreducible, $f$ is not unit. Thus $g(x)=f(x+n)$ is not unit.
(2) If $g(x)=a(x)b(x)$, then $a(x)$ or $b(x)$ is unit. 
Substitute $g(x)=f(x+n)$ gives $f(x+n)=a(x)b(x)$. Transform this to $f(x)=a(x-n)b(x-n)$. 
Since $f$ is irreducible, we have $a(x-n)$ or $b(x-n)$ is unit. Hence $a(x)$ or $b(x)$ is unit.
The only if part is obvious since $f(x)=g(x+(-n))$.

-/
