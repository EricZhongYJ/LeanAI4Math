import Mathlib
/-! Question:
17. Let $f(x)$ be an irreducible polynomial of degree $n$ over a field $F$. Let $g(x)$ be any polynomial in $F[x]$. Prove that every irreducible factor of the composite polynomial $f(g(x))$ has degree divisible by $n$.
-/

open Polynomial IntermediateField

/-Suppose $p$ is a irreducible factor of $f(g(x))$.-/
lemma exercise_1441 {K : Type u} [Field K] {f g p : K[X]} (hf : Irreducible f) 
    (hp : Irreducible p) (dvd : p ∣ f.comp g) : f.natDegree ∣ p.natDegree := by 
  have pdne : p.degree ≠ 0 := 
    fun h ↦ (lt_self_iff_false 0).mp <| h ▸ natDegree_pos_iff_degree_pos.mp hp.natDegree_pos
  /-Suppose $\alpha$ is the root of $p$ in the closure of $K$.-/
  obtain ⟨α, eq⟩ := IsAlgClosed.exists_aeval_eq_zero (AlgebraicClosure K) p pdne 
  obtain ⟨q, hq⟩ := dvd
  /-Then $f(g(\alpha))=0$, thus $\beta=g(\alpha)$ is a root of f.-/
  have eq' : (f.comp g).aeval α = 0 := by rw [hq, mul_comm, map_mul, eq, mul_zero]
  rw [aeval_comp] at eq'
  set β := g.aeval α
  /-We have $K \le K[\beta] \le K[\alpha]$.-/
  have leb: ⊥ ≤ K⟮β⟯ := OrderBot.bot_le _
  have blea: K⟮β⟯ ≤ K⟮α⟯ := adjoin_simple_le_iff.mpr <| 
    (mem_adjoin_simple_iff K (g.aeval α)).mpr ⟨g, 1, by rw [map_one, div_one]⟩
  have inta : IsIntegral K α := Algebra.IsIntegral.isIntegral α
  have intb : IsIntegral K β := Algebra.IsIntegral.isIntegral β
  /-So $[K[\alpha]:K]=[K[\alpha]:K[\beta]]*[K[\beta]:K]$, i.e. $\deg(p)=[K[\alpha]:K[\beta]]*\deg(f)$.-/
  have mul := relfinrank_mul_relfinrank leb blea
  repeat rw [relfinrank_bot_left] at mul
  rw [adjoin.finrank inta, adjoin.finrank intb, 
    ← minpoly.eq_of_irreducible hp eq, ← minpoly.eq_of_irreducible hf eq'] at mul
  have nefl := inv_ne_zero <| leadingCoeff_ne_zero.mpr hf.ne_zero
  have nepl := inv_ne_zero <| leadingCoeff_ne_zero.mpr hp.ne_zero
  rw [natDegree_mul_C nefl, natDegree_mul_C nepl] at mul
  /-Thus $\deg(f) \dvd \deg(p)$.-/
  exact ⟨K⟮β⟯.relfinrank K⟮α⟯, mul.symm⟩ 


/-! Informal proof:
Suppose $p$ is a irreducible factor of $f(g(x))$.
Suppose $\alpha$ is the root of $p$ in the closure of $K$.
Then $f(g(\alpha))=0$, thus $\beta=g(\alpha)$ is a root of f.
We have $K \le K[\beta] \le K[\alpha]$.So $[K[\alpha]:K]=[K[\alpha]:K[\beta]]*[K[\beta]:K]$, i.e. $\deg(p)=[K[\alpha]:K[\beta]]*\deg(f)$.
Thus $\deg(f) \mid \deg(p)$.
-/
