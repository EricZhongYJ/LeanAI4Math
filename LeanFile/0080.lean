import Mathlib
/-! Question:
3.1.16. 设 $K$ 是域, $x$ 是 $K$ 上的超越元, $u \in K(x), u \
otin K$. 求证 $x$ 在域 $K(u)$ 上代数.
-/
import Mathlib.Tactic
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Monic

/- Let x be transcendental over K, u∈K(x), u∉K. Show that x is algebraic over K(u) -/

open Polynomial

example {F K: Type*} [Field F] [Field K] [Algebra K F] {x : F} {u : F} (h1 : u ∈ IntermediateField.adjoin K {x}) (h2 : ∀ a : K, a • 1 ≠ u) : IsAlgebraic (IntermediateField.adjoin K {u}) x := by
  rw [IntermediateField.mem_adjoin_simple_iff] at h1
  rcases h1 with ⟨f, g, hu⟩
  -- -- if the denominator g(u)=0, then u=0∈K, a contradiction
  if gevalnzero : (aeval (x)) g = 0 then
    simp [gevalnzero] at hu
    rw [hu]
    rw [hu] at h2
    have := h2 0
    simp at this
  -- else let p(X)=f(X)-ug(X) and prove that p≠0 ∧ p(x)=0
  else
    let f' := mapRingHom (algebraMap K (IntermediateField.adjoin K {u})) f
    let g' := mapRingHom (algebraMap K (IntermediateField.adjoin K {u})) g
    have uself : u ∈ (IntermediateField.adjoin K {u}) := by
      exact IntermediateField.mem_adjoin_simple_self K u
    let p := f' - C ⟨u, uself⟩ * g'
    -- p≠0, and the following are purely technical computations...
    have pnzero : p ≠ 0 := by
      by_contra pzero
      dsimp [p] at pzero
      have g'coeff : g'.coeff g.natDegree= (algebraMap K (IntermediateField.adjoin K {u})) (g.coeff g.natDegree):= by
        exact coeff_map (algebraMap K (IntermediateField.adjoin K {u})) g.natDegree
      have f'coeff : f'.coeff g.natDegree= (algebraMap K (IntermediateField.adjoin K {u})) (f.coeff g.natDegree):= by
        exact coeff_map (algebraMap K (IntermediateField.adjoin K {u})) g.natDegree
      apply sub_eq_zero.mp at pzero
      symm at pzero
      have ugfcoeff: (C (⟨u, uself⟩ : (IntermediateField.adjoin K {u})) * g').coeff g.natDegree = f'.coeff g.natDegree := by
        exact congrFun (congrArg coeff pzero) g.natDegree
      rw [coeff_C_mul g'] at ugfcoeff
      have g'coeffnzero : g'.coeff g.natDegree ≠ 0 := by
        rw [g'coeff]
        by_contra gcontra
        have gcoeff : g.coeff g.natDegree =g.leadingCoeff := by exact rfl
        have glcnzero : g.leadingCoeff ≠ 0 := by
          refine leadingCoeff_ne_zero.mpr ?_
          by_contra gzero
          rw [gzero] at gevalnzero
          rw [aeval_zero x] at gevalnzero
          contradiction
        rw [gcoeff] at gcontra
        apply (algebraMap.lift_map_eq_zero_iff g.leadingCoeff).mp at gcontra
        contradiction
      have ugfcoeff1 : (⟨u, uself⟩ : (IntermediateField.adjoin K {u})) = (f'.coeff g.natDegree) / (g'.coeff g.natDegree) := by
        exact eq_div_of_mul_eq g'coeffnzero ugfcoeff
      have urfl : u = (algebraMap (IntermediateField.adjoin K {u}) F) ⟨u, uself⟩ := by exact rfl
      rw [ugfcoeff1, g'coeff, f'coeff] at urfl
      simp at urfl
      have urfl1 : u = (algebraMap K F) ((f.coeff g.natDegree) / g.leadingCoeff) := by
        rw [urfl]
        exact Eq.symm (algebraMap.coe_div F (f.coeff g.natDegree) g.leadingCoeff)
      have urfl2 : u = (f.coeff g.natDegree / g.leadingCoeff) • 1 := by
        rw [urfl1]
        exact Algebra.algebraMap_eq_smul_one (f.coeff g.natDegree / g.leadingCoeff)
      exact h2 (f.coeff g.natDegree / g.leadingCoeff) (id (Eq.symm urfl2))
    use p
    constructor
    exact pnzero
    -- p(x)=0
    have urfl : u = (algebraMap (IntermediateField.adjoin K {u}) F) ⟨u, uself⟩ := rfl
    dsimp [p]
    have hu1 : u * (aeval x) g = (aeval x) f := by exact (eq_div_iff gevalnzero).mp hu
    have hu2 : (aeval x) f - u * (aeval x) g = 0 := by exact sub_eq_zero_of_eq (id (Eq.symm hu1))
    rw [urfl] at hu2
    have eq1 : (aeval x) (f' - C ⟨u, uself⟩ * g') = (aeval x) f' - (aeval x) (C ⟨u, uself⟩ * g') := by
      exact map_sub (aeval x) f' (C ⟨u, uself⟩ * g')
    rw [eq1]
    have eq2 : (aeval x) (C ⟨u, uself⟩ * g') = (aeval x) (C (⟨u, uself⟩ : (IntermediateField.adjoin K {u}))) * ((aeval x) g') := by
      exact aeval_mul x
    rw [eq2]
    rw [aeval_C, urfl.symm]
    have eq3 : (aeval x) f = (aeval x) f' := by
      dsimp [f']
      exact Eq.symm (aeval_map_algebraMap (IntermediateField.adjoin K {u}) x f)
    have eq4 : (aeval x) g = (aeval x) g' := by
      dsimp [g']
      exact Eq.symm (aeval_map_algebraMap (IntermediateField.adjoin K {u}) x g)
    rw [eq3.symm, eq4.symm, hu]
    field_simp


/-! Informal proof:
Let u=f(x)/g(x), then take p(X)=f(X)-ug(X) : K(u)[X] and verify that p(X)≠0, p(x)=0.
-/
