import Mathlib
/-! Question:
3.2.5. 设 $F$ 为域, $c \in F, p$ 为素数. 求证: $x^{p}-c$ 在 $F[x]$ 中不可约 $\Longleftrightarrow x^{p}-c$在 $F$ 中无根.
-/
import Mathlib.Tactic
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.BigOperators.Ring

/- Let c be in the field F, p prime. Then x^p-c is irreducible in F[x] iff it has no root in F -/

open Polynomial

example {F : Type*} [Field F] (p : ℕ) (hprime : Nat.Prime p) (c : F) : Irreducible (X ^ p - C c) ↔ (roots (X ^ p - C c) = 0) := by
  have Pmonic := monic_X_pow_sub_C c (Prime.ne_zero (Nat.prime_iff.mp hprime))
  have Pnezero := Monic.ne_zero Pmonic
  have Pdeg : natDegree (X ^ p - C c) = p := by exact natDegree_X_pow_sub_C
  let K := AlgebraicClosure F
  constructor
  -- the forward direction is trivial
  intro irre
  by_contra nonempty
  apply Multiset.exists_mem_of_ne_zero at nonempty
  rcases nonempty with ⟨a, ha⟩
  have mid : X - C a ∣ X ^ p - C c := by
    refine dvd_iff_isRoot.mpr ?_
    exact isRoot_of_mem_roots ha
  rcases mid with ⟨g, hg⟩
  have mid1 : IsUnit (X - C a) ∨ IsUnit g := by exact irre.isUnit_or_isUnit' (X - C a) g hg
  have mid2 : ¬ IsUnit (X - C a) := by exact not_isUnit_X_sub_C a
  have mid3 : IsUnit g := by
    by_contra nunitg
    absurd mid1
    push_neg
    exact Classical.not_imp.mp fun a => nunitg (a mid2)
  have mid4 : natDegree g = 0 := by exact natDegree_eq_zero_of_isUnit mid3
  have mid5 : natDegree ((X - C a) * g) = natDegree (X - C a) + natDegree g := by
    refine natDegree_mul ?hp ?hq
    exact X_sub_C_ne_zero a
    exact IsUnit.ne_zero mid3
  have mid6 : natDegree (X - C a) = 1 := by exact natDegree_X_sub_C a
  rw [hg.symm, mid4, add_zero, Pdeg, mid6] at mid5
  have mid7 : p ≠ 1 := by exact Nat.Prime.ne_one hprime
  exact mid7 mid5
  -- now assume that P = f * g where 0 < deg(f) = n < p and f is monic. We show that P has a root in F. To do this, let K be the algebraic closure of F, and we show that f splits in K, that is, f factors into linear polynomials over K.
  intro rootempty
  by_contra re
  have mid1 : ∃ f g : F[X], X ^ p - C c = f * g ∧ ¬ IsUnit f ∧ ¬ IsUnit g := by
    by_contra h1
    push_neg at h1
    have h2 : ∀ (a b : F[X]), X ^ p - C c = a * b → IsUnit a ∨ IsUnit b := by
      intro a b hab
      by_contra h'1
      push_neg at h'1
      exact h'1.2 (h1 a b hab h'1.1)
    have h3 : ¬ IsUnit (X ^ p - C c) := by
      refine not_isUnit_of_degree_pos (X ^ p - C c) ?hpl
      refine natDegree_pos_iff_degree_pos.mp ?hpl.a
      rw [Pdeg]
      exact Nat.Prime.pos hprime
    have contra := Irreducible.mk h3 h2
    exact (re contra)
  rcases mid1 with ⟨f'', g, ⟨Pfg, ⟨f''nu, gnu⟩⟩⟩
  let f := (f'' * C (f''.leadingCoeff)⁻¹)
  have fnezero : f ≠ 0 := by
    by_contra feqzero
    dsimp [f] at feqzero
    have h1 : f'' * C (f''.leadingCoeff)⁻¹ * C f''.leadingCoeff = 0 := by rw [feqzero]; exact zero_mul (C f''.leadingCoeff)
    have h2 : f''.leadingCoeff⁻¹ * f''.leadingCoeff = 1 := by
      rw [mul_comm]
      refine CommGroupWithZero.mul_inv_cancel f''.leadingCoeff ?_
      refine leadingCoeff_ne_zero.mpr ?_
      by_contra f''eqzero; rw [f''eqzero, zero_mul] at Pfg; exact Pnezero Pfg
    have h3 : C (1 : F) = 1  := by exact rfl
    rw [mul_assoc, C_mul.symm, h2, h3, mul_one] at h1
    rw [h1, zero_mul] at Pfg
    exact (Pnezero Pfg)
  have fmonic : f.leadingCoeff = 1 := by
    refine Monic.def.mpr ?_
    have f''nezero : f'' ≠ 0 := by
      by_contra f''eqzero
      have feqzero : f = 0 := by dsimp [f]; rw [f''eqzero, zero_mul]
      exact fnezero feqzero
    have h2 := @leadingCoeff_mul F _ _ f'' (C (f''.leadingCoeff)⁻¹)
    dsimp [f]
    rw [h2, leadingCoeff_C, Field.mul_inv_cancel]
    exact (@leadingCoeff_ne_zero F _ f'').mpr f''nezero
  --f'' is the lift of f from F[X] into K[X].
  let f' := map (algebraMap F K) f
  have f'monic : Monic f' := by
    dsimp [f']
    exact Polynomial.Monic.map (algebraMap F K) fmonic
  -- f splits over K
  have fsplit : Splits (algebraMap F K) f := @IsAlgClosed.splits_codomain K F _ _ _ (algebraMap F K) f
  have cardrootsf := @natDegree_eq_card_roots' F K _ _ f (algebraMap F K) fsplit
  have ffactors := @C_leadingCoeff_mul_prod_multiset_X_sub_C K _ _ f' cardrootsf.symm
  have fccoe : ((C f'.leadingCoeff) * (Multiset.map (fun a => X - C a) f'.roots).prod).coeff 0 = f'.coeff 0 := by
    rw [ffactors]
  rw [mul_coeff_zero, coeff_C_zero, f'monic, one_mul, @coeff_zero_multiset_prod K _ (Multiset.map (fun a => X - C a) f'.roots)] at fccoe
  simp at fccoe
  -- compute f'.roots.prod ^ p = ∏ x : f'.roots, x ^ p = ∏ x, c = c ^ deg(f)
  have listprod := (Multiset.prod_toList f'.roots).symm
  let funlist := List.get (Multiset.toList f'.roots)
  rw [Eq.symm (List.ofFn_get f'.roots.toList), List.prod_ofFn] at listprod
  have eq1 := @Finset.prod_pow (Fin f'.roots.toList.length) K _ (@Finset.univ (Fin f'.roots.toList.length) _) p funlist
  have eq2 : ∀ x : (Fin f'.roots.toList.length), (fun (x : (Fin f'.roots.toList.length)) => funlist x ^ p) x = (fun (_ : (Fin f'.roots.toList.length)) => ((algebraMap F K) c)) x := by
    intro x
    have mid : funlist x ∈ f'.roots := by
      apply Multiset.mem_toList.mp
      dsimp [funlist]
      exact List.getElem_mem x.isLt
    have mid2 : f' ∣ map (algebraMap F K) (X ^ p - C c) := by
      refine Polynomial.map_dvd (algebraMap F K) ?_
      dsimp [f]
      use g * C f''.leadingCoeff
      have mid3 : f''.leadingCoeff ≠ 0 := by
        refine leadingCoeff_ne_zero.mpr ?_
        by_contra contra
        dsimp [f] at fnezero
        rw [contra, zero_mul] at fnezero
        contradiction
      have mid4 := @Field.mul_inv_cancel F _ f''.leadingCoeff mid3
      rw [mul_comm] at mid4
      rw [Pfg, mul_comm g, ← mul_assoc, mul_assoc f'', ← C_mul, mid4]
      simp
    have mid3 : funlist x ∈ (map (algebraMap F K) (X ^ p - C c)).roots := by
      have := @roots.le_of_dvd K _ _ f' (map (algebraMap F K) (X ^ p - C c)) (map_monic_ne_zero Pmonic) mid2
      exact Multiset.mem_of_le this mid
    apply (mem_roots_iff_aeval_eq_zero (map_monic_ne_zero Pmonic)).mp at mid3
    simp at mid3
    apply eq_of_sub_eq_zero
    exact mid3
  rw [Fintype.prod_congr (fun (x : (Fin f'.roots.toList.length)) => funlist x ^ p) (fun (_ : (Fin f'.roots.toList.length)) => ((algebraMap F K) c)) eq2] at eq1
  simp at eq1
  rw [cardrootsf.symm, Monic.natDegree_map fmonic (algebraMap F K), natDegree_mul_leadingCoeff_self_inv f''] at eq1
  -- since 0 < deg(f) < p and p is a prime, by bezout theorem, there exists a b such that 1 = a * deg(f) + b * p
  have Pfgdeg : (X ^ p - C c).natDegree = f''.natDegree + g.natDegree := by
    rw [congrArg natDegree Pfg]
    refine natDegree_mul ?_ ?_
    by_contra contra
    rw [contra, zero_mul] at Pfg
    contradiction
    by_contra contra
    rw [contra, mul_zero] at Pfg
    contradiction
  have bezout := Int.gcd_eq_gcd_ab (f''.natDegree) p
  simp at bezout
  have gcdone : f''.natDegree.gcd p = 1 := by
    have coprime : Nat.Coprime p f''.natDegree := by
      have zeroltdegf : 0 < f''.natDegree := by
        by_contra contra
        simp at contra
        have : IsUnit f'' := by
          apply isUnit_iff_degree_eq_zero.mpr
          have f''nezero : f'' ≠ 0 := by
            by_contra contra
            rw [contra, zero_mul] at Pfg
            contradiction
          apply (degree_eq_iff_natDegree_eq f''nezero).mpr
          exact contra
        contradiction
      have zeroltdegg : 0 < g.natDegree := by
        by_contra contra
        simp at contra
        have : IsUnit g := by
          apply isUnit_iff_degree_eq_zero.mpr
          have gnezero : g ≠ 0 := by
            by_contra contra
            rw [contra, mul_zero] at Pfg
            contradiction
          apply (degree_eq_iff_natDegree_eq gnezero).mpr
          exact contra
        contradiction
      have degfltp : f''.natDegree < p := by
        rw [Pdeg] at Pfgdeg
        rw [Pfgdeg]
        exact Nat.lt_add_of_pos_right zeroltdegg
      apply Nat.coprime_of_lt_prime zeroltdegf degfltp
      exact hprime
    exact Nat.coprime_comm.mp coprime
  rw [gcdone] at bezout
  -- f'.roots.prod is in F, denoted by z
  have zinF : ∃ z : F, f'.roots.prod = (algebraMap F K) z := by
    have mid : f'.coeff 0 = (algebraMap F K) (f.coeff 0) := by exact coeff_map (algebraMap F K) 0
    use (-1) ^ Multiset.card f'.roots * (f.coeff 0)
    simp
    rw [mid.symm, fccoe.symm]
    ring_nf
    rw [mul_comm (Multiset.card f'.roots), pow_mul, neg_one_pow_two, one_pow, mul_one]
  rcases zinF with ⟨z, hz⟩
  -- finally, (z ^ a * c ^ b) is a root of X ^ p - c in F, contradicting to our original assumption (roots (X ^ p - C c) = 0)
  have zval : (z ^ ((f''.natDegree : ℤ).gcdA (p : ℤ)) * c ^ ((f''.natDegree : ℤ).gcdB (p : ℤ))) ^ (p : ℤ) = c := by
    --have : (algebraMap F K) (z ^ ((f''.natDegree : ℤ).gcdA (p : ℤ)) * c ^ ((f''.natDegree : ℤ).gcdB (p : ℤ))) = (algebraMap F K) c := by sorry
    have inj := Algebra.botEquiv.proof_1 F K
    dsimp [Function.Injective] at inj
    apply inj
    have mid (r : F) (n : ℤ) := @algebraMap.coe_zpow F K _ _ _ r n
    have mid2 : @Algebra.cast F K Semifield.toCommSemiring DivisionSemiring.toSemiring (AlgebraicClosure.instAlgebra F) = (algebraMap F K) := by exact rfl
    rw [mid2] at mid
    have eq1' : (algebraMap F K) c ^ f''.natDegree = (∏ x : Fin f'.roots.toList.length, funlist x) ^ (p : ℤ) := by
      simp
      exact eq1
    rw [mid, map_mul, mul_zpow, ← mid, ← zpow_mul', zpow_mul, mid, mid, hz.symm, listprod, eq1'.symm]
    field_simp
    have : ((algebraMap F K) c ^ (f''.natDegree : ℤ)) ^ (f''.natDegree : ℤ).gcdA ↑p * ((algebraMap F K) c ^ (↑f''.natDegree : ℤ).gcdB ↑p) ^ (p : ℤ) = (algebraMap F K) c := by
      rw [← zpow_mul, ← zpow_mul, ← zpow_add', mul_comm ((f''.natDegree : ℤ).gcdB ↑p), bezout.symm, ← mid]
      simp
      right
      left
      rw [mul_comm ((f''.natDegree : ℤ).gcdB ↑p), bezout.symm]
      simp
    simp at this
    exact this
  apply Multiset.eq_zero_iff_forall_not_mem.mp at rootempty
  have root := rootempty (z ^ ((f''.natDegree : ℤ).gcdA (p : ℤ)) * c ^ ((f''.natDegree : ℤ).gcdB (p : ℤ)))
  absurd root
  refine mem_roots_sub_C'.mpr ?mpr.intro.intro.intro.intro.intro.a
  constructor
  by_contra contra
  rw [contra] at Pnezero
  simp at Pnezero
  simp
  simp at zval
  exact zval


/-! Informal proof:
We follow the top answer from https://math.stackexchange.com/questions/403924/xp-c-has-no-root-in-a-field-f-if-and-only-if-xp-c-is-irreducible
the forward direction is trivial;
for the backward direction we assume that P = f * g where 0 < deg(f) = n < p and f is monic. We show that P has a root in F. To do this, let K be the algebraic closure of F, and we show that f splits in K, that is, f factors into linear polynomials over K.

Let n := deg(f), then 0 < n < p. consider the product z of all the roots of f, clearly z \in F, and z ^ p = (z_1*...*z_n)^p = (z_1^p) *...* (z_n^p) = c^n. By Bezout's theorem, there is a, b such that an+bp = 1. Then (z^a * c^b)^p = c ^ {an+bp}=c, that is, z^a * c^p is a root of X^p - c in F.
-/
