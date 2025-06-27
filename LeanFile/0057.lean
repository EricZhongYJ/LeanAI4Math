import Mathlib
/-! Question:
5. Let $F$ be a finite field of order $p^{n}$. Show that $\operatorname{Gal}\left(F: \mathbb{Z}_{p}\right)$ is cyclic of order $p^{n-1}$.
-/
set_option maxHeartbeats 0

section UnexploredExercise_6803
namespace UnexploredExercise_6803

open Polynomial

variable (p : ℕ) [prime : Fact p.Prime] (n : ℕ)

noncomputable def frobeniusAlgEquiv : GaloisField p n ≃ₐ[ZMod p] GaloisField p n := by
  apply AlgEquiv.ofRingEquiv (f := frobeniusEquiv (GaloisField p n) p) (fun x => ?_)
  simp only [frobeniusEquiv_apply, Algebra.algebraMap_eq_smul_one, frobenius_def, _root_.smul_pow, ZMod.pow_card, one_pow]

/-- frobenius代数同构在GaloisField p n中的阶为 $n$.-/
theorem frobenius_order_eq_n (hn : n ≠ 0):
  orderOf (frobeniusAlgEquiv p n) = n := by  
  -- 一方面已经有 $♯(\mathrm{Gal}(\uD835\uDD3D_{p^n}:Z_p)) = n$.
  have : Fintype.card (GaloisField p n ≃ₐ[ZMod p] GaloisField p n) = n := by
    rw [IsGalois.card_aut_eq_finrank, GaloisField.finrank p hn]
  -- 由于$o(σ) ≤ ♯(\mathrm{Gal}(\uD835\uDD3D_{p^n}:Z_p)) = n$, 因此只需要说明 $n ≤ o(σ) =: r$.
  simp_rw [← this]
  apply le_antisymm (orderOf_le_card_univ)
  set σ := frobeniusAlgEquiv p n with hσ
  set r := orderOf σ
  -- 按照定义直接获得$σ^r(x) = id$,
  have sigma_id : ∀ x : GaloisField p n, x^(p^r) = x := by
    intro x
    have iter_pow : ∀ k : ℕ, (σ^k) x = x^(p^k) := by
      intro k
      induction' k with k hk
      . simp only [pow_zero, AlgEquiv.one_apply, pow_one]
      . show (σ^k * σ) x = _
        rw [pow_mul_comm', AlgEquiv.mul_apply, hk, hσ, frobeniusAlgEquiv]
        simp only [AlgEquiv.ofRingEquiv_apply, frobeniusEquiv_def]
        ring
    specialize iter_pow r
    simp only [pow_orderOf_eq_one σ, AlgEquiv.one_apply] at iter_pow
    exact iter_pow.symm
  -- 进而多项式 $g(x) := x^(p^r) - x$ 在 $\uD835\uDD3D_{p^n}$ 上恒为$0$, 因此至少有 $♯\uD835\uDD3D_{p^n} = p^n$ 个根, 于是$p^n ≤ g.deg = p^r$.
  have one_lt_p : 1 < p := (@Nat.Prime.one_lt p Fact.out)
  have h_roots : Nat.card (GaloisField p n) ≤ p^(orderOf σ) := by
    have zero_lt_r : 0 < r := orderOf_pos σ
    have one_le_p_pow_r : 1 < p^r := by 
      exact Nat.one_lt_pow zero_lt_r.ne.symm one_lt_p
    let poly := (X^(p^r) - X : (GaloisField p n)[X])
    have degree_eq : Polynomial.natDegree poly = p^r := by
      dsimp only [poly]
      compute_degree!
      . simp [one_le_p_pow_r.ne]
      . exact one_le_p_pow_r.le
    rw [← degree_eq, Nat.card_eq_fintype_card]
    apply Polynomial.card_le_degree_of_subset_roots (fun x _ => ?_)
    apply (mem_roots_iff_aeval_eq_zero ?_).mpr ?_
    . apply Polynomial.ne_zero_of_natDegree_gt (n := 1)
      simp only [degree_eq, Nat.one_lt_pow zero_lt_r.ne.symm one_lt_p]
    . simp only [coe_aeval_eq_eval, eval_sub, eval_pow, eval_X, poly, sigma_id, sub_eq_zero]
  rw [Nat.card_eq_fintype_card, GaloisField.card p n hn, pow_le_pow_iff_right one_lt_p] at h_roots
  exact this.symm ▸ h_roots

/-- $\mathrm{Gal}(\uD835\uDD3D_{p^n}:Z_p) = ⟨σ⟩$, 其中 $σ : \uD835\uDD3D_{p^n} ≃ₐ[ZMod p] \uD835\uDD3D_{p^n}, x ↦ x^p$.-/
theorem frobenius_generates (hn : n ≠ 0):
  (⊤ : Subgroup (GaloisField p n ≃ₐ[ZMod p] GaloisField p n)) = Subgroup.zpowers (frobeniusAlgEquiv p n):= by
  rw [eq_comm, ← Subgroup.card_eq_iff_eq_top, Nat.card_zpowers, Nat.card_eq_fintype_card]
  simp only [frobenius_order_eq_n p n hn, ← GaloisField.finrank p hn, ← IsGalois.card_aut_eq_finrank]

/-- $\mathrm{Gal}(\uD835\uDD3D_{p^n}:Z_p)$ 是循环群. -/
theorem frobenius_Galois_is_cyclic (hn : n ≠ 0):
  IsCyclic (GaloisField p n ≃ₐ[ZMod p] GaloisField p n) := by
    apply IsCyclic.mk ⟨frobeniusAlgEquiv p n, fun y ↦ ?_⟩
    simp only [← Subgroup.mem_zpowers_iff, ← ((Subgroup.ext_iff.1 (frobenius_generates p n hn)) y), Subgroup.mem_top]

end UnexploredExercise_6803
end UnexploredExercise_6803


/-! Informal proof:
1. 一方面已经有 $♯(\mathrm{Gal}(\uD835\uDD3D_{p^n}:Z_p)) = n$. 考虑说明 $\mathrm{Gal}(\uD835\uDD3D_{p^n}:Z_p) = ⟨σ⟩$, 其中 $σ : \uD835\uDD3D_{p^n} ≃ₐ[\mathrm{ZMod\ } p]\  \uD835\uDD3D_{p^n}, x ↦ x^p$.
2. 由于$o(σ) ≤ ♯(\mathrm{Gal}(\uD835\uDD3D_{p^n}:Z_p)) = n$, 因此只需要说明 $n ≤ o(σ) =: r$.
3. 按照定义直接获得$σ^r(x) = id$,进而多项式 $g(x) := x^{p^r} - x$ 在 $\uD835\uDD3D_{p^n}$ 上恒为$0$, 因此至少有 $n$ 个根, 于是$n ≤ g.deg = r$.
-/
