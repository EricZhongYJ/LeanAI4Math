import Mathlib
/-! Question:
Suppose $m,n$ are two coprime positive integers. 
If group $G$ of order $mn$ has normal subgroup $H_1,H_2$ of order $m,n$. Then $G\cong H_1\times H_2$.
-/
variable {G : Type*} [Group G] { H1 H2 : Subgroup G}   
noncomputable section QuotientGroup
open MonoidHom 
open Subgroup
-- Lemma:Given two subgroups `H1` and `H2` of a group `G`, if the cardinalities of `H1` and `H2`thenH1 ⊓ H2 = trivial subgroup 
lemma inf_bot_of_coprime {G : Type*} [Group G] (H1 H2 : Subgroup G)
    (h : (Nat.card H1).Coprime (Nat.card H2)) : Disjoint H1 H2 := by
  unfold Disjoint
  have D₁ : Nat.card (H1 ⊓ H2 : Subgroup G) ∣ Nat.card H1 := card_dvd_of_le inf_le_left
  have D₂ : Nat.card (H1 ⊓ H2 : Subgroup G) ∣ Nat.card H2 := card_dvd_of_le inf_le_right
  have inter_bot : H1 ⊓ H2 = ⊥ :=(inf_eq_bot_of_coprime h)
  intro x h1x h2x
  rw [← inter_bot]
  exact le_inf h1x h2x
-- Lemma: Under the finite group G and the given condition h', prove that the order of G/H1 is equal to the order of H2
lemma aux_card_eq [Finite G] (h' : Nat.card G = Nat.card H1 * Nat.card H2) :
    Nat.card (G ⧸ H1) = Nat.card H2 := by
  have := calc
    Nat.card (G ⧸ H1) * Nat.card H1 = Nat.card G := by rw [← H1.index_eq_card, H1.index_mul_card]
    _                             = Nat.card H2 * Nat.card H1 := by rw [h', mul_comm]
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos this
variable [H1.Normal] [H2.Normal] [Fintype G] (h : Disjoint H1 H2)
  (h' : Nat.card G = Nat.card H1 * Nat.card H2)
-- Define the function iso₁: construct a multiplicative equivalence (isomorphism) from H2 to G/H1
def iso₁ [Fintype G] (h' : Nat.card G = Nat.card H1 * Nat.card H2) : H2 ≃* G ⧸ H1 := by
  apply MulEquiv.ofBijective ((QuotientGroup.mk' H1).restrict H2)
  rw [Nat.bijective_iff_injective_and_card]
  constructor
  · rw [← ker_eq_bot_iff, (QuotientGroup.mk' H1).ker_restrict H2]
    simp [h]
  · symm
    exact aux_card_eq h'
-- Define the function iso₂: construct a multiplicative equivalence (isomorphism) from G to (G/H2)×(G/H1)
def iso₂ : G ≃* (G ⧸ H2) × (G ⧸ H1) := by
  apply MulEquiv.ofBijective <| (QuotientGroup.mk' H2).prod (QuotientGroup.mk' H1)
  rw [Nat.bijective_iff_injective_and_card]
  constructor
  · rw [← ker_eq_bot_iff, ker_prod]
    simp [h.symm.eq_bot]
  · rw [Nat.card_prod]
    rw [aux_card_eq h', aux_card_eq (mul_comm (Nat.card H1) _▸ h'), h']
-- Define finalIso: construct a multiplicative equivalence (isomorphism) from G to H1×H2
def finalIso : G ≃* H1 × H2 :=
  (iso₂ h h').trans ((iso₁ h.symm (mul_comm (Nat.card H1) _ ▸ h')).prodCongr (iso₁ h h')).symm
end QuotientGroup
