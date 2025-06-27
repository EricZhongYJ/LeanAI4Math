import Mathlib
/-! Question:
3. Prove that an algebraically closed field must be infinite.
-/
import Mathlib.Tactic
open Polynomial

/- Any algebraically closed field is infinite -/

instance {K : Type*} [Field K] [IsAlgClosed K] : Infinite K := by
  -- assume that K is finite
  apply Infinite.of_not_fintype
  intro hfin
  -- set the cardinality of K to be n
  set n := Fintype.card K
  -- let f(x)=x^{n+1}-1. Given that K is algebraically closed, f is separable, a contradiction
  set f := (X : K[X]) ^ (n + 1) - 1
  have hfsep : Separable f := by
    apply separable_X_pow_sub_C
    simp [n]
    exact one_ne_zero
  apply Nat.not_succ_le_self (Fintype.card K)
  -- since f is separable, f has n+1 roots in K, contradicting that K has siez n
  have hroot : n.succ = Fintype.card (f.rootSet K) := by
    erw [card_rootSet_eq_natDegree hfsep (IsAlgClosed.splits_domain _), natDegree_X_pow_sub_C]
  rw [hroot]
  exact Fintype.card_le_of_injective _ Subtype.coe_injective


/-! Informal proof:
Assume that K is finite. 
Let f(x)=x^{n+1}-1. Given that K is algebraically closed, f is separable, and hence f has n+1 roots in K.
But this contradicts that K has size n.
-/
