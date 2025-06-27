import Mathlib
/-! Question:
3. Assume that $G$ is an abelian, transitive subgroup of $S_{A}$. Show that $\sigma(a) \
eq a$ for all $\sigma \in G-\{1\}$ and all $a \in A$. Deduce that $|G|=|A|$. 
-/

variable {A : Type*} {G : Subgroup (Equiv.Perm A)} [MulAction.IsPretransitive G A] [Subgroup.IsCommutative G]

lemma smul_eq_id_of_smul_eq : ∀ a : A, ∀ σ : G, σ • a = a → σ = 1 := by
  intro a σ hσ
  ext t
  -- We need to show that $\sigma(t) = t$ for all $t \in A$
  obtain ⟨τ, hτ⟩ := MulAction.exists_smul_eq G a t
  -- Since the action is transitive, there exists $\tau \in G$ such that $\tau(a) = t$
  rw [← hτ]
  show σ • τ • a = τ • a
  -- We need to show that $\sigma(\tau(a)) = \tau(a)$
  rw [← smul_assoc, smul_eq_mul, mul_comm, ← smul_eq_mul, smul_assoc, hσ]
  -- Since $G$ is abelian, $\sigma(\tau(a)) = \tau \sigma(a) = \tau(a)$, which completes the proof.


lemma smul_ne_id_implies_smul_ne : ∀ a : A, ∀ σ : G, σ ≠ (1 : G) → σ • a ≠ a := by
  intro a σ
  contrapose!
  exact smul_eq_id_of_smul_eq a σ
  -- The original problem is the contrapositive of the lemma smul_eq_id_of_smul_eq.

theorem card_eq [Nonempty A] : Nat.card G = Nat.card A := by
  let a := Classical.ofNonempty (α := A)
  -- Since A is nonempty, choose $a \in A$
  apply Nat.card_eq_of_bijective (f := fun σ ↦ σ • a)
  -- To show that the map $f : G \to A$, $\sigma \mapsto \sigma(a)$, is bijective
  constructor
  · intro σ τ feq
    -- Suppose $\sigma(a) = \tau(a)$
    have : τ⁻¹ • σ • a = a := by simp only [feq, inv_smul_smul τ a]
    -- This implies $\tau^{-1}(\sigma(a)) = a$
    have : τ⁻¹ • σ = 1 := smul_eq_id_of_smul_eq a (τ⁻¹ • σ) this
    -- By the previous lemma, $\tau^{-1} \circ \sigma = id$
    rwa [smul_eq_mul, inv_mul_eq_one, eq_comm] at this
    -- Hence, $\sigma = \tau$
  · intro b
    exact MulAction.exists_smul_eq G a b
    -- The map is surjective by the transitivity of the action.

/-! Informal proof:
We prove the contraposition prop as a lemma : 
>  **Lemma** : $\forall a \in A, \forall \sigma \in G, \sigma (a) = a \Rightarrow \sigma = id$
Proof of lemma : We need to show that $\sigma(t) = t$ for all $t \in A$
Since the action is transitive, there exists $\tau \in G$ such that $\tau(a) = t$
We need to show that $\sigma(\tau(a)) = \tau(a)$
Since $G$ is abelian, $\sigma(\tau(a)) = \tau \sigma(a) = \tau(a)$, which completes the proof.
The original problem is the contrapositive of this lemma.

>**Theorem** : If $A$ is nonempty, $|A|$ = $|G|$
Since A is nonempty, choose $a \in A$
To show that the map $f : G \to A$, $\sigma \mapsto \sigma(a)$, is bijective
Injective : Suppose $\sigma(a) = \tau(a)$
This implies $\tau^{-1}(\sigma(a)) = a$
By the previous lemma, $\tau^{-1} \circ \sigma = id$.
Hence, $\sigma = \tau$.
Surjective :  The map is surjective by the transitivity of the action.

-/
