import Mathlib
/-! Question:
17. Let $A$ be a nonempty set and let $X$ be any subset of $S_{A}$. Let
\[
F(X)=\{a \in A \mid \sigma(a)=a \text { for all } \sigma \in X\} \quad \text { - the fixed set of } X .
\]

Let $M(X)=A-F(X)$ be the elements which are moved by some element of $X$. Let $D=\left\{\sigma \in S_{A}|| M(\sigma) \mid<\infty\right\}$. Prove that $D$ is a normal subgroup of $S_{A}$.
-/


open Set Equiv

variable {A : Type*}

def F (σ : Perm A) : Set A := Function.fixedPoints σ

def M (σ : Perm A) : Set A := (F σ)ᶜ


@[simp]
lemma fixed_points_id : F (1 : Perm A) = univ := by simp only [F, Perm.coe_one, Function.fixedPoints_id]

@[simp]
lemma moved_points_id : M (1 : Perm A) = ∅ := by simp only [M, fixed_points_id, compl_univ]

@[simp]
lemma fixed_points_mem_iff (σ : Perm A) (a : A) : a ∈ F σ ↔ σ a = a := by rfl


lemma mul_subset_union (σ τ : Perm A) : M (σ * τ) ⊆ M σ ∪ M τ := by
  simp only [M, ← compl_inter (F σ) (F τ), compl_subset_compl]
  -- It suffices to show F(σ * τ) ⊆ F σ ∩ F τ
  rintro a ⟨h₁, h₂⟩
  simp only [fixed_points_mem_iff, Perm.coe_mul, Function.comp_apply]
  rw [h₂, h₁]
  -- Since $a \in F (\sigma) and a \in F(\tau), \sigma(\tau(a)) = \tau(a) = a$


lemma moved_points_inv_eq (σ : Perm A) : M σ = M σ⁻¹ := by
  simp only [M, compl_inj_iff]
  ext a
  simp only [fixed_points_mem_iff]
  -- It suffices to show $$a \in F(\sigma) \iff a \in F(\sigma^{-1})$$
  have := @Perm.eq_inv_iff_eq _ σ a a
  conv at this => lhs ; rw [eq_comm]
  exact this.symm
  -- It follows from $\sigma (a)= a \iff \sigma^{-1}(a) = a$.


instance D : Subgroup (Perm A) where
  carrier := {σ : Perm A | Finite (M σ)}
  mul_mem' := by
    intro σ τ hσ hτ
    simp only [finite_coe_iff, mem_setOf_eq]
    -- It suffices to show that $M(\sigma \tau)$ is finite.
    exact Finite.subset (Finite.union hσ hτ) (mul_subset_union σ τ)
    -- Since $M(\sigma \tau) \subseteq M (\sigma) \cup M (\tau)$ and $M(\sigma)$ and $M(\tau)$ are finite,
    -- $M(\sigma \tau)$ is finite.
  one_mem' := by
    simp only [mem_setOf_eq, moved_points_id]
    exact Finite.of_subsingleton
    -- Since $M(1)= \varnothing$, it is finite.
  inv_mem' := by
    intro σ hσ
    rwa [mem_setOf_eq, moved_points_inv_eq] at hσ
    -- Since $M(\sigma)= M (\sigma^{-1})$, $M (\sigma^{-1})$ is finite if $M(\sigma )$ is finite.


instance : D.Normal (G := Perm A) where
  conj_mem := by
    intro σ hσ τ
    have h : M (τ * σ * τ⁻¹) = τ '' M σ := by
      have : τ '' (F σ)ᶜ = (τ '' F σ)ᶜ := Equiv.image_compl τ (F σ)
      simp only [M, this, compl_inj_iff]
      -- Since $τ(F(\sigma))^c = (\tau F(\sigma))^c$,
      ext a
      -- it suffices to show that $a \in F(\tau \sigma \tau^{-1}) \iff a \in \tau F(\sigma)$.
      constructor
      · intro ha
        use τ⁻¹ a
        simp only [fixed_points_mem_iff, Perm.apply_inv_self, and_true]
        -- It suffices to show that $\tau^{-1}(a) \in F (σ)$ and $\tau(\tau^{-1}(a))=a$, and the latter is trivial.
        exact (@Perm.eq_inv_iff_eq _ τ (σ (τ⁻¹ a)) a).2 ha
        -- Since $a \in F(\tau \sigma \tau^{-1})$, $\sigma(\tau^{-1}(a)) = \tau^{-1}(a)$.
      · rintro ⟨x, h₁, h₂⟩
        rw [← h₂]
        simpa only [fixed_points_mem_iff, Perm.coe_mul, Function.comp_apply, Perm.inv_apply_self,
          EmbeddingLike.apply_eq_iff_eq]
        -- By definition, $\tau (F(\sigma)) \subset F(\tau * \sigma * \tau^{-1})$
    haveI : Finite (τ '' M σ) := @Finite.Set.finite_image _ _ (M σ) τ hσ
    -- As $M (\sigma)$ is finite, $\tau M(\sigma)$ is finite.
    show Finite (M (τ * σ * τ⁻¹))
    rwa [h]
    -- Hence, $M (\tau \sigma \tau^{-1}) = \tau M(\sigma)$ is finite.


/-! Informal proof:

> **Lemma 1** : $\forall \sigma, \tau \in S_A, M(\sigma \tau) \subseteq M (\sigma) \cup M (\tau)$
Proof :  It suffices to show $F(\sigma \tau) ⊆ F (\sigma) \cap F (\tau)$.
Since $a \in F (\sigma)$ and $a \in F(\tau), \sigma(\tau(a)) = \tau(a) = a$.
> **Lemma 2** : $\forall \sigma \in S_A, M(\sigma )= M (\sigma^{-1})$
Proof : It suffices to show $a \in F(\sigma) \iff a \in F(\sigma^{-1})$.
It follows from $\sigma (a)= a \iff \sigma^{-1}(a) = a$.

> **Theorem 1** : $D$ is a subgroup of $S_A$.
Proof : (i) $M(\sigma) \in D, M(\tau) \in D \Rightarrow  M(\sigma \tau) \in D :$ 
It suffices to show that $M(\sigma \tau)$ is finite.
Since $M(\sigma \tau) \subseteq M (\sigma) \cup M (\tau)$ and $M(\sigma)$ and $M(\tau)$ are finite, $M(\sigma \tau)$ is finite.
(ii) $M(1) \in D :$ Since $M(1)= \varnothing$, it is finite. 
(iii)  $M(\sigma^{-1}) \in D :$ Since $M(\sigma)= M (\sigma^{-1})$, 
$M (\sigma^{-1})$ is finite if $M(\sigma )$ is finite. 

> **Theorem 2** : $D$ is a normal subgroup of $S_A$.
Proof : Firstly, we show $M(\tau\sigma\tau^{-1})=\tau M(\sigma)$
Since $τ(F(\sigma))^c = (\tau F(\sigma))^c$, it suffices to show that $a \in F(\tau \sigma \tau^{-1}) \iff a \in \tau F(\sigma)$.
$\"\Longrightarrow \" :$ It suffices to show that $\tau^{-1}(a) \in F (σ)$ and $\tau(\tau^{-1}(a))=a$, and the latter is trivial. 
Since $a \in F(\tau \sigma \tau^{-1})$, $\sigma(\tau^{-1}(a)) = \tau^{-1}(a)$. 
As $M (\sigma)$ is finite, $\tau M(\sigma)$ is finite.
Hence, $M (\tau \sigma \tau^{-1}) = \tau M(\sigma)$ is finite.



-/
