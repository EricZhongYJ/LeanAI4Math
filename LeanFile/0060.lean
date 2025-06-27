import Mathlib
/-! Question:
2. Prove that $C_{G}(Z(G))=G$ and deduce that $N_{G}(Z(G))=G$.
-/
import Mathlib.Algebra.Group.Center
import Mathlib.Tactic.Group
import Mathlib.Data.Set.Basic
--Prove that C_G(Z(G))=G and deduce that N_G(Z(G))=G.

variable {G : Type*} [Group G]

-- Prove that C_G(Z(G)) = G
theorem centralizer_center_eq_self : Set.centralizer (Set.center G) = (Set.univ: Set G) := by
  rw [Set.Subset.antisymm_iff]
  apply And.intro
  · -- we show that C_G(Z(G)) ⊆ G.
    show (Set.center G).centralizer ⊆ (Set.univ: Set G)
    -- This is trivial because C_G(Z(G)) is defined as a subset of G (it consists of elements of G that commute with elements of Z(G))
    exact fun _ _ ↦ trivial
  · -- we show that G ⊆ C_G(Z(G)).
    show (Set.univ: Set G) ⊆ (Set.center G).centralizer
    -- Take any element g ∈ G
    intro g _;
    -- by definition of centralizer, we need to show that g commutes with every element of Z(G)
    simp [Set.centralizer];
    show ∀ z ∈ Set.center G, z * g = g * z
    intro z hz
    -- By the definition of the center Z(G), every element z∈Z(G) commutes with g, i.e.,zg = gz.
    exact hz.comm g

-- Prove that C_G(Z(G)) = N_G(Z(G))
theorem centralizer_center_eq_normalizer_center: Set.centralizer (Set.center G) = (@Subgroup.setNormalizer G _ (Subgroup.center G)) := by
  -- By the definition of centralizer and normalizer, we need to show that g commutes with every element of Z(G) if and only if g normalizes Z(G).
  ext g
  simp [Set.centralizer, Subgroup.setNormalizer, Subgroup.center]
  show (∀ z ∈ Set.center G, z * g = g * z) ↔ ∀ (n : G), n ∈ Set.center G ↔ g * n * g⁻¹ ∈ Set.center G

  apply Iff.intro
  · -- We show that if g commutes with every element of Z(G), then g normalizes Z(G).
    show (∀ z ∈ Set.center G, z * g = g * z) → ∀ (n : G), n ∈ Set.center G ↔ g * n * g⁻¹ ∈ Set.center G
    intros h z
    apply Iff.intro
    · -- We show that if z ∈ Z(G), then g * z * g⁻¹ ∈ Z(G).
      show z ∈ Set.center G → g * z * g⁻¹ ∈ Set.center G
      specialize h z
      intro this
      simpa [←h this] using this
    · -- We show that if g * z * g⁻¹ ∈ Z(G), then z ∈ Z(G).
      show g * z * g⁻¹ ∈ Set.center G → z ∈ Set.center G
      specialize h (g * z * g⁻¹); simp at h;
      -- We need prove that g * z * g⁻¹ ∈ Z(G) implies z ∈ Z(G).
      show g * z * g⁻¹ ∈ Set.center G → z ∈ Set.center G
      intro this;
      simpa [←h this] using this
  · -- We show that if g normalizes Z(G), then g commutes with every element of Z(G).
    show (∀ (n : G), n ∈ Set.center G ↔ g * n * g⁻¹ ∈ Set.center G) → ∀ z ∈ Set.center G, z * g = g * z
    intro h z hz
    -- By the definition of the center Z(G), every element z∈Z(G) commutes with g, i.e.,zg = gz.
    exact hz.comm g


-- Deduce that N_G(Z(G)) = G
theorem normalizer_center_eq_self: @Subgroup.setNormalizer G _ (Subgroup.center G) = (Set.univ: Set G) := by
  rw [←centralizer_center_eq_normalizer_center]
  rw [centralizer_center_eq_self]


/-! Informal proof:
## theorem centralizer_center_eq_self
Prove that $C_G(Z(G)) = G$:
we show that $C_G(Z(G)) ⊆ G$.
This is trivial because $C_G(Z(G))$ is defined as a subset of $G$ (it consists of elements of $G$ that commute with elements of $Z(G)$), So  $C_G(Z(G)) ⊆ G$.
we show that $G ⊆ C_G(Z(G))$. Take any element $g ∈ G$. By definition of centralizer, we need to show that $g$ commutes with every element of $Z(G)$. By the definition of the center $Z(G)$, every element $z∈Z(G)$ commutes with $g$, i.e.,$zg = gz$. So  $G ⊆ C_G(Z(G))$.
So $C_G(Z(G)) = G$.
## theorem centralizer_center_eq_normalizer_center
**Proof:**
We aim to prove that the centralizer of the center of a group $G$, denoted $C_G(Z(G))$, is equal to the normalizer of the center of $G$, denoted $N_G(Z(G))$. This means we need to show that an element $g$ in $G$ commutes with every element of $Z(G)$ if and only if $g$ normalizes $Z(G)$.
**Forward Direction:**
Assume $g$ commutes with every element of $Z(G)$. We need to show that $g$ normalizes $Z(G)$. Let $z$ be an arbitrary element of $Z(G)$. Since $g$ commutes with $z$, we have $zg = gz$. Now consider $g zg^{-1}$. Since $z$ is in the center, it commutes with all elements of $G$, including $g$, so $g zg^{-1} = z$. This shows that $z$ is mapped to an element in $Z(G)$ under conjugation by $g$, which means $g$ normalizes $Z(G)$.
**Reverse Direction:**
Assume $g$ normalizes $Z(G)$. We need to show that $g$ commutes with every element of $Z(G)$. Let $z$ be an arbitrary element of $Z(G)$. Since $g$ normalizes $Z(G)$, we have $g Z(G) g^{-1} = Z(G)$. This implies that for any $z \in Z(G)$, there exists some $z' \in Z(G)$ such that $g z g^{-1} = z'$. But since $z$ is in the center, it commutes with all elements, including $g$, so $g z g^{-1} = z$. This shows that $g$ must commute with $z$, and since $z$ was arbitrary, $g$ commutes with every element of $Z(G)$.
Thus, we have shown that $g$ commutes with every element of $Z(G)$ if and only if $g$ normalizes $Z(G)$, which completes the proof.
## theorem normalizer_center_eq_self
Combining the two theorems proved before, we get $N_G(Z(G)) = G$
-/
