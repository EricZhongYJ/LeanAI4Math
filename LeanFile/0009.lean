import Mathlib
/-! Question:
if G/Z(G) is cyclic, then G is abelian.
-/
open Subgroup

example {G : Type*} [Group G](Cyclic_Quotient_Group : IsCyclic (G ⧸ Subgroup.center G)) : CommGroup G := by
  /- To prove a group is an abelian group is the same to show that the law of composition in this group is symmtric. In this example we use multiplication to refer the law of composition. -/
  apply CommGroup.mk
  /- Choose arbitrary $ a, b ∈ G $, then show $ a * b = b * a $. -/
  intro a b
  /- Use ha, hb to record the equivalent class $ ↑a, ↑b $ of $ a, b $ in the quotient group $ G/Z(G) $ respectively. -/
  have ha := QuotientGroup.mk'_apply (center G : Subgroup G) (a : G)
  have hb := QuotientGroup.mk'_apply (center G : Subgroup G) (b : G)
  /- By assumption $ G/Z(G) $ is cyclic, obtain the generator $ g ∈ G/Z(G) $. -/
  rcases Cyclic_Quotient_Group.exists_generator with Exists_generator
  rcases Exists_generator with ⟨g, hg⟩
  /- Since $ ↑a, ↑b ∈ G/Z(G) $ and $ G/Z(G) $ is a cyclic group, $ ↑a, ↑b $ can be represented by the generator $ g ∈ G/Z(G) $. -/
  have hga := hg a
  have hgb := hg b
  /- Since $ G/Z(G) $ is a cyclic group, $ ↑a, ↑b $ can be represented by power of the generator $ g $. Let $ g ^ {ka}, g ^ {kb} $ denote $ ↑a, ↑b $ respectively. -/
  rw [Subgroup.mem_zpowers_iff] at *
  rcases hga with ⟨ka, hka⟩
  rcases hgb with ⟨kb, hkb⟩
  /- We can lift the generator $ g ∈ G/Z(G) $ into group $ G $, denote the lift by $ gr $, i.e. $ g $ is the image of $ gr $ under the canonical map. -/
  obtain ⟨gr, hgr⟩ : ∃(x : G), g = (x : G ⧸ Subgroup.center G) := QuotientGroup.exists_mk.mp ⟨g, rfl⟩
  rw [hgr] at hka hkb
  /- With the lift $ gr ∈ G $, we can lift $ g ^ ka, g ^ kb $ with $ gr ^ ka, gr ^ kb $ respectively, i.e. $ g ^ ka, g ^ kb $ is the image of $ gr ^ ka, gr ^ kb $ under the canonical map. -/
  have Hgrb := QuotientGroup.mk'_apply (center G : Subgroup G) (gr ^ kb : G)
  have Hgra := QuotientGroup.mk'_apply (center G : Subgroup G) (gr ^ ka : G)
  /- With respect to the lift $ gr $, we want to represent $ a, b ∈ G $ by $ gr ^ ka * za, gr ^ kb * zb $, where $ za, zb ∈ Z(G) $. The existence of $ za, zb $ comes from the definition of the coset. -/
  /- Exists_za and Exists_zb use the \"records\" ha and hb to declare that $ ↑a, ↑b $ and $ g ^ ka, g ^ kb $ represent same cosets respectively. -/
  have Exists_za : (QuotientGroup.mk' (center G)) (gr ^ ka) = (QuotientGroup.mk' (center G)) a := by
    calc
      (QuotientGroup.mk' (center G)) (gr ^ ka) = (gr ^ ka : G ⧸ center G) := by exact Hgra
      _ = (a : G ⧸ center G) := by rw [hka]
      _ = (QuotientGroup.mk' (center G)) a := by rw [← ha]
  have Exists_zb : (QuotientGroup.mk' (center G)) (gr ^ kb) = (QuotientGroup.mk' (center G)) b := by
    calc
      (QuotientGroup.mk' (center G)) (gr ^ kb) = (gr ^ kb : G ⧸ center G) := by exact Hgrb
      _ = (b : G ⧸ center G) := by rw [hkb]
      _ = (QuotientGroup.mk' (center G)) b := by rw [← hb]
  /- Since $ ↑a, ↑b $ and $ g ^ ka, g ^ kb $ represent same cosets respectively, by definition of coset, we can find the $ za, zb ∈ Z(G) $ we want. -/
  rw [QuotientGroup.mk'_eq_mk'] at Exists_za
  rw [QuotientGroup.mk'_eq_mk'] at Exists_zb
  rcases Exists_za with ⟨za, hza⟩
  rcases Exists_zb with ⟨zb, hzb⟩
  /- We use hza and hzb to denote the identity $ gr ^ ka * za = a, gr ^ kb * zb = b $ respectively. -/
  rcases hza with ⟨hza1, hza2⟩
  rcases hzb with ⟨hzb1, hzb2⟩
  /- By this rewrite, we explicitly express the property of the elements in center. -/
  rw [Subgroup.mem_center_iff] at *

  /- Now we try to use the new representations to show that the $ a * b = b * a $. -/
  calc
    a * b = gr ^ ka * za * (gr ^ kb * zb) := by
      /- Substitute the new representations of $ a, b $. -/
      rw [← hza2]
      rw [← hzb2]
    _ = za * gr ^ ka * (gr ^ kb * zb) := by
      /- Exchange the position of $ za $ and $ gr ^ kb $. -/
      rw [← hza1]
    _ = za * (gr ^ ka * gr ^ kb) * zb := by
      /- Add parentheses to force lean recognise the elements' positions which we want to exchange. -/
      rw [← mul_assoc]
      rw [mul_assoc za (gr ^ ka) (gr ^ kb)]
    _ = za * (gr ^ kb * gr ^ ka) * zb := by
      /- Exchange the position of $ gr ^ ka $ and $ gr ^ kb $. -/
      rw [Commute.zpow_zpow_self (gr : G) (ka : ℤ) (kb : ℤ)]
    _ = gr ^ kb * za * gr ^ ka * zb := by
      /- Exchange the position of $ za $ and $ gr ^ kb $. -/
      rw [← mul_assoc]
      rw [hza1]
    _ = gr ^ kb * (za * gr ^ ka) * zb := by
      /- Add parentheses to force lean recognise the elements' positions which we want to exchange. -/
      rw [mul_assoc (gr ^ kb) za (gr ^ ka)]
    _ = gr ^ kb * gr ^ ka * za * zb := by
      /- Exchange the position of $ za $ and $ gr ^ ka $. -/
      rw [← hza1]
      rw [← mul_assoc]
    _ = gr ^ kb * gr ^ ka * (zb * za) := by
      /- Exchange the position of $ za $ and $ zb $. -/
      rw [mul_assoc]
      rw [hza1]
    _ = gr ^ kb * (zb * gr ^ ka) * za := by
      /- Exchange the position of $ gr ^ ka $ and $ zb $. -/
      rw [← mul_assoc]
      rw [mul_assoc (gr ^ kb)]
      rw [← hzb1]
    _ = gr ^ kb * zb * (gr ^ ka * za) := by
      /- Adding enough parentheses to make clear the corresponding forms of $ a, b $. -/
      rw [← mul_assoc]
      rw [mul_assoc]
    _ = b * a := by
      /- Reach the result $ a * b = b * a $ by substitute the identities on $ a, b $. -/
      rw [← hza2]
      rw [← hzb2]

/-! Informal proof:
-- Example_8015B
If $G/Z(G)$ is cyclic, then $G$ is abelian.
-- informal answer
Proof:
1. To prove group $G$ is abelian, one can prove $∀ \ a, b ∈ G, a * b = b * a$.
2. Since $G/Z(G)$ is cyclic, we can choose generator $gZ(G) ∈ G/Z(G)$.
3. Since $G/Z(G)$ is cyclic, the image of $a, b$ under the canonical map $$π: G → G/Z(G)$$ can be represented by the generator $gZ(G)$ in step 2, i.e. $$∃ \ ka, kb ∈ ℕ, π(a) = (gZ(G)) ^ {ka} = g ^ {ka} Z(G), π(b) = (gZ(G)) ^ {kb} = g ^ {kb} Z(G).$$
4. By definition of the canonical map, $π(a) := aZ(G), π(b) := bZ(G)$.
5. Since $aZ(G) = g ^ {ka} Z(G), bZ(G) = g ^ {kb} Z(G)$, where $a, b, g ∈ G$. By definition of coset, $∃ za, zb ∈ Z(G), a = g ^ {ka} * za, b = g ^ {kb} * zb$.
6. Since $za, zb ∈ Z(G)$, we have $$a * b = (g ^ {ka} * za) * (g ^ {kb} * zb) = za * g ^ {(ka + kb)} * zb = zb * g ^ {(kb + ka)} * za = (zb * g ^ {kb}) * (za * g ^ {ka}) = b * a.$$
7. Since we choose $a, b$ arbitrarily, therefore we prove $∀ \ a, b ∈ G, a * b = b * a.$
-/
