import Mathlib
/-! Question:
2.2.10. 环 $\mathbb{Z} / 3 \mathbb{Z}$ 与环 $\mathbb{Z} / 6 \mathbb{Z}$ 的子环 $2 \mathbb{Z} / 6 \mathbb{Z}$ 是否同构?
-/
/-Problem: Verify that ring $\mathbb{Z}_3$ is isomorphic to $2\mathbb{Z}/6\mathbb{Z}$(the subring of $\mathbb{Z}_6$) or not. -/
/-An elemet is in a nonunitalsubsemiring if and only if it's in the carrier set of the corresponding semiring.
This is a lemma that can simplify the prove, transforming relations on a semiring into a set with its concrete element. -/
lemma mem_carrier_iff {R : Type*} [NonUnitalNonAssocRing R] {s : NonUnitalSubsemiring R} {x : R}:
 x∈s↔ (x∈s.carrier) :=Eq.to_iff rfl
/-Define the nonunitalsubring $2\mathbb{Z}/6\mathbb{Z}$.-/
instance subring: NonUnitalSubring (ZMod 6) where
  carrier := {0,2,4}
  add_mem' := by decide
  zero_mem' := by decide
  mul_mem' := by decide
  neg_mem' := by decide
/-Define an isomorphism between $\mathbb{Z}_3$ and $2\mathbb{Z}/\mathbb{Z}_6$ which implies they are isomorphic to each other.-/
instance isomorphism :subring≃+* (ZMod 3)  where
/-By simple computation we find that $4$ is the identiy of $2\mathbb{Z}/6\mathbb{Z}$ 
in the sense of multiplicative group, and $0$ is the zero element.So we can construct a map:$2\mathbb{Z}/6\mathbb{Z}\to
\mathbb{Z}_3$ that sends $4$ to $1$, $0$ to $0$ and $2$ to $2$ or equivalently sents $x$ to $x%3$.-/
  toFun := by
    intro ⟨a,_⟩
    use a.1%3; simp only [Nat.reduceAdd]
    exact Nat.mod_lt a.1  (Nat.zero_lt_succ 2)
/-Similar to the construction above, we define the inverse map:\mathbb{Z}_3\to2\mathbb{Z}/6\mathbb{Z} that
sends $0$ to $0$, $1$ to $4$ and $2$ to $2$ or equivalently sents $x$ to $4*x%6$-/
  invFun := by
    intro ⟨a,ha⟩
    simp only [Nat.reduceAdd] at ha
    let g:subring:={
      val := {
        val := 4*a%6
        isLt := by
          simp only [Nat.reduceAdd]
          exact Nat.mod_lt (4*a)  (Nat.zero_lt_succ 5)
      }
      property := by
        apply mem_carrier_iff.mpr
        simp[subring];
        rw [← @Finset.mem_range] at ha
        fin_cases ha
        · simp only [mul_zero, Nat.zero_mod, Fin.zero_eta, Fin.isValue, true_or]
        · simp only [mul_one, Nat.reduceMod, Fin.reduceFinMk, Fin.isValue, or_true]
        · simp only [Nat.reduceMul, Nat.reduceMod, Fin.reduceFinMk, Fin.isValue, true_or, or_true]
    }
    use g,g.2
/-Verify that the maps defined above form a pair of invertible map.
We handle with this by checking the equation holds pointwisely. -/
  left_inv := by
    intro t; have ht:=t.2
    simp only [Nat.reduceAdd]
    apply mem_carrier_iff.mpr at ht
    simp only[subring] at ht
    ext
    rcases ht with (h|h|h)
    · rw[h]; rfl 
    · rw[h]; rfl
    · rw[Set.mem_singleton_iff.mp h]; rfl
  right_inv := by
    intro t; simp only [Nat.reduceAdd]; fin_cases t
    · rfl
    · rfl
    · rfl
/-Verify that the maps defined above are ring homomorphisms.
Similarly, we handle with this by checking the equation holds pointwisely.-/
  map_mul' := by
    intro a b; have ha:=a.2; have hb:=b.2
    simp only [Nat.reduceAdd]
    apply mem_carrier_iff.mpr at ha
    apply mem_carrier_iff.mpr at hb
    simp only[subring] at *
    rw [← @Fin.natCast_def,← @Fin.natCast_def,← @Fin.natCast_def]
    rcases ha with (ha|ha|ha)
    · rw[ha]; simp only [zero_mul, Fin.val_zero, Nat.cast_zero, Fin.isValue] 
    · rw[ha]; simp only [Fin.val_two, Nat.cast_ofNat, Fin.isValue]; rcases hb with (hb|hb|hb)
      · rw[hb]; rfl
      · rw[hb]; rfl
      · rw[Set.mem_singleton_iff.mp hb]; rfl
    · rw[Set.mem_singleton_iff.mp ha];  rcases hb with (hb|hb|hb)
      · rw[hb]; rfl
      · rw[hb]; rfl
      · rw[Set.mem_singleton_iff.mp hb]; rfl
  map_add' := by
    intro a b 
    simp only [Nat.reduceAdd]; have ha:=a.2; have hb:=b.2; 
    apply mem_carrier_iff.mpr at ha
    apply mem_carrier_iff.mpr at hb
    simp only[subring] at *
    rw [← @Fin.natCast_def,← @Fin.natCast_def,← @Fin.natCast_def]
    rcases ha with (ha|ha|ha)
    · rw[ha]; simp only [zero_add, Fin.val_zero, Nat.cast_zero, Fin.isValue]
    · rw[ha]; rcases hb with (hb|hb|hb)
      · rw[hb]; rfl 
      · rw[hb]; rfl
      · rw[Set.mem_singleton_iff.mp hb]; rfl
    · rw[Set.mem_singleton_iff.mp ha]; rcases hb with (hb|hb|hb)
      · rw[hb]; rfl
      · rw[hb]; rfl
      · rw[Set.mem_singleton_iff.mp hb]; rfl
  

/-! Informal proof:
**Problem**: Verify that ring $\mathbb{Z}_3$ is isomorphic to $2\mathbb{Z}/6\mathbb{Z}$(the subring of $\mathbb{Z}_6$) or not.
**Proof**:Claim that $\mathbb{Z}_3$ is isomorphisc to $2\mathbb{Z}/6\mathbb{Z}$. Indeed, we can construct a map $f:\mathbb{Z}_3\to2\mathbb{Z}/6\mathbb{Z}, x\mapsto 4x$, obviously, $f$ is bijective and is a homomorphism, hence, is an isomorphism. Q.E.D.
-/
