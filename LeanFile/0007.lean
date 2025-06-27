import Mathlib
/-! Question:
5. Let $G$ be a group and let $A$ be a subgroup of $G$. Use Zorn's lemma to prove that there is a subgroup $M$ of $G$ that is maximal such that $M \cap A=1$ (that is, $M \cap A=1$, and $M<H \leqq G$ implies $H \cap A \
eq 1$ ).
-/

variable {G : Type u} [Group G] (A : Subgroup G)

lemma zorn₀ : ∃ M : Subgroup G, Maximal (fun N ↦ N ∈ {N : Subgroup G | N ⊓ A = ⊥}) M := by
  apply zorn_le₀
  intro c hc H
  --By Zorn's lemma, need to show that each chain of this set has an upperbound.
  obtain rfl | hcnemp := c.eq_empty_or_nonempty
  --We divide into two cases: whether c is empty or not
  · exact ⟨⊥, by simp⟩
  --If c is empty, trivial.
  · use sSup c
  --If not, use  $\bigcup_{N \in c}N$ to be the upperbound
  --In this case we can use ``sSup c`` as the \"union\" by theorem `Subgroup.mem_sSup_of_directedOn`.
    constructor
  --Need to show $\bigcup_{N \in c}N \in \{N : N \cap A = 1 \}$ and it is an u.b.
    · ext z
      --First, we show $\bigcup_{N \in c}N \in \{N : N \cap A = 1 \}$
      --i.e. $z \in \bigcup_{N \in c}N  \cap A \iff z = 1$
      constructor
      · rintro ⟨hzsup, hza⟩
        obtain ⟨s, hsc, hzs⟩ := (Subgroup.mem_sSup_of_directedOn hcnemp H.directedOn).1 hzsup
        --Since c is a chain, for $z \in \bigcup_{N \in c}N, \exists \ s \in c, z \in s$
        rw [← hc hsc]
        exact ⟨hzs, hza⟩
        --Then $s \in \{N : N \cap A = 1 \}, z \in s$ and $z \in a \Rightarrow z = 1$
      · intro hz
        rw [hz]
        exact Subgroup.one_mem (sSup c ⊓ A)
        --Since  $\bigcup_{N \in c}N \cap A$ is a subgroup, $z = 1 \in \bigcup_{N \in c}N \cap A$
    · intro z hz
      exact CompleteLattice.le_sSup c z hz
      --Finally, it is an u.b. as every element is below the supremum.


lemma zorn : ∃ M : {N : Subgroup G | N ⊓ A = ⊥}, IsMax M := by
  obtain ⟨M, hM, H⟩ := zorn₀ A
  exact ⟨⟨M, hM⟩, fun N hN ↦ H N.2 hN⟩
--This is the version where M is treated as an element of the subtype of G.

/-! Informal proof:
By Zorn's lemma, need to show that each chain of this set has an upperbound. 
We divide into two cases: whether c is empty or not
If c is empty, trivial.
If not, use $\bigcup_{N \in c}N$ to be the upperbound
Need to show $\bigcup_{N \in c}N \in \{N : N \cap A = 1 \}$ and it is an u.b.
First, we show $\bigcup_{N \in c}N \in \{N : N \cap A = 1 \} \in \{N : N \cap A = 1 \}$ 
i.e. $z \in \bigcup_{N \in c}N  \cap A \iff z = 1$
$\" \Rightarrow \" :$ Since c is a chain, for $z \in \bigcup_{N \in c}N, \exists \ s \in c, z \in s$
Then $s \in \{N : N \cap A = 1 \}, z \in s$ and $z \in a \Rightarrow z = 1$
$\" \Leftarrow \" :$  Since  $\bigcup_{N \in c}N \cap A$ is a subgroup, $z = 1 \in \bigcup_{N \in c}N \cap A$
Finally, it is an u.b. as every element is below the supremum.

-/
