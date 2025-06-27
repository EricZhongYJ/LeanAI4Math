import Mathlib
/-! Question:
7. Let $G$ be a group. The centralizer of a subgroup $H$ of $G$ is $C(H)=\{x \in G \mid x h=h x$ for all $h \in H\}$. Show that $(C, C)$ is a Galois connection between subgroups of $G$ and subgroups of $G$.
-/

namespace UnexploredExercise_7355

/- Let $G$ be a group. The centralizer of a subgroup $H$ of $G$ is $C(H)=\{x \in G \mid xh=hx\}$. Show that $(C, C)$ is a Galois connection between subgroups of $G$ and subgroups of $G$. -/

-- informal answer

/-
An antitone Galois connection between two preordered sets
  $\alpha$ and $\beta$ consists of two maps $l : \alpha \rightarrow \beta$
  and $u : \beta \rightarrow \alpha$ such that $\forall a \in \alpha$
  and $b \in \beta$, $b \leq l a \leftrightarrow a \leq u b$.


Given two subgroup $H_1$ and $H_2$ of $G$, our goal is to prove $H_2 \leq C(H_1) \leftrightarrow H_1 \leq C(H_2)$.
That is, $H_2 \leq C(H_1) \rightarrow H_1 \leq C(H_2)$ and $H_1 \leq C(H_2) \rightarrow H_2 \leq C(H_1)$.


We'll only prove the first direction, as the second can follow the same proof.
Take an arbitrary element $x$ of $H_1$, to show that $x \in C(H_2)$, it suffices to prove $\forall h \in H_2, xh = hx$.
And this follows directly from $H_2 \leq C(H_1)$
-/

-- formal answer

/-- An antitone Galois connection between two preordered sets
  $\alpha$ and $\beta$ consists of two maps $l : \alpha \rightarrow \beta$
  and $u : \beta \rightarrow \alpha$ such that $\all a \in \alpha$
  and $b \in \beta$, $b \leq l a \leftrightarrow a \leq u b$. -/
def AntitoneGaloisConnection [Preorder α] [Preorder β] (l : α → β) (u : β → α) :=
  ∀ a b, b ≤ l a ↔ a ≤ u b

variable (G : Type*) [Group G]

open Subgroup in
example : AntitoneGaloisConnection
  (fun H : Subgroup G ↦ centralizer H)
  (fun H : Subgroup G ↦ centralizer H) := by
  -- Given two subgroup $H_1$ and $H_2$ of $G$,
  intro H₁ H₂
  -- our goal is to prove $H_2 \leq C(H_1) \leftrightarrow H_1 \leq C(H_2)$.
  constructor
  -- That is, $H_2 \leq C(H_1) \rightarrow H_1 \leq C(H_2)$ and $H_1 \leq C(H_2) \rightarrow H_2 \leq C(H_1)$.
  -- We'll only prove the first direction, as the second can follow the same proof.
  all_goals
    -- Take an arbitrary element $x$ of $H_1$
    intro hle x hx
    -- to show that $x \in C(H_2)$, it suffices to prove $\all h \in H_2, xh = hx$.
    rw [mem_centralizer_iff]
    intro h hh
    -- and this follows directly from $H_2 \leq C(H_1)$
    exact hle hh x hx |>.symm

end UnexploredExercise_7355

/-! Informal proof:
An antitone Galois connection between two preordered sets
  $\alpha$ and $\beta$ consists of two maps $l : \alpha \rightarrow \beta$
  and $u : \beta \rightarrow \alpha$ such that $\forall a \in \alpha$
  and $b \in \beta$, $b \leq l a \leftrightarrow a \leq u b$.

Given two subgroup $H_1$ and $H_2$ of $G$, our goal is to prove $H_2 \leq C(H_1) \leftrightarrow H_1 \leq C(H_2)$.
That is, $H_2 \leq C(H_1) \rightarrow H_1 \leq C(H_2)$ and $H_1 \leq C(H_2) \rightarrow H_2 \leq C(H_1)$.

We'll only prove the first direction, as the second can follow the same proof.
Take an arbitrary element $x$ of $H_1$, to show that $x \in C(H_2)$, it suffices to prove $\forall h \in H_2, xh = hx$.
And this follows directly from $H_2 \leq C(H_1)$
-/
