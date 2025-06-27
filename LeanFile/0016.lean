import Mathlib
/-! Question:
6. Let $R$ be a ring. The annihilator of a left ideal $L$ of $R$ is the right ideal $\operatorname{Ann}(L)=$ $\{x \in R \mid L x=0\}$ of $R$. The annihilator of a right ideal $T$ of $R$ is the left ideal $\operatorname{Ann}(T)=\{x \in R \mid x T=0\}$ of $R$. Show that these constructions constitute a Galois connection between left ideals and right ideals of $R$.
-/

namespace UnexploredExercise_7354

/- Let $R$ be a ring. The annihilator of a left ideal $L$ of $R$ is the right ideal $Ann⁡(L)=\{x \in R \mid Lx=0\}$ of $R$. The annihilator of a right ideal $T$ of $R$ is the left ideal $Ann⁡(T)=\{x \in R \mid xT=0\}$ of $R$. Show that these constructions constitute a Galois connection between left ideals and right ideals of $R$. -/

-- informal answer

/-
An antitone Galois connection between two preordered sets
  $\alpha$ and $\beta$ consists of two maps $l : \alpha \rightarrow \beta$
  and $u : \beta \rightarrow \alpha$ such that $\forall a \in \alpha$
  and $b \in \beta$, $b \leq l a \leftrightarrow a \leq u b$.


The set of left ideals of $R$ is preordered with order inherited from the underlying set of each ideal. The set of right ideals of $R$ is preordered with order inherited from the underlying set of each ideal.


The annihilator of a left ideal $L$ of $R$ is a subset $\{x \in R \mid Lx=0\}$. This set is closed under addition, posses a zero, closed under negation, and satisfies right absorbing condition, hence is a right ideal. Similarly the annihilator of a right ideal is a left ideal.


The left and right annihilator constitute a antitone Galois connection between left ideals and right ideals of $R$: Given arbitrary left ideal $L$ and right ideal $T$ of $R$, our goal is to prove $T \leq Ann(L) \leftrightarrow L \leq Ann(T)$. We'll only do one direction since the other is the same.


Given $T \leq Ann(L)$, to prove $L \leq Ann(T)$, we only need to show that for any $l \in L$, $lt=0$ for all $t \in T$. But since $T \leq Ann(L)$, $lt$ is exactly $0$ for all $l \in L$ and $t \in T$.
-/


-- formal answer

variable {α : Type u} {β : Type v}

/-- An antitone Galois connection between two preordered sets
  $\alpha$ and $\beta$ consists of two maps $l : \alpha \rightarrow \beta$
  and $u : \beta \rightarrow \alpha$ such that $\all a \in \alpha$
  and $b \in \beta$, $b \leq l a \leftrightarrow a \leq u b$. -/
def AntitoneGaloisConnection [Preorder α] [Preorder β] (l : α → β) (u : β → α) :=
  ∀ a b, b ≤ l a ↔ a ≤ u b

variable (R : Type*) [Ring R]

/-- The left ideal of $R$ -/
structure LeftIdeal extends AddSubgroup R where
  left_absorb : ∀ r : R, ∀ i ∈ carrier, r * i ∈ carrier

/-- The right ideal of $R$ -/
structure RightIdeal extends AddSubgroup R where
  right_absorb : ∀ r : R, ∀ i ∈ carrier, i * r ∈ carrier

-- The set of left ideals of $R$ is preordered
instance : Preorder (LeftIdeal R) := {
  -- with order inherited from the underlying set of each ideal.
  le := fun L1 L2 ↦ L1.carrier ≤ L2.carrier
  le_refl := fun a ⦃_⦄ a ↦ a
  le_trans := fun a b c hab hbc ⦃_⦄ a ↦ hbc (hab a)
}

-- The set of right ideals of $R$ is preordered
instance : Preorder (RightIdeal R) := {
  -- with order inherited from the underlying set of each ideal.
  le := fun L1 L2 ↦ L1.carrier ≤ L2.carrier
  le_refl := fun a ⦃_⦄ a ↦ a
  le_trans := fun a b c hab hbc ⦃_⦄ a ↦ hbc (hab a)
}

-- The annihilator of a left ideal $L$ of $R$
def LeftAnnihilator : LeftIdeal R → RightIdeal R := fun L ↦ {
  -- is a subset $\{x \in R \mid Lx=0\}$
  carrier := {x : R | ∀ l ∈ L.carrier, l * x = 0}
  -- this set is closed under addition
  add_mem' := fun {a b} ha hb l hl ↦ by
    rw [mul_add, ha l hl, hb l hl, add_zero]
  -- and posses a zero
  zero_mem' := fun l a ↦ mul_zero l
  -- and is closed under negation
  neg_mem' := fun {x} hx l hl ↦ by
    rw [mul_neg, hx l hl, neg_zero]
  -- and satisfies right absorbing condition, hence is a right ideal.
  right_absorb := fun r i hi l hl ↦ by
    rw [← mul_assoc, hi l hl, zero_mul]
}

-- The annihilator of a right ideal $T$ of $R$
def RightAnnihilator : RightIdeal R → LeftIdeal R := fun T ↦ {
  -- is a subset $\{x \in R \mid xT=0\}$
  carrier := {x : R | ∀ t ∈ T.carrier, x * t = 0}
  -- this set is closed under addition
  add_mem' := fun {a b} ha hb t ht ↦ by
    rw [add_mul, ha t ht, hb t ht, add_zero]
  -- and posses a zero
  zero_mem' := fun t a ↦ zero_mul t
  -- and is closed under negation
  neg_mem' := fun {x} hx t ht ↦ by
    rw [neg_mul, hx t ht, neg_zero]
  -- and satisfies left absorbing condition, hence is a left ideal.
  left_absorb := fun r i hi t ht ↦ by
    rw [mul_assoc, hi t ht, mul_zero]
}

-- The left and right annihilator constitute a antitone Galois connection between left ideals and right ideals of $R$.
example : AntitoneGaloisConnection
  (LeftAnnihilator R) (RightAnnihilator R) := by
  -- Given arbitrary left ideal $L$ and right ideal $T$ of $R$,
  intro L T
  -- our goal is to prove $T \leq Ann(L) \leftrightarrow L \leq Ann(T)$
  constructor
  -- We'll only do one direction since the other is the same.
  all_goals
    -- Given $T \leq Ann(L)$, to prove $L \leq Ann(T)$, we only need to show that for any $l \in L$, $lt=0$ for all $t \in T$.
    intro HTL l hl t ht
    -- But since $T \leq Ann(L)$, $lt$ is exactly $0$ for all $l \in L$ and $t \in T$.
    exact HTL ht l hl

end UnexploredExercise_7354

/-! Informal proof:
An antitone Galois connection between two preordered sets
  $\alpha$ and $\beta$ consists of two maps $l : \alpha \rightarrow \beta$
  and $u : \beta \rightarrow \alpha$ such that $\forall a \in \alpha$
  and $b \in \beta$, $b \leq l a \leftrightarrow a \leq u b$.

The set of left ideals of $R$ is preordered with order inherited from the underlying set of each ideal. The set of right ideals of $R$ is preordered with order inherited from the underlying set of each ideal.

The annihilator of a left ideal $L$ of $R$ is a subset $\{x \in R \mid Lx=0\}$. This set is closed under addition, posses a zero, closed under negation, and satisfies right absorbing condition, hence is a right ideal. Similarly the annihilator of a right ideal is a left ideal.

The left and right annihilator constitute a antitone Galois connection between left ideals and right ideals of $R$: Given arbitrary left ideal $L$ and right ideal $T$ of $R$, our goal is to prove $T \leq Ann(L) \leftrightarrow L \leq Ann(T)$. We'll only do one direction since the other is the same.

Given $T \leq Ann(L)$, to prove $L \leq Ann(T)$, we only need to show that for any $l \in L$, $lt=0$ for all $t \in T$. But since $T \leq Ann(L)$, $lt$ is exactly $0$ for all $l \in L$ and $t \in T$.
-/
