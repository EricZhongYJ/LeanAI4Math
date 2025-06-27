import Mathlib
/-! Question:
5. Prove the following: when $(\alpha, \beta)$ is a Galois connection between two partially ordered sets $X$ and $Y$, then $\alpha$ and $\beta$ induce mutually inverse, order reversing bijections between $\operatorname{Im} \alpha$ and $\operatorname{Im} \beta$; moreover, if $X$ and $Y$ are complete lattices, then $\operatorname{Im} \alpha$ and $\operatorname{Im} \beta$ are complete lattices.
-/

/-Prove the following: when $(\alpha, \beta)$ is a Galois connection between two partially ordered sets $X$ and $Y$, then $\alpha$ and $\beta$ induce mutually inverse, order reversing bijections between $Im⁡ \alpha \beta$ and $Im⁡ \beta \alpha$-/

-- informal answer

/-
An antitone Galois connection between two preordered sets
  $\alpha$ and $\beta$ consists of two maps $l : \alpha \rightarrow \beta$
  and $u : \beta \rightarrow \alpha$ such that $\all a \in \alpha$
  and $b \in \beta$, $b \leq l a \leftrightarrow a \leq u b$.


Preparation:
1. Under the setup of a Galois connection, every $x \in X \leq \beta (\alpha x)$.
 - Since $\forall x \in X, \alpha x \leq \alpha x$
 - Then by antitone Galois connection, $x \leq \beta (\alpha x)$

2. Similarly, under the setup of a Galois connection, every $y \in Y \leq \alpha (\beta y)$.

3. Under the setup of a Galois connection, conjugate action $\alpha \beta \alpha$ is only $\alpha$: We use the antisymmetic property
 - first, we've proved that $x \leq \beta (\alpha x)$, substitute $x$ with $\beta (\alpha x)$ then we got $x \leq \beta (\alpha x) \leq \beta (\alpha (\beta (\alpha x)))$
 - then by antitone Galois connection, where we substitute $a$ for $x$ and $b$ for $\alpha (\beta (\alpha x))$, we can directly get $\alpha (\beta (\alpha x)) \leq \alpha x$.
 - For the other direction, first by reflexivity, $\beta (\alpha x) \leq \beta (\alpha x)$ then it follows from antitone Galois connection that $\alpha x \leq \alpha (\beta (\alpha x))$.

4. Similarly we can prove the conjugate action $\beta \alpha \beta$ is only $\beta$


Defining key set and map:
1. Define the closure of $X$ as the image of $\beta \alpha$
2. Define the closure of $Y$ as the image of $\alpha \beta$
3. Restrict $\alpha$ to the closure of $X$, by definition, this gives a map from the closure of $X$ to the closure of $Y$
4. Restrict $\beta$ to the closure of $Y$, by definition, this gives a map from the closure of $Y$ to the closure of $X$


Proof:
1. Then the restricted maps are bijective, and they are each other's inverse
 - We prove this by showing that the restricted $\beta$ is the left and right inverse of the restricted $\alpha$
 - Left inverse: By definition there should be a $x'$ such that $x = \beta \alpha x'$. Thus $\beta \alpha x = \beta \alpha \beta \alpha x' = \beta \alpha x' = x$
 - Right inverse: similarly there should be a $y'$ s.t., $y = \alpha \beta y'$, then $\alpha \beta y = \alpha \beta \alpha \beta y' = \alpha \beta y' = y$

2. The restricted $\alpha$ is order-reversing
 - Given arbitrary $x_1 \leq x_2$ in the closure of $X$, there are, by definition, $x_1'$ and $x_2'$ s.t., $x_1 = \beta \alpha x_1'$ and so on
 - Then to prove $\alpha x_1 \leq \alpha x_2$, we only need to show $\alpha \beta \alpha x_1' \leq \alpha \beta \alpha x_2'$, which, by antitone Galois connection, is equivalent to $\beta (\alpha x_1') \leq \beta (\alpha (\beta (\alpha x_2')))$.
 - Using the conjugate cancellation, we get $\beta (\alpha x_1') \leq \beta (\alpha x_2')$. This is exactly $x_1 \leq x_2$

3. The restricted $\beta$ is order-reversing for similar reason.
-/

-- formal answer

variable {α : Type u} {β : Type v}

/-- An antitone Galois connection between two preordered sets
  $\alpha$ and $\beta$ consists of two maps $l : \alpha \rightarrow \beta$
  and $u : \beta \rightarrow \alpha$ such that $\all a \in \alpha$
  and $b \in \beta$, $b \leq l a \leftrightarrow a \leq u b$. -/
def AntitoneGaloisConnection [Preorder X] [Preorder Y] (α : X → Y) (β : Y → X) :=
  ∀ a b, b ≤ α a ↔ a ≤ β b

variable
  {X Y : Type*} [PartialOrder X] [PartialOrder Y] (α : X → Y) (β : Y → X)
  (hGal : AntitoneGaloisConnection α β)

include hGal

variable {α} {β} in
-- Under the setup of a Galois connection, every $x \in X \leq \beta (\alpha x)$.
lemma le_ba_X : ∀ x : X, x ≤ β (α x) := fun x ↦ by
  -- Since $\forall x \in X, \alpha x \leq \alpha x$
  have refl : ∀ x : X, α x ≤ α x := fun x ↦ le_refl (α x)
  -- Then by antitone Galois connection, $x \leq \beta (\alpha x)$
  exact hGal x (α x) |>.1 (refl x)

variable {α} {β} in
-- Under the setup of a Galois connection, every $y \in Y \leq \alpha (\beta y)$.
lemma le_ab_Y : ∀ y : Y, y ≤ α (β y) := fun y ↦ by
  -- Since $\forall y \in Y, \beta y \leq \beta y$
  have refl : ∀ y : Y, β y ≤ β y := fun y ↦ le_refl (β y)
  -- Then by antitone Galois connection, $y \leq \alpha (\beta y)$
  exact hGal (β y) y |>.2 (refl y)

-- Under the setup of a Galois connection, conjugate action $\alpha \beta \alpha$ is only $\alpha$
lemma conj_eq : ∀ x : X, α (β (α x)) = α x := fun x ↦ by
  -- We use the antisymmetic property
  refine le_antisymm ?_ ?_
    -- first, we've proved that $x \leq \beta (\alpha x)$, substitute $x$ with $\beta (\alpha x)$ then we got $x \leq \beta (\alpha x) \leq \beta (\alpha (\beta (\alpha x)))$
  · have le := le_trans (le_ba_X hGal x) <| (le_ba_X hGal) <| β (α x)
    -- then by antitone Galois connection, where we substitute $a$ for $x$ and $b$ for $\alpha (\beta (\alpha x))$, we can directly get $\alpha (\beta (\alpha x)) \leq \alpha x$.
    exact hGal x (α <| β (α x)) |>.2 le
    -- For the other direction, first by reflexivity, $\beta (\alpha x) \leq \beta (\alpha x)$
  · have refl := le_refl β (α x)
    -- then it follows from antitone Galois connection that $\alpha x \leq \alpha (\beta (\alpha x))$.
    exact hGal (β (α x)) (α x) |>.2 refl

-- Similarly we can prove the conjugate action $\beta \alpha \beta$ is only $\beta$
lemma conj_eq' : ∀ y : Y, β (α (β y)) = β y := fun y ↦ by
  -- We use the antisymmetic property
  refine le_antisymm ?_ ?_
  · -- $y \leq \alpha (\beta (\alpha (\beta y)))$
    have le := le_trans (le_ab_Y hGal y) <| (le_ab_Y hGal) <| α (β y)
    -- By Galois conncetion we can get $\beta (\alpha (\beta y)) ≤ \beta y$
    exact hGal (β <| α (β y)) y |>.1 le
  · -- $\alpha \beta y \leq \alpha \beta y$
    have refl := le_refl α (β y)
    -- By Galois conncetion we can get $\beta y \leq \beta (\alpha (\beta y))$
    exact hGal (β y) (α (β y)) |>.1 refl

-- Define the closure of $X$ as the image of $\beta \alpha$
def ClosedX : Set X := Set.range (β.comp α)
-- Define the closure of $Y$ as the image of $\alpha \beta$
def ClosedY : Set Y := Set.range (α.comp β)

-- Restrict $\alpha$ to the closure of $X$, by definition, this gives a map from the closure of $X$ to the closure of $Y$
def toFun : ClosedX α β → ClosedY α β := fun x ↦ by
  use α x.1
  obtain ⟨x', hx'⟩ := x.2
  use α x'
  rw [Function.comp_apply, ← hx', Function.comp_apply]

-- Restrict $\beta$ to the closure of $Y$, by definition, this gives a map from the closure of $Y$ to the closure of $X$
def invFun : ClosedY α β → ClosedX α β := fun y ↦ by
  use β y.1
  obtain ⟨y', hy'⟩ := y.2
  use β y'
  rw [Function.comp_apply, ← hy', Function.comp_apply]

-- Then the restricted maps are bijective, and they are each other's inverse
lemma bij : Function.Bijective (toFun α β) := by
  refine Function.bijective_iff_has_inverse.mpr ?_
  -- We prove this by showing that the restricted $\beta$ is the left and right inverse of the restricted $\alpha$
  use invFun α β
  constructor
  -- Left inverse
  · intro x
    -- By definition there should be a $x'$ such that $x = \beta \alpha x'$
    obtain ⟨x', hx'⟩ := x.2
    -- Thus $\beta \alpha x = \beta \alpha \beta \alpha x' = \beta \alpha x' = x$
    simp_rw [invFun, toFun, ← hx', Function.comp_apply, conj_eq _ _ hGal, ← Subtype.val_inj, ← hx', Function.comp_apply]
  -- Right inverse
  · intro y
    -- similarly there should be a $y'$ s.t., $y = \alpha \beta y'$
    obtain ⟨y', hy'⟩ := y.2
    -- then $\alpha \beta y = \alpha \beta \alpha \beta y' = \alpha \beta y' = y$
    simp_rw [invFun, toFun, ← hy', Function.comp_apply, conj_eq' _ _ hGal, ← Subtype.val_inj, ← hy', Function.comp_apply]

-- The restricted $\alpha$ is order-reversing
lemma order_re1 : ∀ x₁ x₂ : ClosedX α β, x₁ ≤ x₂ → α x₂ ≤ α x₁ := fun x₁ x₂ h12 ↦ by
  -- Given arbitrary $x_1 \leq x_2$ in the closure of $X$, there are, by definition, $x_1'$ and $x_2'$ s.t., $x_1 = \beta \alpha x_1'$ and so on
  obtain ⟨x₁', h1⟩ := x₁.2
  obtain ⟨x₂', h2⟩ := x₂.2
  -- Then to prove $\alpha x_1 \leq \alpha x_2$, we only need to show $\alpha \beta \alpha x_1' \leq \alpha \beta \alpha x_2'$, which, by antitone Galois connection, is equivalent to $\beta (\alpha x_1') \leq \beta (\alpha (\beta (\alpha x_2')))$.
  -- Using the conjugate cancellation, we get $\beta (\alpha x_1') \leq \beta (\alpha x_2')$.
  rw [← h1, ← h2, Function.comp_apply, Function.comp_apply, hGal, conj_eq _ _ hGal]
  -- This is exactly $x_1 \leq x_2$
  rw [Function.comp_apply, h1, h2] at *
  exact h12

-- The restricted $\beta$ is order-reversing
lemma order_re2 : ∀ y₁ y₂ : ClosedY α β, y₁ ≤ y₂ → β y₂ ≤ β y₁ := fun y₁ y₂ h12 ↦ by
  -- Given arbitrary $y_1 \leq y_2$ in the closure of $Y$, there are, by definition, $y_1'$ and $y_2'$ s.t., $y_1 = \alpha \beta y_1'$ and so on
  obtain ⟨y₁', h1⟩ := y₁.2
  obtain ⟨y₂', h2⟩ := y₂.2
  -- Then to prove $\beta y_1 \leq \beta y_2$, we only need to show $\beta \alpha \beta y_1' \leq \beta \alpha \beta y_2'$, which, by antitone Galois connection, is equivalent to $\alpha (\beta y_1') \leq \alpha (\beta (\alpha (\beta y_2')))$.
  -- Using the conjugate cancellation, we get $\alpha (\beta y_1') \leq \alpha (\beta y_2')$.
  rw [← h1, ← h2, Function.comp_apply, Function.comp_apply, ← hGal, conj_eq' _ _ hGal]
  -- This is exactly $y_1 \leq y_2$
  rw [Function.comp_apply, h1, h2] at *
  exact h12
  
/-! Informal proof:
An antitone Galois connection between two preordered sets
  $\alpha$ and $\beta$ consists of two maps $l : \alpha \rightarrow \beta$
  and $u : \beta \rightarrow \alpha$ such that $\forall a \in \alpha$
  and $b \in \beta$, $b \leq l a \leftrightarrow a \leq u b$.

Preparation:
1. Under the setup of a Galois connection, every $x \in X \leq \beta (\alpha x)$.
 - Since $\forall x \in X, \alpha x \leq \alpha x$
 - Then by antitone Galois connection, $x \leq \beta (\alpha x)$
2. Similarly, under the setup of a Galois connection, every $y \in Y \leq \alpha (\beta y)$.
3. Under the setup of a Galois connection, conjugate action $\alpha \beta \alpha$ is only $\alpha$: We use the antisymmetic property
 - first, we've proved that $x \leq \beta (\alpha x)$, substitute $x$ with $\beta (\alpha x)$ then we got $x \leq \beta (\alpha x) \leq \beta (\alpha (\beta (\alpha x)))$
 - then by antitone Galois connection, where we substitute $a$ for $x$ and $b$ for $\alpha (\beta (\alpha x))$, we can directly get $\alpha (\beta (\alpha x)) \leq \alpha x$.
 - For the other direction, first by reflexivity, $\beta (\alpha x) \leq \beta (\alpha x)$ then it follows from antitone Galois connection that $\alpha x \leq \alpha (\beta (\alpha x))$.
4. Similarly we can prove the conjugate action $\beta \alpha \beta$ is only $\beta$

Defining key set and map:
1. Define the closure of $X$ as the image of $\beta \alpha$
2. Define the closure of $Y$ as the image of $\alpha \beta$
3. Restrict $\alpha$ to the closure of $X$, by definition, this gives a map from the closure of $X$ to the closure of $Y$
4. Restrict $\beta$ to the closure of $Y$, by definition, this gives a map from the closure of $Y$ to the closure of $X$

Proof:
1. Then the restricted maps are bijective, and they are each other's inverse
 - We prove this by showing that the restricted $\beta$ is the left and right inverse of the restricted $\alpha$
 - Left inverse: By definition there should be a $x'$ such that $x = \beta \alpha x'$. Thus $\beta \alpha x = \beta \alpha \beta \alpha x' = \beta \alpha x' = x$
 - Right inverse: similarly there should be a $y'$ s.t., $y = \alpha \beta y'$, then $\alpha \beta y = \alpha \beta \alpha \beta y' = \alpha \beta y' = y$
2. The restricted $\alpha$ is order-reversing
 - Given arbitrary $x_1 \leq x_2$ in the closure of $X$, there are, by definition, $x_1'$ and $x_2'$ s.t., $x_1 = \beta \alpha x_1'$ and so on
 - Then to prove $\alpha x_1 \leq \alpha x_2$, we only need to show $\alpha \beta \alpha x_1' \leq \alpha \beta \alpha x_2'$, which, by antitone Galois connection, is equivalent to $\beta (\alpha x_1') \leq \beta (\alpha (\beta (\alpha x_2')))$.
 - Using the conjugate cancellation, we get $\beta (\alpha x_1') \leq \beta (\alpha x_2')$. This is exactly $x_1 \leq x_2$
3. The restricted $\beta$ is order-reversing for similar reason.
-/
