import Mathlib
/-! Question:
4. A Galois connection between two partially ordered sets $X$ and $Y$ is a pair of order reversing mappings $F: X \longrightarrow Y, G: Y \longrightarrow X\left(x^{\prime} \leqq x^{\prime \prime}\right.$ implies $F x^{\prime} \geqq F x^{\prime \prime}, y^{\prime} \leqq y^{\prime \prime}$ implies $G y^{\prime} \geqq G y^{\prime \prime}$ ) such that $F G y \geqq y$ and $G F x \geqq x$ for all $x, y$. Show that $F$ and $G$ induce mutually inverse, order reversing bijections between $\{x \in X \mid G F x=x\}$ and $\{y \in Y \mid F G y=y\}$.
-/

-- define partial order X and Y
variable {X Y : Type _} [PartialOrder X] [PartialOrder Y]

-- define galois connection
-- A Galois connection between two partially ordered sets $X$ and $Y$ is a pair of order reversing mappings $F: X \\longrightarrow Y, G: Y \\longrightarrow X\\left(x^{\\prime} \\leqq x^{\\prime \\prime}\\right.$ implies $F x^{\\prime} \\geqq F x^{\\prime \\prime}, y^{\\prime} \\leqq y^{\\prime \\prime}$ implies $G y^{\\prime} \\geqq G y^{\\prime \\prime}$ ) such that $F G y \\geqq y$ and $G F x \\geqq x$ for all $x, y$.
structure galois_connection (F : X → Y) (G : Y → X) where
  f_is_order_reverse : ∀(x1 x2 : X), x1 ≤ x2 → F x1 ≥ F x2 -- F is order reversing mapping
  g_is_order_reverse : ∀(y1 y2 : Y), y1 ≤ y2 → G y1 ≥ G y2 -- G is order reversing mapping
  h : ∀(x : X) (y : Y), F (G y) ≥ y ∧ G (F x) ≥ x

-- construct sub_f mapping from $\\{x \\in X \\mid G F x=x\\}$ to $\\{y \\in Y \\mid F G y=y\\}$
def sub_f (F : X → Y) (G : Y → X) (x : { x // G (F x) = x }) : { y // F (G y) = y } := by
  apply Subtype.mk (F x)
  rw [x.property]

-- construct sub_g mapping from $\\{y \\in Y \\mid F G y=y\\}$ to $\{x \\in X \\mid G F x=x\\}$
def sub_g (F : X → Y) (G : Y → X) (y : { y // F (G y) = y }) : { x // G (F x) = x } := by
  apply Subtype.mk (G y)
  rw [y.property]

-- Show that $F$ and $G$ induce mutually inverse, order reversing bijections between $\\{x \\in X \\mid G F x=x\\}$ and $\\{y \\in Y \\mid F G y=y\\}$.
theorem galois_connection_bijection (F : X → Y) (G : Y → X) (c : galois_connection F G):
  let sf := sub_f F G;
  let sg := sub_g F G;
  -- $F$ and $G$ is mutually inverse bijection
  (∀x, sg (sf x) = x) ∧ (∀y, sf (sg y) = y) ∧
  -- $F$ and $G$ is order reverseing mapping
  (∀x1 x2 : { x // G (F x) = x }, x1 ≤ x2 → sf x1 ≥ sf x2) ∧ (∀y1 y2 : { y // F (G y) = y }, y1 ≤ y2 → sg y1 ≥ sg y2) := by
    -- proof of $F$ is mutually inverse bijection
    apply And.intro
    intro x
    rw [sub_g]
    -- convert subtype to its value
    apply Subtype.ext
    simp
    rw [sub_f]
    simp
    -- directly using $G(F(x)) = x$ to prove
    rw [x.property]
    -- proof of $G$ is mutually inverse bijection
    apply And.intro
    intro y
    rw [sub_f]
    apply Subtype.ext
    simp
    rw [sub_g]
    simp
    rw [y.property]
    apply And.intro
    -- proff of $F$ is order reverseing mapping
    intro x1 x2 leq
    -- get f is order reverse from galois connection
    have fxleq := c.f_is_order_reverse x1 x2 leq
    rw [GE.ge]
    rw [GE.ge] at fxleq
    -- convert subtype $\leq$ to its value's $\leq$
    rw [Subtype.mk_le_mk]
    exact fxleq
    -- proff of $G$ is order reverseing mapping
    intro y1 y2 leq
    have gxleq := c.g_is_order_reverse y1 y2 leq
    rw [GE.ge]
    rw [GE.ge] at gxleq
    rw [Subtype.mk_le_mk]
    exact gxleq


/-! Informal proof:
### 1. Proof of $F$ and $G$ induce mutually inverse bijection between $\{ x \in X \mid GFx = x \}$ and $\{y \in Y \mid FGy = y\}$
This proposition is equivalence to $G(F(x)) = x$ and $F(G(y)) = y$ when $\{ x \in X \mid GFx = x \}$ and $\{y \in Y \mid FGy = y\}$
Just prove this by definition.
### 2. Proof of $F$ and $G$ is order reverseing mapping
It can be proved by its definition: $x^{'} \leq x^{''} \to Fx^{'} \leq Fx^{''}$
-/
