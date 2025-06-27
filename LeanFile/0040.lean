import Mathlib
/-! Question:
*4.34 Let $U$ be a subspace of a vector space $V$.
(i) Prove that the natural map $\pi: V \rightarrow V / U$, given by $v \mapsto v+U$, is a linear transformation with kernel $U$.
(ii) State and prove the first isomorphism theorem for vector spaces.
-/

/- Problem Description
  Let $U$ be a subspace of a vector space $V$.
  (i) Prove that the natural map $\pi: V \to V/U$, given by $v \mapsto v + U$, is a linear transformation with kernel $U$.
  (ii) State and prove the first isomorphism theorem for vector spaces.
-/

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
variable (H: AddSubgroup V)
variable (U: Submodule K V)

-- let π be a natural mapping
def π: V -> V ⧸ U := Submodule.Quotient.mk

-- π is a linear transformation
def π_linear : V →ₗ[K] V ⧸ U where
  toFun := π U
  map_add' := by simp [π]
  map_smul' := by simp [π]

-- kernel of π is U
theorem kernel_is_U: LinearMap.ker (π_linear U) = U := by
  unfold LinearMap.ker
  ext x; simp [π_linear, π]

-- Let W be a vector space and f: V -> W be a linear mapping
variable {W: Type*} [AddCommGroup W] [Module K W]
variable (f: V →ₗ[K] W)

-- the kernel of f is a subspace of V
def kernel: Submodule K V where
  carrier :=  LinearMap.ker f
  add_mem':= by {
    simp; intro a b fa fb
    rw [fa, fb]; simp
  }
  zero_mem':= by simp
  smul_mem' := by {
    simp; intro _ x fx
    right; assumption
  }

-- the image of f is a subspace of W
def image: Submodule K W where
  carrier :=  LinearMap.range f
  add_mem':= by {
    simp; intro a b x1 ha x2 hb
    use (x1 + x2)
    simp [ha, hb]
  }
  zero_mem':= by simp
  smul_mem' := by {
    simp; intro c a
    use (c • a)
    simp
  }

-- (V ⧸ kernel f) is isomophic to the image of f
noncomputable def isomorphism: (V ⧸ kernel f) ≃ₗ[K] image f :=
  f.quotKerEquivRange

/-! Informal proof:
(i) For any $u, v \in V$ and scalar $c \in K$,
$\pi(u) + \pi(v) = (u+U) + (v+U) = (u+v) + U = \pi(u+v)$
where the second equation is from the definition of the addition on 
$V/U$. Besides, $c\pi(u) = \pi(cu)$ also follows from the
definition of the scalar multiplication on $V/U$.
Therefore $\pi$ is a linear transformation.
Besides for any $x \in V$, 
$$\pi(x) = U \iff \{ x + u: u \in U \} = U \iff x \in U $$
Therefore $\ker \pi = \{x \in V : \pi(x) = U \} = U$.
(ii) The first isomorphism theorem for vector spaces states that, if $W$ is a vector space and $f: V \to W$ is a linear mapping, then:
- the kernel of $f$ is a subspace of $V$
- the image of $f$ is a subsapce of $W$
- $V/ \ker f$ is isomorphic to $\text{im } f$
To prove the first statement, we only need to show $\ker f$ is closed under addition and scalar multiplication:
- if $f(a) = f(b) = 0$, then $f(a+b) = f(a) + f(b) = 0 + 0 = 0$, so $a+b \in \ker f$.
- if $f(a)=0$, then $f(c\cdot a) = c \cdot f(a) = c \cdot 0 = 0$, so $c \dot 0 \in \ker f$.
To prove the second statement, we only need to show $\text{im }f$ is closed under addition and scalar multiplication:
- $f(a) + f(b) = f(a+b)$, so $f(a) + f(b) \in \text{im }f$.
- $c \cdot f(a) = f(c \cdot a)$, so $c \cdot f(a) \in \text{im }f$.
The last statement simply follows from the first isomorphism theorem for the underlying additive group and $f$ preserves scalar multiplication.
-/
