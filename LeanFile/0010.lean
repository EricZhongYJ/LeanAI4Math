import Mathlib
/-! Question:
If $L$ be an extension of $R$, then for a monic polynomial $p \in R[X]$, the roots of $p$ in $L$ are equal to the roots of $p$ in the integral closure of $R$ in $L$.
-/

variable {R L : Type _} [CommRing R] [CommRing L] [Algebra R L]

-- 定义 p 的根在 L 中的性质
def isRootInExtendRing (p : Polynomial R) (x : L) : Prop :=
  Polynomial.aeval x p = 0

-- 定义 p 的根在整闭包中的性质
def isRootInClosure (p : Polynomial R) (x : L) : Prop :=
  (x ∈ integralClosure R L) ∧ Polynomial.aeval x p = 0

theorem roots_eq_in_extring_and_closure {x : L} (p : Polynomial R) (m : p.Monic) :
    isRootInExtendRing p x ↔ isRootInClosure p x := by
  constructor
  · -- 如果 x 是 L 中的根，则 x 在整闭包中
    intro h_root
    -- 展开 isRootInExtendRing 的定义
    rw [isRootInExtendRing] at h_root
    -- 展开 isRootInClosure 定义
    rw [isRootInClosure]
    -- 使用：x 属于整闭包 R L 当前仅当 x 在 R 上是整的
    rw [mem_integralClosure_iff, IsIntegral]
    apply And.intro
    swap
    exact h_root
    -- 展开 x 属于整闭包的元素的定义
    rw [RingHom.IsIntegralElem]
    -- 直接得证
    exists p
  · -- 如果 x 在整闭包中且是根，则 x 是 L 中的根
    rintro ⟨h_closure, h_eval⟩
    exact h_eval

/-! Informal proof:
(1) 首先，证明$p$在$L$中的根属于$R$的整闭包
设 $α \in L$，且满足 $p(a)= 0$。
由于$p$是首一多项式，系数在$R$中，因此$p$的形式为
$p(X)=X^n + a_{n-1}X^{n-1}-1+...+a_0, a_i \in R$
将 $\alpha$ 代入，得到:
$\alpha^n + a_{n-1}\alpha^{n-1}-1+...+a_0 = 0$
这表明 $\alpha$ 满足一个系数在$R$中的首一多项式方程，因此 $\alpha$ 在 R上整。
因此，$\alpha$ 属于 $L$ 中 $R$ 的整闭包
(2)其次，证明 $R$ 的整闭包中满足 $p$ 的元素属于 $p$ 的根
由于$p \in R[X]$，且$R \subseteq L$，所以$p$也属于$L[X]$。
设 $\beta \in L$ 是$R$的整闭包中的元素，且满足 $p(\beta)= 0$
因为 $\beta$ 满足 $p(\beta) = 0$，所以 $\beta$ 显然是 $p$ 在 $L$ 中的根,

-/
