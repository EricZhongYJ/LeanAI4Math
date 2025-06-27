import Mathlib
/-! Question:
2.1.1. 设 $A$ 是 $\mathrm{Abel}$ 群, $\operatorname{End}(A)$ 是群 $A$ 的全部自同态作成的集合. 对 $f$, $g \in \operatorname{End}(A)$ 定义
\[
(f+g)(a)=f(a)+g(a), \quad(f \cdot g)(a)=f(g(a)), \quad \forall a \in A .
\]

则 $\operatorname{End}(A)$ 对于上述运算是含么环.
-/

--We want to prove that the endomorphisms of an abelian group form a ring with addition and composition of endomorphisms as addition and multiplication respectively, which means the group must be defined as an addcommgroup, otherwise the addition in the ring should be defined as (f,g)↦f*g.
--The instance is already defined in the file addmonoid.lean.
instance commendring {G : Type*} [AddCommGroup G] : Ring (AddMonoid.End G) := AddMonoid.End.instRing
/-! Informal proof:

We want to prove that the endomorphisms of an abelian group form a ring with addition and composition of endomorphisms as addition and multiplication respectively, which means the group must be defined as an addcommgroup, otherwise the addition in the ring should be defined as (f,g)↦f*g.
The instance is already defined in the file addmonoid.lean.

-/
