import Mathlib
/-! Question:
证明 $\mathbb{Z}[\mathbb{i}]$ 是主理想环。
-/

instance : IsPrincipalIdealRing GaussianInt := EuclideanDomain.to_principal_ideal_domain

/-! Informal proof:
Mathlib4库中已有 $\mathbf{Z}[i]$ 是欧几里得整环的证明, infer_instance即可.
-/
