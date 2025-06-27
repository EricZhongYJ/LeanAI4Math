import Mathlib
/-! Question:
1. Show that the binary operation $\wedge$ on a lower semilattice $(S, \leqq)$ is idempotent, commutative, associative, and order preserving.
-/
import MathLib

example {α : Type*} [SemilatticeInf α] (a : α) : a ⊓ a = a := by
  -- the meet operation is idempotent
  exact inf_idem a

example {α : Type*} [SemilatticeInf α] (a : α) (b : α) : a ⊓ b = b ⊓ a := by
  -- the meet operation is commutative
  exact inf_comm a b

example {α : Type*} [SemilatticeInf α] (a : α) (b : α) (c : α) : a ⊓ b ⊓ c = a ⊓ (b ⊓ c) := by
  -- the meet operation is associative
  exact inf_assoc a b c

example {α : Type*} [SemilatticeInf α] (a : α) (b : α) (c : α) (h : a ≤ b) : (a ⊓ c) ≤ (b ⊓ c) := by
  -- taking meet with the same element c preserves the ordering
  exact inf_le_inf_right c h

/-! Informal proof:
## Proof
Let \((S, \leq)\) be a lower semilattice with the binary operation \(\wedge\) (meet). We need to show that the operation \(\wedge\) is idempotent, commutative, associative, and order-preserving.
### Idempotent
To show that \(\wedge\) is idempotent, we need to prove that for any \(a \in S\), \(a \wedge a = a\).
- \(a \wedge a \leq a\) (by definition of meet)
- \(a \leq a\) (by reflexivity of \(\leq\))
- \(a \leq a \wedge a\) (since \(a \leq a\) and \(a \leq a\))
By antisymmetry of \(\leq\), we have \(a \wedge a = a\).
### Commutative
To show that \(\wedge\) is commutative, we need to prove that for any \(a, b \in S\), \(a \wedge b = b \wedge a\).
- \(a \wedge b \leq b\) and \(a \wedge b \leq a\) (by definition of meet)
- \(b \wedge a \leq a\) and \(b \wedge a \leq b\) (by definition of meet)
- \(a \wedge b \leq b \wedge a\) and \(b \wedge a \leq a \wedge b\)
By antisymmetry of \(\leq\), we have \(a \wedge b = b \wedge a\).
### Associative
To show that \(\wedge\) is associative, we need to prove that for any \(a, b, c \in S\), \((a \wedge b) \wedge c = a \wedge (b \wedge c)\).
- \((a \wedge b) \wedge c \leq a \wedge b\) and \((a \wedge b) \wedge c \leq c\)
- \(a \wedge (b \wedge c) \leq a\) and \(a \wedge (b \wedge c) \leq b \wedge c\)
- \(b \wedge c \leq b\) and \(b \wedge c \leq c\)
- \(a \wedge (b \wedge c) \leq a\) and \(a \wedge (b \wedge c) \leq b\) and \(a \wedge (b \wedge c) \leq c\)
- \((a \wedge b) \wedge c \leq a\) and \((a \wedge b) \wedge c \leq b\) and \((a \wedge b) \wedge c \leq c\)
By antisymmetry of \(\leq\), we have \((a \wedge b) \wedge c = a \wedge (b \wedge c)\).
### Order-Preserving
To show that \(\wedge\) is order-preserving, we need to prove that for any \(a, b, c \in S\), if \(a \leq b\), then \(a \wedge c \leq b \wedge c\).
- \(a \leq b \implies a \wedge c \leq b\) and \(a \wedge c \leq c\)
- \(b \wedge c \leq b\) and \(b \wedge c \leq c\)
- \(a \wedge c \leq b \wedge c\)
Thus, \(\wedge\) is order-preserving.
-/
