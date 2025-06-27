import Mathlib
/-! Question:
9. Prove that the binary operation of matrix multiplication of $2 \times 2$ matrices with real number entries is associative.
-/
import Mathlib.Data.Matrix.Basic

import Mathlib.Data.Matrix.Notation




-- Define our matrix type with real entries and size 2x2

example {R : Type} [Ring R] (A B C : Matrix (Fin 2) (Fin 2) R) :

  A * B * C = A * (B * C) := by

  -- use the associative property of matrix multiplication

  simp only [Matrix.mul_assoc]

/-! Informal proof:
Define our matrix type with real entries and size 2x2. 
Use the associative property of matrix multiplication.
-/
