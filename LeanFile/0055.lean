import Mathlib
/-! Question:
3. Show that $G L_{2}\left(\mathbb{F}_{2}\right)$ is non-abelian.
-/

def GL2_F2_nonabelian : ∃ (a b : (GL (Fin 2) (ZMod 2))), ¬ Commute a b:= by
  -- 定义 $G L_{2}\left(\mathbb{F}_{2}\right)$ 中矩阵 $a$ 为 $\begin{bmatrix}1 & 1\\0 & 1\end{bmatrix}$,
  let a : GL (Fin 2) (ZMod 2) := Matrix.GeneralLinearGroup.mk''
    ![![1, 1],
      ![0, 1]]
    (by decide)
  -- 定义 $G L_{2}\left(\mathbb{F}_{2}\right)$ 中矩阵 $b$ 为 $\begin{bmatrix}1 & 1\\0 & 1\end{bmatrix}$.
  let b : GL (Fin 2) (ZMod 2) := Matrix.GeneralLinearGroup.mk''
    ![![1, 0],
      ![1, 1]]
    (by decide)
  -- 直接计算有 $a * b ≠ b * a$, 因而 $G L_{2}\left(\mathbb{F}_{2}\right)$ 非交换.
  use a, b
  rw [commute_iff_eq]
  dsimp only [a, b]
  decide

/-! Informal proof:
1. 定义 $G L_{2}\left(\mathbb{F}_{2}\right)$ 中矩阵 $a$ 为 $\begin{bmatrix}1 & 1\\0 & 1\end{bmatrix}$, 定义 $G L_{2}\left(\mathbb{F}_{2}\right)$ 中矩阵 $b$ 为 $\begin{bmatrix}1 & 1\\0 & 1\end{bmatrix}$.
2. 直接计算有 $a * b ≠ b * a$, 因而 $G L_{2}\left(\mathbb{F}_{2}\right)$ 非交换.
-/
