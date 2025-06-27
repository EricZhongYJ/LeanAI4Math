import Mathlib
/-! Question:
4.56 Let $A$ be an $n \times n$ matrix over a field $k$. If $c$ is an eigenvalue of $A$, prove, for all $m \geq 1$, that $c^{m}$ is an eigenvalue of $A^{m}$.
-/

variable (K : Type _) [Field K]
variable {n : ℕ} (A : Matrix (Fin n) (Fin n) K)

-- Let $A$ be an $n \\times n$ matrix over a field $k$. If $c$ is an eigenvalue of $A$, prove, for all $m \\geq 1$, that $c^{m}$ is an eigenvalue of $A^{m}$.
example (c : K) (v : (Fin n) → K) (m : ℕ) (h : A.mulVec v = c • v) : ((A^(m+1)).mulVec v = c^(m+1) • v) := by {
  induction m with
  | zero => {
    simp
    exact h
  }
  | succ d hd => {
    -- 两边同时乘以 $A$, 得到 $A^{m+1}v = Ac^{m}v$
    apply congrArg (A.mulVec) at hd; simp at hd
    -- 化简, 得到 $A^{m+2}v = Ac^{m+1}v$
    rw [← pow_mul_comm', ← pow_succ, Matrix.mulVec_smul] at hd
    -- 对 $Ac^{m+1}v$ 使用条件 $Av = cv$ 得到 $A^{m+2}v = c^{m+1}v$
    rw [h] at hd
    -- 将 $A^{m+2}v = c^{m+2}=v$ 中的 $A^{m+2}v$ 替换为上边得到的 $c^{m+2}v$
    rw [hd]
    rw [← smul_assoc]
    rw [smul_eq_mul]
    ring_nf
  }
}


/-! Informal proof:
对 m 使用数学归纳法，当 m = 1 时易证，证明略
当 $m=k$ 时，我们有 $A^{k}v = c^{k}v$，我们需要证明 $A^{k+1}v = c^{k+1}v$
我们对 $A^{k}v = c^{k}v$ 等式两边左乘一个 $A$ 得到 $A^{k+1} = Ac^{k}v$
再对 $A^{k+1} = Ac^{k}v$ 运用条件 $Av = cv$ 得到 $A^{k+1} = c^{k+1}v$，得证
-/
