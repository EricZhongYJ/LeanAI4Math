import Mathlib
/-! Question:
7. Let $G_{1}, G_{2}, \ldots, G_{n}$.be groups and let $\pi$ be a fixed element of $S_{n}$. Prove that the map
$$
\varphi_{\pi}: G_{1} \times G_{2} \times \cdots \times G_{n} \rightarrow G_{\pi^{-1}(1)} \times G_{\pi^{-1}(2)} \times \cdots \times G_{\pi^{-1}(n)}
$$
defined by
$$
\varphi_{\pi}\left(g_{1}, g_{2}, \ldots, g_{n}\right)=\left(g_{\pi^{-1}(1)}, g_{\pi^{-1}(2)}, \ldots, g_{\pi^{-1}(n)}\right)
$$
is an isomorphism (so that changing the order of the factors in a direct product does not change the isomorphism type).
-/

/-- 7. Let $G_{1}, G_{2}, \ldots, G_{n}$.be groups and let $\pi$ be a fixed element of $S_{n}$. Prove that the map

$$

\varphi_{\pi}: G_{1} \times G_{2} \times \cdots \times G_{n} \rightarrow G_{\pi^{-1}(1)} \times G_{\pi^{-1}(2)} \times \cdots \times G_{\pi^{-1}(n)}

$$

defined by

$$

\varphi_{\pi}\left(g_{1}, g_{2}, \ldots, g_{n}\right)=\left(g_{\pi^{-1}(1)}, g_{\pi^{-1}(2)}, \ldots, g_{\pi^{-1}(n)}\right)

$$

is an isomorphism (so that changing the order of the factors in a direct product does not change the isomorphism type). -/
def equivCongrLeft {n : ℕ} {G : Fin n → Type*} [∀ i, Monoid (G i)] (π : Equiv.Perm (Fin n)) :
    ((i : Fin n) → G i) ≃* ((i : Fin n) → G (π.symm i)) where
  toFun := fun x i => x (π.symm i)
  invFun := fun y i => cast (by simp) (y (π i))
  left_inv := by
    intro x; ext i; beta_reduce; rw [cast_eq_iff_heq, Equiv.symm_apply_apply]
  right_inv := by
    intro x; ext i; rw [cast_eq_iff_heq, Equiv.apply_symm_apply]
  map_mul' := by
    intro x y; ext i; simp


/-! Informal proof:
ESS","data":{"total":1,"list":[{"created":"2025-04-25 13:38:48","updated":"2025-04-26 14:28:59","id":7706,"questionId":504,"taskId":2622,"jobId":5954,"userId":199,"judgeUserId":213,"answer":{"informalProof":null,"formalProof":"import Mathlib
/-- 7. Let $G_{1}, G_{2}, \ldots, G_{n}$.be groups and let $\pi$ be a fixed element of $S_{n}$. Prove that the map
$$
\varphi_{\pi}: G_{1} \times G_{2} \times \cdots \times G_{n} \rightarrow G_{\pi^{-1}(1)} \times G_{\pi^{-1}(2)} \times \cdots \times G_{\pi^{-1}(n)}
$$
defined by
$$
\varphi_{\pi}\left(g_{1}, g_{2}, \ldots, g_{n}\right)=\left(g_{\pi^{-1}(1)}, g_{\pi^{-1}(2)}, \ldots, g_{\pi^{-1}(n)}\right)
$$
is an isomorphism (so that changing the order of the factors in a direct product does not change the isomorphism type). -/
def equivCongrLeft {n : ℕ} {G : Fin n → Type*} [∀ i, Monoid (G i)] (π : Equiv.Perm (Fin n)) :
    ((i : Fin n) → G i) ≃* ((i : Fin n) → G (π.symm i)) where
  toFun := fun x i => x (π.symm i)
  invFun := fun y i => cast (by simp) (y (π i))
  left_inv := by
    intro x; ext i; beta_reduce; rw [cast_eq_iff_heq, Equiv.symm_apply_apply]
  right_inv := by
    intro x; ext i; rw [cast_eq_iff_heq, Equiv.apply_symm_apply]
  map_mul' := by
    intro x y; ext i; simp
","formalStatement":null,"suggestion":null,"comment":""},"judgement":{"result":"done","score":5,"suggestion":"<p>Prove smooth, logically rigorous, completely correct, keep up the good work!</p>","feedbackAction":"done","comment":null},"stepInfo":null,"userInfo":{"id":199,"username":"hilbert","nickname":"hilbert","avatar":"//p1-arco.byteimg.com/tos-cn-i-uwbnlip3yd/a8c8cdb109cb051163646151a4a5083b.png~tplv-uwbnlip3yd-webp.webp","email":"zhangqinchuan17@163.com"},"judgeUserInfo":{"id":213,"username":"Tristan","nickname":"Tristan","avatar":"//p1-arco.byteimg.com/tos-cn-i-uwbnlip3yd/a8c8cdb109cb051163646151a4a5083b.png~tplv-uwbnlip3yd-webp.webp","email":"ct_rabbit_math@163.com"}}]},"errorCode":0
-/
