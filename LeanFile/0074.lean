import Mathlib
/-! Question:
14. Let $G=A_{1} \times A_{2} \times \cdots \times A_{n}$ and for each $i$ let $B_{i}$ be a normal subgroup of $A_{i}$. Prove that $B_{1} \times B_{2} \times \cdots \times B_{n} \unlhd G$ and that
\[
\left(A_{1} \times A_{2} \times \cdots \times A_{n}\right) /\left(B_{1} \times B_{2} \times \cdots \times B_{n}\right) \cong\left(A_{1} / B_{1}\right) \times\left(A_{2} / B_{2}\right) \times \cdots \times\left(A_{n} / B_{n}\right) \text {. }
\]

The following exercise describes the direct product of an arbitrary collection of groups. The terminology for the Cartesian product of an arbitrary collection of sets may be found in the Appendix.
-/
open Subgroup QuotientGroup

variable {n : ℕ}
variable {A : Fin n → Type*} [∀ i, Group (A i)]
variable {B : ∀ i, Subgroup (A i)} [∀ i, (B i).Normal]

/-- 正规子群的直积是直积的正规子群. -/
lemma direct_product_normal_subgroup (G : (i : Fin n) → Type*) [∀ i, Group (G i)]
  (Bi : ∀ i, Subgroup (G i)) [h : ∀ i, (Bi i).Normal] :
  (Subgroup.pi Set.univ Bi).Normal :=
  -- 使用正规子群的定义进行证明, 证明 x * a * x⁻¹ 属于 pi Set.univ Bi, 需要证明它的第 i 个分量属于 Bi i.
  -- 由于 Bi i 是正规子群, 可以使用 (h i).conj_mem, 它表示正规子群的共轭元素仍然在该子群中.
  Subgroup.Normal.mk fun _ ha _ => fun i hi => (h i).conj_mem _ (ha i hi) _

instance : (pi Set.univ B).Normal := direct_product_normal_subgroup A B

-- #check Pi.monoidHom fun (i : Fin n) => QuotientGroup.mk' (B i)
noncomputable def direct_product_quotient_iso_product_quotient :
    (Π i, A i) ⧸ (pi Set.univ B) ≃* (Π i, A i ⧸ B i) := by
    -- 定义一个群同态 f,将直积 Π i, A i 映射到商群的直积 Π i, A i ⧸ B i
    let f : (Π i, A i) →* (Π i, A i ⧸ B i) :=
    { toFun := fun x i => QuotientGroup.mk (x i)
      map_one' := by ext i; simp only [Pi.one_apply, mk_one]
      map_mul' x y := by ext i; simp only [Pi.mul_apply, mk_mul]}
    -- 证明 f 的核等于 pi Set.univ B
    have kernel_f : f.ker = pi Set.univ B := by
      -- 使用 extensionality 规则,证明两个集合相等只需证明它们的元素相同
      -- 使用 MonoidHom.mem_ker 来表明 x 在 f 的核中当且仅当 f(x) = 1
      ext x; rw [MonoidHom.mem_ker, MonoidHom.coe_mk, OneHom.coe_mk]
      -- 将 f(x) = 1 展开为对所有 i,f(x)(i) = 1, 即 x(i) 属于 B i, 即 x 属于 pi Set.univ B
      simp_rw [funext_iff, Pi.one_apply, eq_one_iff, mem_pi, Set.mem_univ, forall_const]
    -- 于是只需要证明 f 是满射即可
    apply MulEquiv.trans (QuotientGroup.quotientMulEquivOfEq kernel_f.symm)
    apply QuotientGroup.quotientKerEquivOfSurjective f fun y => ?_
    -- 仍和先前类似,逐分量应用等价类的代表元即可
    choose g hg using (fun i => Quotient.exists_rep (y i))
    exact ⟨g, funext hg⟩

/-! Informal proof:
ESS","data":{"total":3,"list":[{"created":"2024-12-20 17:41:10","updated":"2025-01-19 12:55:59","id":5762,"questionId":2699,"taskId":2591,"jobId":4604,"userId":201,"judgeUserId":223,"answer":{"informalProof":null,"formalProof":"import Mathlib
open Subgroup QuotientGroup
variable {n : ℕ}
variable {A : Fin n → Type*} [∀ i, Group (A i)]
variable {B : ∀ i, Subgroup (A i)} [∀ i, (B i).Normal]
/-- 正规子群的直积是直积的正规子群. -/
lemma direct_product_normal_subgroup (G : (i : Fin n) → Type*) [∀ i, Group (G i)]
  (Bi : ∀ i, Subgroup (G i)) [h : ∀ i, (Bi i).Normal] :
  (Subgroup.pi Set.univ Bi).Normal :=
  -- 使用正规子群的定义进行证明, 证明 x * a * x⁻¹ 属于 pi Set.univ Bi, 需要证明它的第 i 个分量属于 Bi i.
  -- 由于 Bi i 是正规子群, 可以使用 (h i).conj_mem, 它表示正规子群的共轭元素仍然在该子群中.
  Subgroup.Normal.mk fun _ ha _ => fun i hi => (h i).conj_mem _ (ha i hi) _
instance : (pi Set.univ B).Normal := direct_product_normal_subgroup A B
-- #check Pi.monoidHom fun (i : Fin n) => QuotientGroup.mk' (B i)
noncomputable def direct_product_quotient_iso_product_quotient :
    (Π i, A i) ⧸ (pi Set.univ B) ≃* (Π i, A i ⧸ B i) := by
    -- 定义一个群同态 f,将直积 Π i, A i 映射到商群的直积 Π i, A i ⧸ B i
    let f : (Π i, A i) →* (Π i, A i ⧸ B i) :=
    { toFun := fun x i => QuotientGroup.mk (x i)
      map_one' := by ext i; simp only [Pi.one_apply, mk_one]
      map_mul' x y := by ext i; simp only [Pi.mul_apply, mk_mul]}
    -- 证明 f 的核等于 pi Set.univ B
    have kernel_f : f.ker = pi Set.univ B := by
      -- 使用 extensionality 规则,证明两个集合相等只需证明它们的元素相同
      -- 使用 MonoidHom.mem_ker 来表明 x 在 f 的核中当且仅当 f(x) = 1
      ext x; rw [MonoidHom.mem_ker, MonoidHom.coe_mk, OneHom.coe_mk]
      -- 将 f(x) = 1 展开为对所有 i,f(x)(i) = 1, 即 x(i) 属于 B i, 即 x 属于 pi Set.univ B
      simp_rw [funext_iff, Pi.one_apply, eq_one_iff, mem_pi, Set.mem_univ, forall_const]
    -- 于是只需要证明 f 是满射即可
    apply MulEquiv.trans (QuotientGroup.quotientMulEquivOfEq kernel_f.symm)
    apply QuotientGroup.quotientKerEquivOfSurjective f fun y => ?_
    -- 仍和先前类似,逐分量应用等价类的代表元即可
    choose g hg using (fun i => Quotient.exists_rep (y i))
    exact ⟨g, funext hg⟩","formalStatement":null,"suggestion":null,"comment":"<p>noncomputable的证明是简单的, 但是要写出可计算的证明超出了我的知识范围</p>"},"judgement":{"result":"resubmit","score":5,"suggestion":"<p>提交的答案不能通过编译，需要修改。</p><p>审核端编译不通过</p><p style=\"text-align: justify;\"><span style=\"color: rgb(0, 0, 0); font-family: 微软雅黑;\">审核端将在如下固定版本进行Lean编译检查，以该版本编译通过为准</span></p><p style=\"text-align: justify;\"><span style=\"color: rgb(0, 0, 0); font-family: 微软雅黑;\">本地配置环境流程：</span></p><p style=\"text-align: left;\"><span style=\"font-family: 微软雅黑;\"> 1. </span><span style=\"color: rgb(0, 0, 0); font-family: 微软雅黑;\">将压缩包Archive中三个文件放在一个空文件夹里，然后命令行中运行lake update</span></p><p style=\"text-align: left;\"><span style=\"font-family: 微软雅黑;\"> 2. </span><span style=\"color: rgb(0, 0, 0); font-family: 微软雅黑;\">将题目解答的lean文件，比如AlgebraExercise.lean，放在同一文件夹下</span></p><p style=\"text-align: left;\"><span style=\"font-family: 微软雅黑;\"> 3. </span><span style=\"color: rgb(0, 0, 0); font-family: 微软雅黑;\">运行 lake env lean AlgebraExercise.lean，没有报错没有警告即可；或inforview中无报错</span></p><p style=\"text-align: left;\"><span style=\"color: rgb(51, 51, 51); font-family: 微软雅黑;\">压缩包下载链接: </span><a href=\"https://pan.baidu.com/s/1yh6OfdOc4ynx8CKsmYv2VQ\" target=\"\"><span style=\"color: rgb(30, 111, 255); font-family: 微软雅黑;\">https://pan.baidu.com/s/1yh6OfdOc4ynx8CKsmYv2VQ</span></a><span style=\"color: rgb(51, 51, 51); font-family: 微软雅黑;\"> 提取码: u1jg</span></p><p style=\"text-align: left;\"><span style=\"color: rgb(51, 51, 51); font-family: 微软雅黑;\">该版本对应的mathlib doc page地址为</span><a href=\"https://console.siflow.cn/siflow/draco/ai4math/wlli/doc-page-v1/\" target=\"\"><span style=\"color: rgb(30, 111, 255); font-family: 微软雅黑;\">https://console.siflow.cn/siflow/draco/ai4math/wlli/doc-page-v1/</span></a></p><p style=\"text-align: left;\">虽然文档没有明确要求, 但是按照惯例应写英文注释</p>","feedbackAction":"resubmit","comment":""},"stepInfo":null,"userInfo":{"id":201,"username":"shouxinzhang","nickname":"wdz001","avatar":"//p1-arco.byteimg.com/tos-cn-i-uwbnlip3yd/a8c8cdb109cb051163646151a4a5083b.png~tplv-uwbnlip3yd-webp.webp","email":"1571193735@qq.com"},"judgeUserInfo":{"id":223,"username":"Janecia","nickname":"Janecia","avatar":"//p1-arco.byteimg.com/tos-cn-i-uwbnlip3yd/a8c8cdb109cb051163646151a4a5083b.png~tplv-uwbnlip3yd-webp.webp","email":"Janecia@163.com"}},{"created":"2025-01-22 05:48:25","updated":"2025-01-26 13:30:50","id":5883,"questionId":2699,"taskId":2591,"jobId":4604,"userId":201,"judgeUserId":223,"answer":{"informalProof":null,"formalProof":"import Mathlib
open Subgroup QuotientGroup
variable {n : ℕ} {A : Fin n → Type*} [∀ i, Group (A i)]
variable {B : ∀ i, Subgroup (A i)} [∀ i, (B i).Normal]
/-- 正规子群的直积是直积的正规子群. -/
lemma direct_product_normal_subgroup (G : (i : Fin n) → Type*) [∀ i, Group (G i)]
  (Bi : ∀ i, Subgroup (G i)) [h : ∀ i, (Bi i).Normal] :
  (Subgroup.pi Set.univ Bi).Normal :=
  -- 使用正规子群的定义进行证明, 证明 x * a * x⁻¹ 属于 pi Set.univ Bi, 需要证明它的第 i 个分量属于 Bi i.
  Subgroup.Normal.mk fun _ ha _ => fun i hi => (h i).conj_mem _ (ha i hi) _
/--  `pi Set.univ B` 是 `Π i, A i` 的正规子群，因为它是正规子群的直积. -/
instance : (pi Set.univ B).Normal := direct_product_normal_subgroup A B
/-- 商群的直积同构于直积的商群. -/
noncomputable def direct_product_quotient_iso_product_quotient :
  (Π i, A i) ⧸ (pi Set.univ B) ≃* (Π i, A i ⧸ B i) := by
  -- 定义一个群同态 f,将直积 Π i, A i 映射到商群的直积 Π i, A i ⧸ B i
  let f : (Π i, A i) →* (Π i, A i ⧸ B i) :={ 
    toFun := fun x i => QuotientGroup.mk (x i)
    map_one' := by ext; simp
    map_mul' x y := by ext; simp}
  -- 证明 f 的核等于 pi Set.univ B
  have kernel_f : f.ker = pi Set.univ B := by
    -- 证明两个集合相等只需证明它们的元素相同,而 `x` 在 `f` 的核中当且仅当 `f(x) = 1`.
    ext x; rw [MonoidHom.mem_ker, MonoidHom.coe_mk, OneHom.coe_mk]
    -- 将 `f(x) = 1` 展开为对所有 `i`, `f(x)(i) = 1`, 即 `x(i)` 属于 `B i`, 即 `x` 属于 `pi Set.univ B`.
    simp_rw [funext_iff, Pi.one_apply, eq_one_iff, mem_pi, Set.mem_univ, forall_const]
  -- 于是只需要证明 `f` 是满射
  apply MulEquiv.trans (QuotientGroup.quotientMulEquivOfEq kernel_f.symm)
  apply QuotientGroup.quotientKerEquivOfSurjective f fun y => ?_
  -- 仍和先前类似,逐分量应用等价类的代表元
  choose g hg using (fun i => Quotient.exists_rep (y i))
  exact ⟨g, funext hg⟩","formalStatement":null,"suggestion":null,"comment":"<p>在<a href=\"https://live.lean-lang.org/\" target=\"_blank\">Lean4 online上编译是正常通过的.</a></p><p>中文是为了书写方便, 我认为中文完全可行(没道理语言模型无法理解中文?</p>"},"judgement":{"result":"resubmit","score":5,"suggestion":"<p>1. 目前版本规定就是4.13.0，近期内不会更换版本，lean web editor的版本是4.16.0，如果始终坚持在线编译那么将无法通过审核.</p><p>2. 注释中英均可</p>","feedbackAction":"resubmit","comment":""},"stepInfo":null,"userInfo":{"id":201,"username":"shouxinzhang","nickname":"wdz001","avatar":"//p1-arco.byteimg.com/tos-cn-i-uwbnlip3yd/a8c8cdb109cb051163646151a4a5083b.png~tplv-uwbnlip3yd-webp.webp","email":"1571193735@qq.com"},"judgeUserInfo":{"id":223,"username":"Janecia","nickname":"Janecia","avatar":"//p1-arco.byteimg.com/tos-cn-i-uwbnlip3yd/a8c8cdb109cb051163646151a4a5083b.png~tplv-uwbnlip3yd-webp.webp","email":"Janecia@163.com"}},{"created":"2025-02-28 17:19:38","updated":"2025-03-10 22:39:42","id":6009,"questionId":2699,"taskId":2591,"jobId":4604,"userId":201,"judgeUserId":223,"answer":{"informalProof":null,"formalProof":"import Mathlib
open Subgroup QuotientGroup
variable {n : ℕ} {A : Fin n → Type*} [∀ i, Group (A i)]
variable {B : ∀ i, Subgroup (A i)} [h : ∀ i, (B i).Normal]
/--  `pi Set.univ B` 是 `Π i, A i` 的正规子群，因为它是正规子群的直积. -/
instance : (pi Set.univ B).Normal :=
  Subgroup.Normal.mk fun _ ha _ => fun i hi => (h i).conj_mem _ (ha i hi) _
/-- 商群的直积同构于直积的商群. -/
noncomputable def direct_product_quotient_iso_product_quotient :
  (Π i, A i) ⧸ (pi Set.univ B) ≃* (Π i, A i ⧸ B i) := by
  -- 定义一个自然群直积同态 f,考虑证明 `(Π i, A i) ⧸ f.ker ≃* f.range = (Π i, A i ⧸ B i)`.
  letI := Pi.monoidHom (fun i ↦ (QuotientGroup.mk' (B i)).comp (Pi.evalMonoidHom A i))
  refine (quotientMulEquivOfEq ?_).trans (quotientKerEquivOfSurjective this (fun y ↦ ?_))
  -- 使用定义容易证明 `f` 的核等于 `pi Set.univ B`, 逐分量应用等价类的代表元则可证明 `f` 是满射.
  . ext1; simp [this, funext_iff, mem_pi]
  . choose g hg using fun i ↦ Quotient.exists_rep (y i); exact ⟨g, funext hg⟩","formalStatement":null,"suggestion":null,"comment":"<p>没想到时隔数月重新提交又发现了更强的压行方法</p>"},"judgement":{"result":"done","score":5,"suggestion":"<p>证明通顺，逻辑严密，完全正确，再接再厉！</p>","feedbackAction":"done","comment":null},"stepInfo":null,"userInfo":{"id":201,"username":"shouxinzhang","nickname":"wdz001","avatar":"//p1-arco.byteimg.com/tos-cn-i-uwbnlip3yd/a8c8cdb109cb051163646151a4a5083b.png~tplv-uwbnlip3yd-webp.webp","email":"1571193735@qq.com"},"judgeUserInfo":{"id":223,"username":"Janecia","nickname":"Janecia","avatar":"//p1-arco.byteimg.com/tos-cn-i-uwbnlip3yd/a8c8cdb109cb051163646151a4a5083b.png~tplv-uwbnlip3yd-webp.webp","email":"Janecia@163.com"}}]},"errorCode":0
-/
