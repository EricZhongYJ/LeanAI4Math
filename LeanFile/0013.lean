import Mathlib
/-! Question:
5. Prove that every intersection of sublattices of a lattice $L$ is a sublattice of $L$.
-/
CESS","data":{"total":1,"list":[{"created":"2024-11-14 15:13:08","updated":"2024-11-28 19:36:06","id":5498,"questionId":6883,"taskId":2435,"jobId":4377,"userId":230,"judgeUserId":196,"answer":{"informalProof":"Lattice means for every two elements of a partial order set L has their supremum and infimum in the same set L。

The sublattice of Lattice L  which is the subset of L is lattice as well.

Therefore, for two sublattices of lattice L, named s t ⊆ L, every two elements, named a, b ∈ s ∩ t，

 supremum( a, b ) ∈ s  due to sublattice s is a lattice, where as infimum (a, b) ∈ s .

The same reason for sublattice t, that is, supremum( a, b ) ∈ t  due to sublattice s is a lattice, where as infimum (a, b) ∈ t .

So, in conclusion, we have  supremum( a, b ) ∈ s  and supremum( a, b ) ∈ t, that is supremum( a, b ) ∈  s ∩ t ; whereas infimum( a, b ) ∈ s  and infimum( a, b ) ∈ t, that is infimum( a, b ) ∈  s ∩ t. By the way, s ∩ t ⊆ L due to s t ⊆ L.

Therefore,  every intersection of sublattices of a lattice L is a sublattice of L.","formalProof":"/-- A set `s` is *sup-closed* if `a ⊔ b ∈ s` for all `a ∈ s`, `b ∈ s`. -/
def SupClosed (s : Set α) : Prop := ∀ ⦃a⦄, a ∈ s → ∀ ⦃b⦄, b ∈ s → a ⊔ b ∈ s
lemma SupClosed.inter (hs : SupClosed s) (ht : SupClosed t) : SupClosed (s ∩ t) :=
  fun _a ha _b hb ↦ ⟨hs ha.1 hb.1, ht ha.2 hb.2⟩
/-- A set `s` is *inf-closed* if `a ⊓ b ∈ s` for all `a ∈ s`, `b ∈ s`. -/
def InfClosed (s : Set α) : Prop := ∀ ⦃a⦄, a ∈ s → ∀ ⦃b⦄, b ∈ s → a ⊓ b ∈ s
lemma InfClosed.inter (hs : InfClosed s) (ht : InfClosed t) : InfClosed (s ∩ t) :=
  fun _a ha _b hb ↦ ⟨hs ha.1 hb.1, ht ha.2 hb.2⟩

/-- A set `s` is a *sublattice* if `a ⊔ b ∈ s` and `a ⊓ b ∈ s` for all `a ∈ s`, `b ∈ s`.
Note: This is not the preferred way to declare a sublattice. One should instead use `Sublattice`.
TODO: Define `Sublattice`. -/
structure IsSublattice (s : Set α) : Prop where
  supClosed : SupClosed s
  infClosed : InfClosed s

lemma IsSublattice.inter (hs : IsSublattice s) (ht : IsSublattice t) : IsSublattice (s ∩ t) :=
  ⟨hs.1.inter ht.1, hs.2.inter ht.2⟩","formalStatement":null,"suggestion":null,"comment":"<p>This formal proof does already exist in the Order part of Mathlib. I pose it directly.</p>"},"judgement":{"result":"done","score":5,"suggestion":"<p>证明通顺，逻辑严密，完全正确，再接再厉！</p>","feedbackAction":"done","comment":"<p><br></p>"},"stepInfo":null,"userInfo":{"id":230,"username":"keithtsui","nickname":"KeithTsui","avatar":"//p1-arco.byteimg.com/tos-cn-i-uwbnlip3yd/a8c8cdb109cb051163646151a4a5083b.png~tplv-uwbnlip3yd-webp.webp","email":"pixxf@me.com"},"judgeUserInfo":{"id":196,"username":"WanyiHe","nickname":"WanyiHe","avatar":"//p1-arco.byteimg.com/tos-cn-i-uwbnlip3yd/a8c8cdb109cb051163646151a4a5083b.png~tplv-uwbnlip3yd-webp.webp","email":"2100017455@stu.pku.edu.cn"}}]},"errorCode"
  
/-! Informal proof:
Lattice means for every two elements of a partial order set L has their supremum and infimum in the same set L。
The sublattice of Lattice L  which is the subset of L is lattice as well.
Therefore, for two sublattices of lattice L, named s t ⊆ L, every two elements, named a, b ∈ s ∩ t，
 supremum( a, b ) ∈ s  due to sublattice s is a lattice, where as infimum (a, b) ∈ s .
The same reason for sublattice t, that is, supremum( a, b ) ∈ t  due to sublattice s is a lattice, where as infimum (a, b) ∈ t .
So, in conclusion, we have  supremum( a, b ) ∈ s  and supremum( a, b ) ∈ t, that is supremum( a, b ) ∈  s ∩ t ; whereas infimum( a, b ) ∈ s  and infimum( a, b ) ∈ t, that is infimum( a, b ) ∈  s ∩ t. By the way, s ∩ t ⊆ L due to s t ⊆ L.
Therefore,  every intersection of sublattices of a lattice L is a sublattice of L.
-/
