import Mathlib
/-! Question:
1. Prove that $D_{16}, Z_{2} \times D_{8}, Z_{2} \times Q_{8}$ are nonisomorphic non-abelian groups of order 16.
-/

variable {G : Type*} [Group G] [DecidableEq G] [Fintype G]
set_option maxHeartbeats 900000


--First we prove that $D_16$ is non-abelian,we choose two elements r and sr, and prove that they do not commute.
example : ∃ (a : DihedralGroup 8) (b : DihedralGroup 8) , a * b ≠ b * a := by
    use (DihedralGroup.r 1) ; use (DihedralGroup.sr 1);simp
    rw [@one_add_one_eq_two,← @Ne.eq_def]
    exact ne_of_beq_false rfl

--Next we prove that $Z_2 × D_8$ is non-abelian,we choose two elements (1,r) and (1,sr), and prove that they do not commute.
example : ∃ (a : G × (DihedralGroup 4)) (b : G × (DihedralGroup 4)) , a * b ≠ b * a := by
    use ((1,DihedralGroup.r 1)) ; use ((1,DihedralGroup.sr 1));simp
    rw [@one_add_one_eq_two,← @Ne.eq_def]
    exact ne_of_beq_false rfl

--Next we prove that $Z_2× Q_8$ is non-abelian,we choose two elements (1,xa 1) and (1,a1), and prove that they do not commute.
example  : ∃ (a : G × (QuaternionGroup 2)) (b : G × (QuaternionGroup 2)) , a * b ≠ b * a := by
    use ((1,QuaternionGroup.a 1)) ; use ((1,QuaternionGroup.xa 1));simp
    rw [@one_add_one_eq_two,← @Ne.eq_def]
    exact ne_of_beq_false rfl


--Then we prove that D16 and Z2× D8 are nonisomorphic using the fact that the order of r in $D_16$ is 16, while the order of the elements in Z2× D8 is at most 8.

--We need the first lemma to prove that the isomorphism preserves the order of the elements,which is easy.
lemma iso_order_eq {G H: Type*} [Group G] [Group H] (f : G ≃* H) (x : G) :orderOf (f x) = orderOf x := by
    rw [@orderOf_eq_orderOf_iff]
    intro n
    rw [← @map_pow,@MulEquiv.map_eq_one_iff]

--Then we need the second lemma that the order of the elements in $G × D_8 $ is at most 4 as the order of G is 2 and the exponent of $D_8$ is 4.
lemma orderZD  (hg : Nat.card G = 2): ∀ (x : G × (DihedralGroup 4)), orderOf x ≤ 4 := by
    intro x
    refine orderOf_le_of_pow_eq_one ?hn ?h;exact Nat.zero_lt_succ 3
    rw [@Prod.pow_def];simp
    constructor
    · have : x.1 ^ 2 = 1 := by
        rw [← hg]
        exact pow_card_eq_one'
      have hh: x.1 ^ 4 = (x.1 ^ 2) ^ 2 := by
        rw [← @npow_mul]
      rw [hh,this];simp
    · have := @DihedralGroup.exponent 4
      have hh : lcm 4 2 = 4 := by
        exact rfl
      rw [hh] at this
      have uu:= Monoid.pow_exponent_eq_one x.2
      rw [this] at uu;tauto
--The same as the third lemma, we can prove that the order of the elements in $Z_2× Q_8$ is at most 4.
lemma orderZQ  (hg : Nat.card G = 2) : ∀ (x : G × (QuaternionGroup 2)), orderOf x ≤ 4 := by
    intro x
    refine orderOf_le_of_pow_eq_one ?hn ?h;exact Nat.zero_lt_succ 3
    rw [@Prod.pow_def];simp
    constructor
    · have : x.1 ^ (Nat.card G) = 1 := by
        exact pow_card_eq_one'
      rw [hg] at this
      have hh: x.1 ^ 4 = (x.1 ^ 2) ^ 2 := by
        rw [← @npow_mul]
      rw [hh,this];simp
    · have := @QuaternionGroup.exponent 2
      have hh : lcm 2 2 = 2 := by
        exact rfl
      rw [hh] at this
      have uu:= Monoid.pow_exponent_eq_one x.2
      rw [this] at uu;tauto

--Using the first lemma and the fact that the order of r in $D_16$ is 16, we can prove that $D_{16}$ and $Z_2× D_8$ are nonisomorphic.
example [Group G] (hg : Nat.card G = 2) (f : (DihedralGroup 8) ≃* (G × (DihedralGroup 4))) : false := by
    have h2 := @DihedralGroup.orderOf_r_one 8
    have h3 : orderOf (f (@DihedralGroup.r 8 1)) = 8 := by
        have : orderOf (f (@DihedralGroup.r 8 1)) = orderOf (@DihedralGroup.r 8 1) := iso_order_eq f (DihedralGroup.r 1)
        linarith
    have := orderZD hg (f (@DihedralGroup.r 8 1))
    linarith

--The same way, we can prove that $D_{16}$ and $Z_2× Q_8$ are nonisomorphic.
example [Group G] (hg : Nat.card G = 2) (f : (DihedralGroup 8) ≃* G × (QuaternionGroup 2)) : false := by
    have h2 := @DihedralGroup.orderOf_r_one 8
    have h3 : orderOf (f (@DihedralGroup.r 8 1)) = 8 := by

        have : orderOf (f (@DihedralGroup.r 8 1)) = orderOf (@DihedralGroup.r 8 1) := by
            exact iso_order_eq f (DihedralGroup.r 1)
        linarith

    have := orderZQ hg (f (@DihedralGroup.r 8 1))
    linarith


--It is easy that if $G$ is a group with two elements, then the order of the elements in $G$ is 1 or 2.
lemma od12  (hg : Nat.card G = 2) : ∀ x : G, orderOf x = 1 ∨ orderOf x = 2 := by
    intro x
    have :x ^ 2 = 1 := by
      rw [← hg];exact pow_card_eq_one'
    rw [← @orderOf_dvd_iff_pow_eq_one] at this
    have hx: 0 < 2 := Nat.zero_lt_succ 1
    have hx1 : 0 < orderOf x := orderOf_pos x
    have := Nat.le_of_dvd hx this;rw [@Nat.le_add_one_iff,@Nat.le_succ_iff_eq_or_le] at this;simp only [Nat.succ_eq_add_one,
        zero_add, nonpos_iff_eq_zero, Nat.reduceAdd] at this
    rcases this with h1|h2;rcases h1 with h3|h4;exact Or.inl h3;linarith;exact Or.inr h2


lemma ttt (hg : Nat.card G = 2) (x : G × (DihedralGroup 4)) : orderOf x = 4 ↔  orderOf x.2 = 4 := by
  have x1 := od12 hg x.1
  constructor
--To prove lemma ttt, we need to prove two directions. First, we prove that if the order of x is 4, then the order of x.2 is 4 and we use the property of the order of the product of two elements.
  · intro hx;rw [@Prod.orderOf] at hx
    have := Nat.dvd_lcm_right (orderOf x.1) (orderOf x.2);rw [hx] at this
    have h44 : 0 < 4 := Nat.zero_lt_succ 3
    have hxxx := Nat.le_of_dvd h44 this
--We cases with x.1 and x.2 one by one to prove that the order of x.2 is 4.
    rcases x1 with h1|h2
    · rw [h1] at hx;simp at hx;exact hx
    · rw [h2] at hx
      rw [Nat.le_add_one_iff,Nat.le_add_one_iff,Nat.le_add_one_iff,Nat.le_add_one_iff] at hxxx;simp only [Nat.succ_eq_add_one,
        zero_add, nonpos_iff_eq_zero, Nat.reduceAdd] at hxxx
      if h : orderOf x.2 = 0 then
        have : 0 < orderOf x.2 := orderOf_pos x.2
        rw [h] at this;linarith
      else if h : orderOf x.2 = 1 then
        rw [h] at hx;simp at hx
      else if h : orderOf x.2 = 2 then
        rw [h] at hx;simp at hx
      else if h : orderOf x.2 = 3 then
        rw [h] at hx;have : Nat.lcm 2 3 = 6 := rfl;rw [this] at hx;simp at hx
      else if h : orderOf x.2 = 4 then
        exact h
      else
        rw [← @Ne.eq_def] at *;tauto
  --The other direction is trivial.
  · intro hx;rw [@Prod.orderOf,hx];rcases x1 with h1|h2;rw [h1];simp;rw [h2]
    exact rfl

--We give all the elements in $D_8$ and $Q_8$ of order 4, examine the order of the 8 elements one by one.
lemma order44d (x : (DihedralGroup 4)) (hx: orderOf x = 4) : x ∈ ({@DihedralGroup.r 4 1,DihedralGroup.r 3} : Set (DihedralGroup 4)):= by
    cases x with
    | r a =>
      if h : a= 0 then
        rw [h] at hx
        have := @DihedralGroup.one_def 4
        rw [←this,@orderOf_one] at hx;tauto
      else
        fin_cases a
        simp at h;simp;rw [@DihedralGroup.orderOf_r] at hx;simp at hx
        have : (@ZMod.val 4 2 ) = 2 := by
          exact rfl
        rw[this] at hx;simp at hx;simp
    | sr a =>
      have := DihedralGroup.orderOf_sr a
      linarith


--lemma tttt as well as its proval is similar to lemma ttt.
lemma tttt  (hg : Nat.card G = 2) (x : G × (QuaternionGroup 2)) : orderOf x = 4 ↔  orderOf x.2 = 4 := by
  have x1 := od12 hg x.1
  constructor
  · intro hx;rw [@Prod.orderOf] at hx
    have := Nat.dvd_lcm_right (orderOf x.1) (orderOf x.2);rw [hx] at this
    have h44 : 0 < 4 := Nat.zero_lt_succ 3
    have hxxx := Nat.le_of_dvd h44 this

    rcases x1 with h1|h2
    · rw [h1] at hx;simp at hx;exact hx
    · rw [h2] at hx
      rw [Nat.le_add_one_iff,Nat.le_add_one_iff,Nat.le_add_one_iff,Nat.le_add_one_iff] at hxxx;simp only [Nat.succ_eq_add_one,
        zero_add, nonpos_iff_eq_zero, Nat.reduceAdd] at hxxx
      if h : orderOf x.2 = 0 then
        have : 0 < orderOf x.2 := orderOf_pos x.2
        rw [h] at this;linarith
      else if h : orderOf x.2 = 1 then
        rw [h] at hx;simp at hx
      else if h : orderOf x.2 = 2 then
        rw [h] at hx;simp at hx
      else if h : orderOf x.2 = 3 then
        rw [h] at hx;have : Nat.lcm 2 3 = 6 := rfl;rw [this] at hx;simp at hx
      else if h : orderOf x.2 = 4 then
        exact h
      else
        rw [← @Ne.eq_def] at *;tauto
  · intro hx;rw [@Prod.orderOf,hx];rcases x1 with h1|h2;rw [h1];simp;rw [h2]
    exact rfl



lemma order44q (x : (QuaternionGroup 2)) (hx : orderOf x = 4) : x ∈ ({QuaternionGroup.xa 0,QuaternionGroup.xa 1,QuaternionGroup.xa 2,QuaternionGroup.xa 3, QuaternionGroup.a 1, QuaternionGroup.a 3} : Set (QuaternionGroup 2)):= by
  cases x with
  | a m => if h : m = 0 then
      rw [h] at hx
      have := @QuaternionGroup.one_def 2
      rw [←this,@orderOf_one] at hx;tauto
    else
      fin_cases m
      simp only [Nat.reduceMul, Nat.reduceAdd, Fin.zero_eta] at h;tauto
      simp;rw [@QuaternionGroup.orderOf_a] at hx;simp at hx;have : (@ZMod.val 4 2 ) = 2 := by exact rfl
      rw[this] at hx;simp at hx;simp
  | xa m =>
    simp;fin_cases m;simp;simp;simp;simp


--Finally, we prove that $Z_2× D_8$ and $Z_2× Q_8$ are nonisomorphic.
example [Group G] [inst : NeZero 2] (hg : Nat.card G = 2) (f : G × (DihedralGroup 4) ≃* (G × (QuaternionGroup 2)))
: false := by
--We define the sets L and R, and prove that the cardinality of L is 4 and the cardinality of R is 12.
    let L : Set (G × (DihedralGroup 4)) := {a | orderOf a = 4}
    let R : Set (G × (QuaternionGroup 2)) := {a | orderOf a = 4}
--According to the lemma that iso preserves the order of the elements, we can prove that the image of L under f is R.
    have h4 : f ''(L) = R := by
        ext x
        simp only [Set.mem_image,L,R,Set.mem_setOf_eq]
        constructor
        · rintro ⟨a,ha,h⟩
          rw [← ha,← h];exact iso_order_eq f a
        · rintro h
          use f.symm x
          simp
          have : orderOf (f.symm x) = orderOf x := iso_order_eq f.symm x
          linarith
--Thus, as f is bijective, we can prove that the cardinality of L is equal to the cardinality of R.
    have hhh : Nat.card L = Nat.card (f '' (L)) := by
        exact Eq.symm (Nat.card_image_equiv f.toEquiv)
    rw [h4] at hhh
    have hgg:= Nat.card_eq_two_iff.mp hg
    rcases hgg with ⟨a,b,hg1,hg2⟩
--We can give the concrete form of L and R
    have hl : L = { (a,DihedralGroup.r 1 ),(b,DihedralGroup.r 1), (b,DihedralGroup.r 3),(a,DihedralGroup.r 3)} := by
--Using the lemma ttt, we observe that order 4 elements must have the same part in the projection to the second component.Thus, combining with the lemma order44d, we can get the form of L.
        ext x;constructor
        · rintro h
          have x11: x.1 ∈ ({a,b} : Set G) := by
            rw [hg2];exact trivial
--We cases with x.1 and x.2 one by one to prove that the two sets are equal.
          rw [@Set.mem_setOf] at h
          rw [ttt hg x] at h;have x22:= order44d x.2 h
          change (x.1,x.2) ∈ { (a,DihedralGroup.r 1 ),(b,DihedralGroup.r 1), (b,DihedralGroup.r 3),(a,DihedralGroup.r 3)}
          rcases x11 with h1|h2
          rcases x22 with h3|h4;rw [h1,h3];simp;rw[h1,h4];simp
          rcases x22 with h3|h4;rw [h2,h3];simp;rw[h2,h4];simp
        · rintro h
          rw [@Set.mem_setOf,ttt hg x]
          rcases h with h1|h2|h3|h4
          rw [h1];simp;rw [h2];simp
          rw [h3];simp;rw [@DihedralGroup.orderOf_r];tauto
          rw [h4];simp;rw [@DihedralGroup.orderOf_r];tauto
--The same way, we can get the form of R.
    have hr : R = { (a,QuaternionGroup.xa 1 ),(b,QuaternionGroup.xa 1), (b,QuaternionGroup.xa 2),(a,QuaternionGroup.xa 2),(a,QuaternionGroup.xa 0),(b,QuaternionGroup.xa 0 ),(a,QuaternionGroup.xa 3 ),(b,QuaternionGroup.xa 3 ),(a, QuaternionGroup.a 1), (b, QuaternionGroup.a 1), (a,QuaternionGroup.a 3), (b,QuaternionGroup.a 3) } := by
      ext x;constructor
      · rintro h
        have x11: x.1 ∈ ({a,b} : Set G) := by
            rw [hg2];exact trivial
        rw [@Set.mem_setOf] at h
        rw [tttt hg x] at h;have x22:= order44q x.2 h
        change (x.1,x.2) ∈ { (a,QuaternionGroup.xa 1 ),(b,QuaternionGroup.xa 1), (b,QuaternionGroup.xa 2),(a,QuaternionGroup.xa 2),(a,QuaternionGroup.xa 0),(b,QuaternionGroup.xa 0 ),(a,QuaternionGroup.xa 3 ),(b,QuaternionGroup.xa 3 ),(a, QuaternionGroup.a 1), (b, QuaternionGroup.a 1), (a,QuaternionGroup.a 3), (b,QuaternionGroup.a 3)  }
        rcases x11 with h1|h2
        rcases x22 with h3|h4|h5|h6|h7|h8;rw [h1,h3];simp;rw[h1,h4];simp;rw[h1,h5];simp;rw[h1,h6];simp;rw[h1,h7];simp;rw[h1,h8];simp
        rcases x22 with h3|h4|h5|h6|h7|h8;rw [h2,h3];simp;rw[h2,h4];simp;rw[h2,h5];simp;rw[h2,h6];simp;rw[h2,h7];simp;rw[h2,h8];simp

      · rintro h
        have := @QuaternionGroup.orderOf_a 2 inst
        rw [@Set.mem_setOf,tttt hg x]
        rcases h with h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12
        rw [h1];simp;rw [h2];simp;rw [h3];simp;rw [h4];simp;rw [h5];simp;rw [h6];simp;rw [h7];simp;rw [h8];simp;rw [h9];simp;rw [h10];simp;rw [h11];simp;
        have := this 3;simp at this;have ht : @ZMod.val 4 3 = 3 := rfl;rw [ht] at this;simp at this;exact this
        rw [h12];simp;have := this 3;simp at this;have ht : @ZMod.val 4 3 = 3 := rfl;rw [ht] at this;simp at this;exact this
--Lastly, we get the cardinality of L and R using the forms of L and R.
--In lean4, we need to check the elements of the set one by one to get the cardinality of the set, and then we get the conclusion.
    have hll : Nat.card L = 4 := by
        rw [hl]
        simp only [Nat.card_eq_fintype_card, Fintype.card_ofFinset, Set.toFinset_insert,
          Set.toFinset_singleton];refine Finset.card_eq_succ.mpr ?_
        use (a,DihedralGroup.r 1)
        use { (b,DihedralGroup.r 1), (b,DihedralGroup.r 3),(a,DihedralGroup.r 3)}
        simp;constructor;tauto
        refine Finset.card_eq_three.mpr ?h.right.a
        use (b,DihedralGroup.r 1);use (b,DihedralGroup.r 3);use (a,DihedralGroup.r 3)
        simp;constructor;tauto;constructor;tauto;rw [← @Ne.eq_def];exact hg1.symm
    have hrr : Nat.card R = 12 := by
        rw [hr]
        simp only [Nat.card_eq_fintype_card, Fintype.card_ofFinset, Set.toFinset_insert,
          Set.toFinset_singleton];refine Finset.card_eq_succ.mpr ?_
        use (a,QuaternionGroup.xa 1);use { (b,QuaternionGroup.xa 1), (b,QuaternionGroup.xa 2),(a,QuaternionGroup.xa 2),(a,QuaternionGroup.xa 0),(b,QuaternionGroup.xa 0 ),(a,QuaternionGroup.xa 3 ),(b,QuaternionGroup.xa 3 ),(a, QuaternionGroup.a 1), (b, QuaternionGroup.a 1), (a,QuaternionGroup.a 3), (b,QuaternionGroup.a 3) }
        constructor;simp;tauto;constructor;tauto
        refine Finset.card_eq_succ.mpr ?_
        use (b,QuaternionGroup.xa 1);use { (b,QuaternionGroup.xa 2),(a,QuaternionGroup.xa 2),(a,QuaternionGroup.xa 0),(b,QuaternionGroup.xa 0 ),(a,QuaternionGroup.xa 3 ),(b,QuaternionGroup.xa 3 ),(a, QuaternionGroup.a 1), (b, QuaternionGroup.a 1), (a,QuaternionGroup.a 3), (b,QuaternionGroup.a 3) }
        simp;constructor;tauto
        refine Finset.card_eq_succ.mpr ?_
        use (b,QuaternionGroup.xa 2);use { (a,QuaternionGroup.xa 2),(a,QuaternionGroup.xa 0),(b,QuaternionGroup.xa 0 ),(a,QuaternionGroup.xa 3 ),(b,QuaternionGroup.xa 3 ),(a, QuaternionGroup.a 1), (b, QuaternionGroup.a 1), (a,QuaternionGroup.a 3), (b,QuaternionGroup.a 3) }
        simp;constructor;tauto
        refine Finset.card_eq_succ.mpr ?_
        use (a,QuaternionGroup.xa 2);use { (a,QuaternionGroup.xa 0),(b,QuaternionGroup.xa 0 ),(a,QuaternionGroup.xa 3 ),(b,QuaternionGroup.xa 3 ),(a, QuaternionGroup.a 1), (b, QuaternionGroup.a 1), (a,QuaternionGroup.a 3), (b,QuaternionGroup.a 3) }
        simp;constructor;tauto
        refine Finset.card_eq_succ.mpr ?_
        use (a,QuaternionGroup.xa 0);use { (b,QuaternionGroup.xa 0 ),(a,QuaternionGroup.xa 3 ),(b,QuaternionGroup.xa 3 ),(a, QuaternionGroup.a 1), (b, QuaternionGroup.a 1), (a,QuaternionGroup.a 3), (b,QuaternionGroup.a 3) }
        simp;constructor;tauto
        refine Finset.card_eq_succ.mpr ?_
        use (b,QuaternionGroup.xa 0);use { (a,QuaternionGroup.xa 3 ),(b,QuaternionGroup.xa 3 ),(a, QuaternionGroup.a 1), (b, QuaternionGroup.a 1), (a,QuaternionGroup.a 3), (b,QuaternionGroup.a 3) }
        simp;constructor;tauto
        refine Finset.card_eq_succ.mpr ?_
        use (a,QuaternionGroup.xa 3);use { (b,QuaternionGroup.xa 3 ),(a, QuaternionGroup.a 1), (b, QuaternionGroup.a 1), (a,QuaternionGroup.a 3), (b,QuaternionGroup.a 3) }
        simp;constructor;tauto
        refine Finset.card_eq_succ.mpr ?_
        use (a, QuaternionGroup.a 1);use { (b, QuaternionGroup.a 1), (a,QuaternionGroup.a 3), (b,QuaternionGroup.a 3) };simp;constructor;tauto
        refine Finset.card_eq_succ.mpr ?_
        use (b, QuaternionGroup.a 1);use { (a,QuaternionGroup.a 3), (b,QuaternionGroup.a 3) };simp;constructor;tauto
        refine Finset.card_eq_succ.mpr ?_
        use (a,QuaternionGroup.a 3);use { (b,QuaternionGroup.a 3) };simp;tauto

    linarith


/-! Informal proof:
First we prove that $D_16$ is non-abelian,we choose two elements r and sr, and prove that they do not commute.Next we prove that $Z_2 × D_8$ is non-abelian,we choose two elements (1,r) and (1,sr), and prove that they do not commute.Next we prove that $Z_2× Q_8$ is non-abelian,we choose two elements (1,xa 1) and (1,a1), and prove that they do not commute.
Then we prove that D16 and $Z_2× D_8$ are nonisomorphic using the fact that the order of r in $D_16$ is 16, while the order of the elements in $Z_2× D_8$ is at most 8.We need the first lemma to prove that the isomorphism preserves the order of the elements,which is easy.
Then we need the second lemma that the order of the elements in $ G × D_8 $ is at most 4 as the order of G is 2 and the exponent of $D_8$ is 4.
The same as the third lemma, we can prove that the order of the elements in $Z_2× Q_8$ is at most 4.
Using the first lemma and the fact that the order of r in $D_16$ is 16, we can prove that $D_{16}$ and $Z_2× D_8$ are nonisomorphic.
The same way, we can prove that $D_{16}$ and $Z_2× Q_8$ are nonisomorphic.
It is easy that if $G$ is a group with two elements, then the order of the elements in $G$ is 1 or 2.
To prove lemma ttt, we need to prove two directions. First, we prove that if the order of x is 4, then the order of x.2 is 4 and we use the property of the order of the product of two elements.
We cases with x.1 and x.2 one by one to prove that the order of x.2 is 4.
The other direction is trivial.
We give all the elements in $D_8$ and $Q_8$ of order 4, examine the order of the 8 elements one by one.
lemma tttt as well as its proval is similar to lemma ttt.
Finally, we prove that $Z_2× D_8$ and $Z_2× Q_8$ are nonisomorphic.
According to the lemma that iso preserves the order of the elements, we can prove that the image of L under f is R.
Thus, as f is bijective, we can prove that the cardinality of L is equal to the cardinality of R.
We can give the concrete form of L and R
We cases with x.1 and x.2 one by one to prove that the two sets are equal.
The same way, we can get the form of R.
Lastly, we get the cardinality of L and R using the forms of L and R.
In lean4, we need to check the elements of the set one by one to get the cardinality of the set, and then we get the conclusion.
-/
