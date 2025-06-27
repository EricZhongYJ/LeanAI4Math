import Mathlib
/-! Question:
6. Greatest elements are sometimes inaccurately called unique maximal elements. Construct a partially ordered set $X$ with just one maximal element and no greatest element.
-/
CESS","data":{"total":1,"list":[{"created":"2024-11-10 17:40:17","updated":"2024-11-13 15:01:08","id":5469,"questionId":7065,"taskId":2436,"jobId":4348,"userId":231,"judgeUserId":255,"answer":{"informalProof":"X is a partially ordered set containing only one point union another partially ordered set which only contains an infinitely increasing chain.

","formalProof":"import Mathlib.Order.Bounds.Defs
import Mathlib.Order.Defs
import Mathlib.Data.Set.Defs
import Mathlib.Logic.IsEmpty
import Mathlib.Order.Max

variable {u}
inductive X where
  | leftX : X
  | rightX (n : Nat) : X

def X.le : (@& X) → (@& X) → Prop
    | X.leftX, X.leftX => True
    | X.rightX n, X.rightX m => Nat.le n m
    | _, _ => False

def X.lt : (@& X) → (@& X) → Prop
    | x, y => X.le x y ∧ (Not (X.le y x))

instance instLEX : LE X where
  le := X.le

instance instLTX : LT X where
  lt := X.lt

instance instPartialOrderX : PartialOrder X where
  le := X.le
  lt := X.lt
  le_refl a := match a with
    | X.leftX    => trivial
    | X.rightX n => (Nat.le_refl n)
  le_trans a b c hst htu := match a, b, c with
    | X.leftX,    X.leftX,    X.leftX    => trivial
    | X.rightX a, X.rightX b, X.rightX c => Nat.le_trans hst htu
  le_antisymm a b hst hts := match a, b with
    | X.leftX, X.leftX => by
      dsimp
    | X.rightX a, X.rightX b => by
      rewrite [Nat.le_antisymm hst hts]
      rfl

/- proof of no greatest element -/

lemma X.no_greatest (s : X) : (IsTop s) → False
  := match s with
  | X.leftX    => by
    intro h
    unfold IsTop at h
    apply h (X.rightX Nat.zero)
  | X.rightX n => by
    intro h
    unfold IsTop at h
    apply h X.leftX

/- proof of only one maximal element -/
lemma X.le_succ : (X.rightX n) ≤ (X.rightX n.succ)
  := by dsimp <;> apply Nat.le_succ

lemma X.not_succ_le_self : ¬(X.rightX n.succ) ≤ (X.rightX n)
  := by dsimp <;> apply Nat.not_succ_le_self

lemma X.exists_unique_maximal : ∃! s : X, (IsMax s)
  := by
    unfold ExistsUnique
    constructor
    case w => exact (X.leftX)
    case h =>
      constructor
      case left =>
        simp
        unfold IsMax
        intro x
        intro h
        match x with
          | X.leftX => trivial
      case right =>
        simp
        intro x
        intro h
        unfold IsMax at h
        match x with
          | X.leftX => trivial
          | X.rightX n =>
            specialize @h (X.rightX (Nat.succ n))
            have a := h (X.le_succ)
            have w := X.not_succ_le_self (a)
            apply False.elim w
","formalStatement":null,"suggestion":null,"comment":null},"judgement":{"result":"done","score":5,"suggestion":"<p>证明通顺，逻辑严密，完全正确，再接再厉！</p>","feedbackAction":"done","comment":null},"stepInfo":null,"userInfo":{"id":231,"username":"SyntheticDawn","nickname":"SyntheticDawn","avatar":"//p1-arco.byteimg.com/tos-cn-i-uwbnlip3yd/a8c8cdb109cb051163646151a4a5083b.png~tplv-uwbnlip3yd-webp.webp","email":"cloudifold.3125@gmail.com"},"judgeUserInfo":{"id":255,"username":"mbkybky","nickname":"mbkybky","avatar":"//p1-arco.byteimg.com/tos-cn-i-uwbnlip3yd/a8c8cdb109cb051163646151a4a5083b.png~tplv-uwbnlip3yd-webp.webp","email":"mbkybky@qq.com"}}]},"errorCode"

/-! Informal proof:
X is a partially ordered set containing only one point union another partially ordered set which only contains an infinitely increasing chain.

-/
