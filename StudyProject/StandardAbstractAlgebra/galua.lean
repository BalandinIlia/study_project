import Mathlib.Data.Int.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Algebra.Ring.Basic

-- Increase computational limit to enable all macros run to the end.
set_option maxHeartbeats 10000000

namespace MacroTraining

-- Set of ten consequetive numbers starting from given number
macro "set_ten" na:ident start:num : command =>
`(command|
def $na:ident :Set ℤ :=  {$start:num,
                          $start:num+1,
                          $start:num+2,
                          $start:num+3,
                          $start:num+4,
                          $start:num+5,
                          $start:num+6,
                          $start:num+7,
                          $start:num+8,
                          $start:num+9}
)
set_ten test_ten 8
#check test_ten (7:ℤ)
theorem test_ten_th: test_ten = {8,9,10,11,12,13,14,15,16,17} := by
  rw [test_ten]
  simp

-- Set of integers we will be operating at
def universRaw: Set ℤ :=
{
0,1,2,3,4,5,6,7,8,9,
10,11,12,13,14,15,16,17,18
}
#check universRaw
#print universRaw

macro "fol" a:ident n:num A:ident: term =>
`(term| ($a=$n → $A))

-- This helper lemma works with a property dependent on
-- a universe element a. It enables us to replace reasoning
-- for the entire universe by reasoning for each universe
-- element separately.
lemma sep(a:ℤ)(belong:a∈universRaw)(A:Prop):
(fol a 0 A) →
(fol a 1 A) →
(fol a 2 A) →
(fol a 3 A) →
(fol a 4 A) →
(fol a 5 A) →
(fol a 6 A) →
(fol a 7 A) →
(fol a 8 A) →
(fol a 9 A) →
(fol a 10 A) →
(fol a 11 A) →
(fol a 12 A) →
(fol a 13 A) →
(fol a 14 A) →
(fol a 15 A) →
(fol a 16 A) →
(fol a 17 A) →
(fol a 18 A) →
A := by
  rw [universRaw] at belong
  cases belong
  case inl => aesop
  case inr belong =>
  cases belong
  case inl => aesop
  case inr belong =>
  cases belong
  case inl => aesop
  case inr belong =>
  cases belong
  case inl => aesop
  case inr belong =>
  cases belong
  case inl => aesop
  case inr belong =>
  cases belong
  case inl => aesop
  case inr belong =>
  cases belong
  case inl => aesop
  case inr belong =>
  cases belong
  case inl => aesop
  case inr belong =>
  cases belong
  case inl => aesop
  case inr belong =>
  cases belong
  case inl => aesop
  case inr belong =>
  cases belong
  case inl => aesop
  case inr belong =>
  cases belong
  case inl => aesop
  case inr belong =>
  cases belong
  case inl => aesop
  case inr belong =>
  cases belong
  case inl => aesop
  case inr belong =>
  cases belong
  case inl => aesop
  case inr belong =>
  cases belong
  case inl => aesop
  case inr belong =>
  cases belong
  case inl => aesop
  case inr belong =>
  cases belong
  case inl => aesop
  case inr belong =>
    simp at belong
    aesop

-- formal universe element structure
@[ext]
structure Elem where
val: ℤ
prop: val∈universRaw

-- This macro solves a goal which have form x∈inversRaw → X:Prop.
-- For this the macro divides the goal into subgoals:
--         x=particular_value -> X
-- solCase solves the subgoal (x=particular_value -> X)
-- for each particular x value
macro "prove" x:ident X:ident solCase:tactic : tactic =>
`(tactic|
(
  apply sep $x $X;
  all_goals ($solCase;)
)
)

-- Helper lemma: helps to prove that given number belongs to
-- the universe
lemma bel(z:ℤ):
(
  (z=0)∨
  (z=1)∨
  (z=2)∨
  (z=3)∨
  (z=4)∨
  (z=5)∨
  (z=6)∨
  (z=7)∨
  (z=8)∨
  (z=9)∨
  (z=10)∨
  (z=11)∨
  (z=12)∨
  (z=13)∨
  (z=14)∨
  (z=15)∨
  (z=16)∨
  (z=17)∨
  (z=18)
) → (z∈universRaw) := by
  aesop

instance ins: AddCommMonoid Elem :=
{
  add(e1 e2: Elem) :=
  {
    val := (e1.val + e2.val)%19
    prop := by
      generalize r1:e1.val = x
      rw [Eq.comm] at r1
      generalize r2:e2.val = y
      rw [Eq.comm] at r2
      have eq1:x∈universRaw:=by
        simp [r1]
        apply e1.prop
      have eq2:y∈universRaw:=by
        simp [r2]
        apply e2.prop
      clear r1 r2 e1 e2
      prove x eq1 (prove y eq2 (
                               intro e1 e2
                               simp [e1, e2]
                               clear e1 e2
                               apply bel
                               simp
                               )
                  )
  }
  add_assoc := by
    intro a b c
    generalize ra:a.val = x
    generalize rb:b.val = y
    generalize rc:c.val = z
    have eqx:x∈universRaw:=by
        rw [Eq.comm] at ra
        simp [ra]
        apply a.prop
    have eqy:y∈universRaw:=by
        rw [Eq.comm] at rb
        simp [rb]
        apply b.prop
    have eqz:z∈universRaw:=by
        rw [Eq.comm] at rc
        simp [rc]
        apply c.prop
    simp [HAdd.hAdd]
    rw [ra, rb, rc]
    prove x eqx (prove y eqy (prove z eqz (
                                          intro c1 c2 c3;
                                          simp [c1, c2, c3];
                                          -- We do "try aesop", because aesop is necessary for some subgoals and not necessary for others.
                                          try aesop
                                          )
                             )
                )
  zero :=
  {
    val := 0
    prop := by
      apply bel
      simp
  }
  zero_add := by
    intro a
    apply Elem.ext
    simp [HAdd.hAdd]
    prove a.val a.prop (
                       aesop
                       )
  add_zero := by
    intro a
    apply Elem.ext
    simp [HAdd.hAdd]
    prove a.val a.prop (
                       aesop
                       )
  add_comm := by
    intro a b
    apply Elem.ext
    simp [HAdd.hAdd]
    prove a.val a.prop (prove b.val b.prop (
                                           intro c1 c2;
                                           simp [c1, c2];
                                           try aesop
                                           )
                       )

  nsmul(n: ℕ)(e: Elem):Elem:=
  {
    val := (n:ℤ)*e.val % 19
    prop := by
      sorry
  }
  nsmul_zero := by
    sorry
  nsmul_succ := by
    sorry
}
