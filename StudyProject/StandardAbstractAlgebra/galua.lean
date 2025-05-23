import Mathlib.Data.Int.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Algebra.Ring.Basic

set_option maxHeartbeats 10000000

namespace MacroTraining

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

def universRaw: Set ℤ :=
{
0,1,2,3,4,5,6,7,8,9,
10,11,12,13,14,15,16,17,18
}
#check universRaw
#print universRaw

lemma sep(a:ℤ)(belong:a∈universRaw)(A:Prop):
(a=0 → A) →
(a=1 → A) →
(a=2 → A) →
(a=3 → A) →
(a=4 → A) →
(a=5 → A) →
(a=6 → A) →
(a=7 → A) →
(a=8 → A) →
(a=9 → A) →
(a=10 → A) →
(a=11 → A) →
(a=12 → A) →
(a=13 → A) →
(a=14 → A) →
(a=15 → A) →
(a=16 → A) →
(a=17 → A) →
(a=18 → A) →
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

@[ext]
structure Elem where
val: ℤ
prop: val∈universRaw

-- Solces goal like x∈inversRaw → Prop
-- solCase solces the goal for each particular x value
macro "prove" x:ident X:ident solCase:tactic : tactic =>
`(tactic|
(
  apply sep $x $X;
  $solCase;
  $solCase;
  $solCase;
  $solCase;
  $solCase;
  $solCase;
  $solCase;
  $solCase;
  $solCase;
  $solCase;
  $solCase;
  $solCase;
  $solCase;
  $solCase;
  $solCase;
  $solCase;
  $solCase;
  $solCase;
  $solCase
)
)

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
                                          intro e1 e2 e3;
                                          rw [e1, e2, e3]
                                          try omega
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
                                           intro e1 e2;
                                           rw [e1, e2];
                                           try omega
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
