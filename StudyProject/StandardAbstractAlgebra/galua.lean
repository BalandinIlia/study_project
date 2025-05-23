import Mathlib.Data.Int.Basic
import Mathlib.Algebra.Ring.Basic

set_option maxHeartbeats 10000000

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

set_ten q 0
set_ten w 10
set_ten e 20
set_ten r 30
set_ten t 40
set_ten y 50
set_ten u 60
set_ten i 70
set_ten o 80
set_ten p 90

def universRaw: Set ℤ := q∪w∪e∪r∪t∪y∪u∪i∪o∪p
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
(a=19 → A) →
(a=20 → A) →
(a=21 → A) →
(a=22 → A) →
(a=23 → A) →
(a=24 → A) →
(a=25 → A) →
(a=26 → A) →
(a=27 → A) →
(a=28 → A) →
(a=29 → A) →
(a=30 → A) →
(a=31 → A) →
(a=32 → A) →
(a=33 → A) →
(a=34 → A) →
(a=35 → A) →
(a=36 → A) →
(a=37 → A) →
(a=38 → A) →
(a=39 → A) →
(a=40 → A) →
(a=41 → A) →
(a=42 → A) →
(a=43 → A) →
(a=44 → A) →
(a=45 → A) →
(a=46 → A) →
(a=47 → A) →
(a=48 → A) →
(a=49 → A) →
(a=50 → A) →
(a=51 → A) →
(a=52 → A) →
(a=53 → A) →
(a=54 → A) →
(a=55 → A) →
(a=56 → A) →
(a=57 → A) →
(a=58 → A) →
(a=59 → A) →
(a=60 → A) →
(a=61 → A) →
(a=62 → A) →
(a=63 → A) →
(a=64 → A) →
(a=65 → A) →
(a=66 → A) →
(a=67 → A) →
(a=68 → A) →
(a=69 → A) →
(a=70 → A) →
(a=71 → A) →
(a=72 → A) →
(a=73 → A) →
(a=74 → A) →
(a=75 → A) →
(a=76 → A) →
(a=77 → A) →
(a=78 → A) →
(a=79 → A) →
(a=80 → A) →
(a=81 → A) →
(a=82 → A) →
(a=83 → A) →
(a=84 → A) →
(a=85 → A) →
(a=86 → A) →
(a=87 → A) →
(a=88 → A) →
(a=89 → A) →
(a=90 → A) →
(a=91 → A) →
(a=92 → A) →
(a=93 → A) →
(a=94 → A) →
(a=95 → A) →
(a=96 → A) →
(a=97 → A) →
(a=98 → A) →
(a=99 → A) →
A := by
  rw [universRaw] at belong
  rw [q,w,e,r,t,y,u,i,o,p] at belong
  simp at belong
  sorry
  /-cases belong
  case inr belong => cases belong
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
                     case inr belong => aesop
  case inl belong =>
  cases belong
  case inr belong => cases belong
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
                     case inr belong => aesop
  case inl belong =>
  cases belong
  case inr belong => cases belong
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
                     case inr belong => aesop
  case inl belong =>
  cases belong
  case inr belong => cases belong
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
                     case inr belong => aesop
  case inl belong =>
  cases belong
  case inr belong => cases belong
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
                     case inr belong => aesop
  case inl belong =>
  cases belong
  case inr belong => cases belong
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
                     case inr belong => aesop
  case inl belong =>
  cases belong
  case inr belong => cases belong
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
                     case inr belong => aesop
  case inl belong =>
  cases belong
  case inr belong => cases belong
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
                     case inr belong => aesop
  case inl belong =>
  cases belong
  case inr belong => cases belong
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
                     case inr belong => aesop
  case inl belong =>
  cases belong
  case inr belong => cases belong
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
                     case inr belong => aesop-/

structure Elem where
val: ℤ
prop: val∈universRaw

instance ins: AddCommMonoid Elem :=
{
  add(e1 e2: Elem) :=
  {
    val := (e1.val + e2.val)%100
    prop := by
      sorry
  }
  add_assoc := by
    sorry
  zero :=
  {
    val := 0
    prop := by
      sorry
  }
  zero_add := by
    sorry
  add_zero := by
    sorry
  add_comm := by
    sorry

  nsmul(n: ℕ)(e: Elem):Elem:=
  {
    val := (n:ℤ)*e.val % 100
    prop := by
      sorry
  }
  nsmul_zero := by
    sorry
  nsmul_succ := by
    sorry
}
