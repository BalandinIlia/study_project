import Mathlib.Data.Int.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Algebra.Ring.Basic

-- Increase computational limit to enable all macros run to the end.
set_option maxHeartbeats 10000000

namespace MacroTraining

-- From Lean point of view:
--     This is a "syntactic" program. In other words, it is a
--     program which works at syntax level: it modifies Lean
--     file looking on it as at abstract syntax tree.
--
--     The program takes two arguments: na and start.
--     na has type ident, - name of something (proposition/
--     term). ident is a type of abstract syntax tree element.
--     It makes sense since the entire program works at
--     abstract syntax tree.
--     The second argument: start is just literally a number
--
-- From conceptual point of view:
--     This is a set of ten consequetive numbers starting
--     from given number start and having name na.
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
-- Here we run set_ten program. It works at abstract syntax
-- tree level and generates term with name test_ten and
-- specified content
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

-- This is another type of macro. When applied it
-- generates term. term is a type of abstract syntax tree
-- node.
macro "fol" a:ident n:num A:ident: term =>
`(term| ($a=$n → $A))

-- This helper lemma works with a property dependent on
-- a universe element a. It enables us to replace reasoning
-- for the entire universe by reasoning for each universe
-- element separately.
lemma sep(a:ℤ)(belong:a∈universRaw)(A:Prop):
-- (fol a 0 A) is a program ran at compile time
-- It replaces itself with a term (a=0 → A).
-- The macro program does not "know" anything about logic or
-- reasoning. It only knows about abstract syntax tree
-- structure
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

macro "InUniv" z:ident : term =>
`(term|(
  ($z=0)∨
  ($z=1)∨
  ($z=2)∨
  ($z=3)∨
  ($z=4)∨
  ($z=5)∨
  ($z=6)∨
  ($z=7)∨
  ($z=8)∨
  ($z=9)∨
  ($z=10)∨
  ($z=11)∨
  ($z=12)∨
  ($z=13)∨
  ($z=14)∨
  ($z=15)∨
  ($z=16)∨
  ($z=17)∨
  ($z=18)
))

-- Helper lemma: helps to prove that given number belongs to
-- the universe
lemma bel(z:ℤ):
(InUniv z) → (z∈universRaw) := by
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
      -- Here the "magic" happens:
      -- 1) First prove sees x znd eq1 as some identifiers and
      --    second prove as tactic
      -- 2) The first prove is automatically transformed into
      --    sep application and 19 applications of second prove.
      -- 3) Each second prove is also transformed into 19
      --    applications of the given tactic.
      -- So here we have written only 7 lines, these are lines
      -- of "syntactic programs". They are automatically
      -- transformed into other lines of code. These
      -- autogenerated lines prove 361 (19^2) cases separately.
      -- So here we have examined 361 cases in only 7 lines.
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
                                          -- So in some cases aesop is necessary to finish the proof, while in others there is no proof goal already.
                                          -- Try is neccessary not to ruin second cases.
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

-- This macro is intended to prove goals like
-- ∃n:ℤ, ...
-- by taking particular number and applying it to the goal
macro "use_value" n:num : tactic =>
`(tactic|(
  exists (Elem.mk $n (by apply bel; aesop));
  try simp [HAdd.hAdd];
  try simp [Add.add];
  try ext;
  try simp;
  try aesop
))

-- This macro is intended to prove goals like
-- ∃n:ℤ, ...
-- by checking all possible n
macro "check_all_values" : tactic =>
`(tactic|(
  solve
  | use_value 0
  | use_value 1
  | use_value 2
  | use_value 3
  | use_value 4
  | use_value 5
  | use_value 6
  | use_value 7
  | use_value 8
  | use_value 9
  | use_value 10
  | use_value 11
  | use_value 12
  | use_value 13
  | use_value 14
  | use_value 15
  | use_value 16
  | use_value 17
  | use_value 18
))

-- Existence of inverse by summation
theorem th:∀a:Elem, ∃b:Elem, a+b=0 := by
  intro a
  -- Here we prove existence of inverse by summation.
  -- For this we examine each possible value of a separately.
  -- For each value of a we examine all possible values and
  -- for each value try to prove that this is inverse by
  -- summation.
  prove a.val a.prop (intro eq; check_all_values)
