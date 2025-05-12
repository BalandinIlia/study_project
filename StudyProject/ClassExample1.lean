import Mathlib.Data.Int.Basic

-- This file is the first, trivial example of class
namespace MY

-- instance of this class is a function which takes given value
class ex1Rev(func: ℤ → ℤ)(val: ℤ) where
  arg: ℤ
  prop: func arg = val

theorem ex1Th1{v: ℤ}{f: ℤ→ℤ}(df: ex1Rev f v):
  ∃g:ℤ, f g = v := by
  exists df.arg
  simp [df.prop]

instance ex1Inst1: ex1Rev (fun x:ℤ => x*x) 4 :=
{
  arg := 2
  prop := by
    simp
}

instance ex1Inst2: ex1Rev (fun x:ℤ => x*x) 4 :=
{
  arg := -2
  prop := by
    simp
}

theorem ex1Th2: ∃g:ℤ, g*g=4 := by
  apply ex1Th1 ex1Inst1
