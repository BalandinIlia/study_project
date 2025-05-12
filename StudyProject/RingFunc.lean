import Mathlib.Data.Int.Basic
import Mathlib.Data.Set.Basic
import StudyProject.Ring
import StudyProject.RingTheorems

-- This field provides an example of ring consisting of:
-- 1) Set of linear functions
-- 2) Summation of the functions
-- 3) Composition of the functions
namespace MY

def Func := ℤ → ℤ

def linFunc:Set Func := {f:Func | ∀x y:ℤ, f (x+y) = f x + f y}

def sum: Func → Func → Func
| f1, f2 => (fun x:ℤ => (f1 x) + (f2 x))

def compos: Func → Func → Func
| f1, f2 => (fun x:ℤ => (f1 (f2 x)))

instance RingFunc: Ring Func linFunc sum compos :=
  {
    zero := (fun x:ℤ => 0)
    sumDef := by
      intro a b
      intro aC bC
      rw [sum]
      rw [linFunc]
      simp
      intro x y
      have eqa: a (x+y) = a x + a y := by
        aesop
      rw [eqa]
      have eqb: b (x+y) = b x + b y := by
        aesop
      rw [eqb]
      omega
    mulDef := by
      intro a b
      intro aC bC
      rw [compos]
      rw [linFunc]
      intro x y
      simp
      have eq: b (x+y) = b x + b y := by
        aesop
      rw [eq]
      aesop
    sumComm := by
      intro a b
      intro aC bC
      simp [sum, Func]
      funext x
      apply Int.add_comm
    sumAssoc := by
      intro a b c
      intro aC bC cC
      simp [sum, Func]
      funext x
      apply Int.add_assoc
    zeroEx := by
      simp [linFunc]
    zeroProp := by
      intro a
      intro aC
      clear aC
      simp [sum]
    sumRev := by
      intro a
      intro aIn
      exists (fun x:ℤ => -(a x))
      simp [linFunc, sum]
      apply And.intro
      {
        intro x y
        have eq: a (x+y) = a x + a y := by
          aesop
        rw [eq]
        generalize hX: a x = X
        generalize hY: a y = Y
        clear hX hY a aIn x y eq
        omega
      }
      {
        funext x
        omega
      }
    multAssoc := by
      intro a b c
      intro aIn bIn cIn
      simp [compos]
    multDistrLeft := by
      intro a b c
      intro aIn bIn cIn
      simp [sum, compos]
      funext x
      aesop
    multDistrRight := by
      intro a b c
      intro aIn bIn cIn
      simp [sum, compos]
  }

theorem examp:
  ∀a b c d: Func, a∈linFunc →
                  b∈linFunc →
                  c∈linFunc →
                  d∈linFunc →
                  compos (sum a b) (sum c d) = sum (sum (compos a c) (compos b c)) (sum (compos a d) (compos b d)) := by
  apply ringTheorem2 Func allFunc sum compos
