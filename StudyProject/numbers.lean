import Mathlib.Data.Int.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Algebra.Module.Defs
import Mathlib.Data.Fin.Basic
import Mathlib.LinearAlgebra.TensorPower.Basic
import StudyProject.StandardLinearAlgebra.definitions
import StudyProject.StandardLinearAlgebra.moduleInfinite
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt

namespace numbers

def r1:ℚ := 1
def r2:ℚ := 2
def r3:ℚ := 3
def r4:ℚ := 5/6

theorem thr: r1/r2 + r1/r3 = r4 := by
  rw [r1, r2, r3, r4]
  ring

def rm:ℚ := 1/(10^50)
theorem thr2: r1 < r1 + rm := by
  rw [r1, rm]
  simp

#eval (r1+r2+r3+r4)

noncomputable
def v2:ℝ := Real.sqrt 2
noncomputable
def v3:ℝ := Real.sqrt 3
noncomputable
def v6:ℝ := Real.sqrt 6

theorem threal1:(v2+v3)*(v2+v3) = 5 + 2*v6 := by
  rw [v2, v3, v6]
  ring
  simp
  ring
  simp
  have tr: Real.sqrt 6 = Real.sqrt (2*3) := by
    ring
  rw [tr]
  clear tr
  rw [Real.sqrt_mul _ 3]
  linarith
