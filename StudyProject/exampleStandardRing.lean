import Mathlib.Data.Int.Basic
import Mathlib.Algebra.Ring.Basic

structure MT where
f:ℤ
s:ℤ

def summ(s1 s2: MT):MT := MT.mk (s1.f+s2.f) (s1.s+s2.s)

def mult(s1 s2: MT):MT := MT.mk (s1.f*s2.f) (s1.s*s2.s)

instance ins:Ring MT :=
{
  add := summ
  zero := MT.mk 0 0
  zero_add := by
    simp [HAdd.hAdd]
    simp [summ]
    intro a
    sorry
  add_comm := by
    simp [HAdd.hAdd]
    sorry
  add_assoc := by
    simp [HAdd.hAdd]
    sorry
  add_zero := by
    simp [HAdd.hAdd]
    sorry
  nsmul := (fun n:ℕ => fun m:MT => MT.mk (m.f*n) (m.s*n))
  mul := mult
  left_distrib := by
    simp [HAdd.hAdd]
    simp [HMul.hMul]
    sorry
  right_distrib := by
    simp [HAdd.hAdd]
    simp [HMul.hMul]
    sorry
  zero_mul := by
    simp [HMul.hMul]
    sorry
  mul_zero := by
    simp [HMul.hMul]
    sorry
  mul_assoc := by
    simp [HMul.hMul]
    sorry
  one := MT.mk 1 1
  one_mul := by
    simp [HMul.hMul]
    sorry
  mul_one := by
    simp [HMul.hMul]
    sorry
  neg := (fun n:MT => MT.mk (-n.f) (-n.s))
  zsmul := (fun z:ℤ => fun n:MT => MT.mk (n.f*z) (n.s*z))
  neg_add_cancel := by
    sorry
  nsmul_zero := by
    intro x
    simp
    sorry
  nsmul_succ := by
    sorry
  zsmul_zero' := by
    sorry
  zsmul_succ' := by
    sorry
  zsmul_neg' := by
    sorry
}
