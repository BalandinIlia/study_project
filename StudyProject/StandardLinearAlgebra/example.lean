import Mathlib.Data.Int.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Field.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Basis.Submodule
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Algebra.Module.Defs

def Func := ℕ → ℤ

instance gh:AddCommMonoid Func :=
{
  add: Func → Func → Func
  | f1, f2 => fun n:ℕ => (f1 n) + (f2 n)
  add_assoc := by
    simp [HAdd.hAdd]
    simp [Add.add]
    intro a b c
    funext n
    omega
  zero := fun n:ℕ => 0
  zero_add := by
    simp [HAdd.hAdd]
    simp [Add.add]
    intro a
    funext n
    simp [OfNat.ofNat]
  add_zero := by
    simp [HAdd.hAdd]
    simp [Add.add]
    intro a
    funext n
    simp [OfNat.ofNat]
  add_comm := by
    simp [HAdd.hAdd]
    simp [Add.add]
    intro a b
    funext n
    omega

  nsmul: ℕ → Func → Func
  | m, f => fun n:ℕ => (f n) * m
  nsmul_zero := by
    simp
    intro x
    funext n
    simp [OfNat.ofNat]
  nsmul_succ := by
    simp
    intro n x
    funext m
    simp [Nat.cast]
    simp [HAdd.hAdd]
    simp [Add.add]
    generalize repl: x m = A
    simp [OfNat.ofNat]
    simp [One.one]
    simp [NatCast.natCast]
    simp [Nat.cast]
    rw [Int.mul_add]
    omega
}

instance rx: Module ℤ Func :=
{
  smul(z: ℤ)(f: Func) := fun n:ℕ => (f n) * z
  one_smul := by
    simp [HSMul.hSMul]
  smul_zero := by
    simp [HSMul.hSMul]
    simp [OfNat.ofNat]
    simp [Zero.zero]
  smul_add := by
    simp [HSMul.hSMul]
    intro a x y
    funext n
    simp [HAdd.hAdd]
    simp [Add.add]
    generalize r1: x n = X
    generalize r2: y n = Y
    rw [Int.add_mul X Y a]
  add_smul := by
    simp [HSMul.hSMul]
    intro a x y
    funext n
    simp [HAdd.hAdd]
    simp [Add.add]
    generalize r2: y n = Y
    rw [Int.mul_add]
  zero_smul := by
    simp [HSMul.hSMul]
    simp [OfNat.ofNat]
    simp [Zero.zero]
  mul_smul := by
    simp [HSMul.hSMul]
    intro a x y
    funext n
    generalize r2: y n = Y
    rw [Int.mul_comm a x]
    rw [Int.mul_assoc]
}
