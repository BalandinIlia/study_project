import Mathlib.Data.Int.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Algebra.Module.Defs
import StudyProject.StandardLinearAlgebra.definitions

instance GroupInfinite:AddCommMonoid SeqInf :=
{
  add: SeqInf → SeqInf → SeqInf
  | f1, f2 => fun n:ℕ => (f1 n) + (f2 n)
  add_comm := by
    prove_by_integer_prop Int.add_comm
  add_assoc := by
    prove_by_integer_prop Int.add_assoc
  zero := fun n:ℕ => 0
  zero_add := by
    prove_by_integer_prop Int.zero_add
  add_zero := by
    prove_by_integer_prop Int.add_zero

  nsmul: ℕ → SeqInf → SeqInf
  | m, f => fun n:ℕ => (f n) * m
  nsmul_zero := by
    simp
    intro x
    clear x
    funext n
    simp [OfNat.ofNat]
  nsmul_succ := by
    simp
    intro n x
    funext m
    simp [HAdd.hAdd]
    generalize rxm:x m = XM
    generalize rn:(↑n:ℤ) = N
    simp [Add.add]
    clear n x m rxm rn
    simp [Int.mul_add
}

instance ModuleInfinite: Module ℤ SeqInf :=
{
  smul(z: ℤ)(f: SeqInf) := fun n:ℕ => (f n) * z
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
    simp [HSMul.hSMul, HAdd.hAdd]
    simp [Add.add]
    intro a x y
    funext n
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
