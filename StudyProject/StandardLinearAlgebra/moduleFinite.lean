import Mathlib.Data.Int.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Field.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Basis.Submodule
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Algebra.Module.Defs
import Mathlib.Data.Fin.Basic
import Mathlib.LinearAlgebra.DirectSum.Basis
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Algebra.Module.Submodule.Bilinear
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.Data.Matrix.Kronecker
import StudyProject.StandardLinearAlgebra.definitions

instance GroupFinite(N: ℕ):AddCommMonoid (SeqFin N) :=
{
  add: (SeqFin N) → (SeqFin N) → (SeqFin N)
  | f1, f2 => fun n:(Fin N) => (f1 n) + (f2 n)
  add_assoc := by
    simp [HAdd.hAdd]
    simp [Add.add]
    intro a b c
    funext n
    omega
  zero := fun n:Fin N => 0
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

  nsmul: ℕ → (SeqFin N) → (SeqFin N)
  | m, f => fun n:Fin N => (f n) * m
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

instance ModuleFinite(N: ℕ): Module ℤ (SeqFin N) :=
{
  smul(z: ℤ)(f: SeqFin N) := fun n:Fin N => (f n) * z
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
