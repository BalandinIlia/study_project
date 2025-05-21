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
import StudyProject.StandardLinearAlgebra.moduleFinite
import StudyProject.StandardLinearAlgebra.moduleInfinite
import StudyProject.StandardLinearAlgebra.linearMaps

def sumZero(N: ℕ)(seq: SeqFin N) := (∑ i:Fin N, seq i) = 0

def f(N: ℕ): Submodule ℤ (SeqFin N) :=
{
  carrier := {seq: SeqFin N | sumZero N seq}
  add_mem' := by
    intro a b
    intro A B
    simp at A
    simp at B
    simp
    simp [sumZero] at A B
    simp [sumZero]
    simp [HAdd.hAdd]
    simp [Add.add]
    have eq: ∑ x, (a x + b x) = ∑ x, a x + ∑ x, b x := by
      clear A B
      simp [SeqFin] at a b
      apply Finset.sum_add_distrib
    rw [eq]
    rw [A, B]
    simp
  zero_mem' := by
    simp [sumZero]
    simp [OfNat.ofNat]
    simp [Zero.zero]
  smul_mem' := by
    intro c x
    simp
    intro CX
    simp [sumZero] at CX
    simp [sumZero]
    simp [HSMul.hSMul]
    simp [SMul.smul]
    have eq: ∑ i, x i * c = c * ∑ i, x i := by
      simp [Finset.mul_sum]
      apply Finset.sum_congr
      simp
      intro i
      intro I
      generalize repl:x i = XI
      simp [Int.mul_comm]
    rw [eq]
    rw [CX]
    simp
}
