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
import StudyProject.StandardLinearAlgebra.basis

def Z(n:ℕ):ℤ:=n

instance jkl(N: ℕ): AddCommMonoid (SeqFin N →ₗ[ℤ] SeqFin N) :=
{
  add(l1 l2: (SeqFin N →ₗ[ℤ] SeqFin N)):(SeqFin N →ₗ[ℤ] SeqFin N):=
  {
    toFun(s: SeqFin N):SeqFin N := (l1 s) + (l2 s)
    map_add' := by
      intro x y
      have eq1: l1 (x+y)=l1 x + l1 y := by
        aesop
      have eq2: l2 (x+y)=l2 x + l2 y := by
        aesop
      rw [eq1, eq2]
      generalize replA: l1 x = A
      generalize replB: l1 y = B
      generalize replC: l2 x = C
      generalize replD: l2 y = D
      clear replA replB replC replD eq1 eq2 l1 l2
      module
    map_smul' := by
      intro m x
      have eq1:l1 (m • x) = m • (l1 x) := by
        aesop
      have eq2:l2 (m • x) = m • (l2 x) := by
        aesop
      have eq3:(RingHom.id ℤ) m • (l1 x + l2 x) = m • (l1 x) + m • (l2 x) := by
        aesop
      rw [eq1, eq2, eq3]
  }
  add_comm := by
    intro a b
    ext s
    simp [HAdd.hAdd]
    generalize replA:a s=A
    generalize replB:b s=B
    clear a b s replA replB
    simp [Add.add]
    funext n
    ring
  add_assoc := by
    intro a b c
    ext s
    simp [HAdd.hAdd]
    generalize replA:a s=A
    generalize replB:b s=B
    generalize replC:c s=C
    clear a b c s replA replB replC
    simp [Add.add]
    funext n
    ring
  zero :=
  {
    toFun(s: SeqFin N):SeqFin N := (fun n: Fin N => 0)
    map_add' := by
      intro x y
      aesop
    map_smul' := by
      intro m
      intro x
      funext n
      simp [HSMul.hSMul]
      simp [SMul.smul]
  }
  zero_add := by
    intro a
    ext s
    simp [HAdd.hAdd]
    simp [Add.add]
    funext n
    simp [Zero.zero]
    aesop
  add_zero := by
    intro a
    ext s
    simp [HAdd.hAdd]
    simp [Add.add]
    funext n
    simp [Zero.zero]
    aesop

  nsmul(n:ℕ)(lm: (SeqFin N →ₗ[ℤ] SeqFin N)):(SeqFin N →ₗ[ℤ] SeqFin N) :=
  {
    toFun(s: SeqFin N) := (Z n)•(lm s)
    map_add' := by
      aesop
    map_smul' := by
      intro m
      intro x
      have eq: lm (m • x) = m • (lm x) := by
        aesop
      rw [eq]
      module
  }
  nsmul_zero := by
    intro leftMul
    simp [HSMul.hSMul]
    simp [SMul.smul]
    ext argument
    simp
    funext n
    rw [Zero.toOfNat0]
    simp [Z]
    aesop
  nsmul_succ := by
    intro n
    intro leftMul
    simp [HSMul.hSMul]
    simp [SMul.smul]
    ext argument
    simp
    funext x
    simp [Z]
    simp [HAdd.hAdd]
    simp [Add.add]
    ring
}
