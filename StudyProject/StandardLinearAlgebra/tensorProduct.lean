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

open TensorProduct

def pair:Type:=(SeqFin 2) ⊗[ℤ] (SeqFin 2)
#synth Module ℤ ((SeqFin 2) ⊗[ℤ] (SeqFin 2))
#synth CommSemiring ℤ
#check instModule
#check @instModule
#check @instModule ℤ Int.instCommSemiring (SeqFin 2) (SeqFin 2)
#synth AddCommMonoid (SeqFin 2)
#synth Module ℤ (SeqFin 2)
#check @instModule ℤ Int.instCommSemiring (SeqFin 2) (SeqFin 2) (GroupFinite 2) (GroupFinite 2) (ModuleFinite 2) (ModuleFinite 2)

noncomputable
def resT:=@instModule ℤ Int.instCommSemiring (SeqFin 2) (SeqFin 2) (GroupFinite 2) (GroupFinite 2) (ModuleFinite 2) (ModuleFinite 2)
#check resT
#check resT.smul

def simp:Type:=ℤ ⊗[ℤ] ℤ
