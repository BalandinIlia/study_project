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

#check Basis
#check @Basis.mk
#synth Semiring ℤ
noncomputable
def rl(N: ℕ):Basis (Fin N) ℤ (SeqFin N) :=
@Basis.mk (Fin N)
          ℤ
          (SeqFin N)
          Int.instSemiring
          (GroupFinite N)
          (ModuleFinite N)
          (fun i:Fin N => (fun x: Fin N => if(x==i) then 1 else 0))
          (by
            simp [LinearIndependent]
            simp [Finsupp.linearCombination]
            simp [Function.Injective]
            intro a₁ a₂
            simp [HSMul.hSMul]
            simp [SMul.smul]
            simp [Finsupp.sum]
            intro A
            rw [Finset.sum] at A
            rw [Finset.sum] at A
            generalize s1:(∑ x ∈ a₁.support, fun n => if n = x then a₁ x else 0) = Seq1
            simp [SeqFin] at A
            #check congr_fun
            #check congr_fun A
            let AA := congr_fun A
            #check congr_arg
            simp at AA
            have eq: ∀a:Fin N →₀ ℤ,
                     ∀k:Fin N,
                     a k = (∑ x ∈ a.support, fun n => if n = x then a x else 0) k := by
                     simp
                     aesop
            apply Finsupp.ext
            intro aaa
            rw [eq a₁]
            rw [eq a₂]
            apply AA aaa
          )
          (by
            simp [LE.le]
            intro x
            simp [Submodule.span]
            intro p
            simp [Set.range]
            sorry
          )
