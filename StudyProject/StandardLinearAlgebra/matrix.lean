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

#check LinearMap.toMatrix
#check Matrix.toLin

#check LinearMap.toMatrix (rl 5) (rl 5) (multLin 5 (fun n:Fin 5 => n))
noncomputable
def mat:=LinearMap.toMatrix (rl 5) (rl 5) (multLin 5 (fun n:Fin 5 => n))
#check mat
#check mat 1 1

#check Matrix.toLin (rl 3) (rl 3)
noncomputable
def op := Matrix.toLin (rl 3) (rl 3) !![1, 2, 1; 1, 2, 1; 1, 2, 1]
