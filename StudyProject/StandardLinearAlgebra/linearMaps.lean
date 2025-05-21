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

def cut(N: ℕ): SeqInf →ₗ[ℤ] SeqFin N :=
{
  toFun(s:SeqInf):SeqFin N := fun n:Fin N => s n
  map_add' := by
    intro x y
    funext n
    simp [HAdd.hAdd]
    simp [Add.add]
  map_smul' := by
    intro x y
    funext n
    simp [HAdd.hAdd, HSMul.hSMul, SMul.smul]
}

lemma Var(A B: Prop): (A→B) → ((¬A)→B) → B := by
  intro h1 h2
  have helper:(A∨(¬A))→B:= by
    aesop
  apply helper
  clear h1 h2 helper B
  by_contra
  aesop
#print axioms Var

def extend{N: ℕ}: SeqFin N →ₗ[ℤ] SeqInf :=
{
  toFun(s:SeqFin N):SeqInf :=
    fun n:ℕ => if eq:n<N then s (Fin.mk n eq)
                         else 0
  map_add' := by
    intro x y
    funext n
    apply Var (n<N)
    {
      intro neq
      simp [neq]
      simp [HAdd.hAdd, HSMul.hSMul, SMul.smul]
      simp [Add.add]
      have eq1:x ⟨n, neq⟩=(if eq : n < N then x ⟨n, eq⟩ else 0) := by
        aesop
      rw [eq1]
      aesop
    }
    {
      intro neq
      simp [neq]
      simp [HAdd.hAdd, HSMul.hSMul, SMul.smul]
      simp [Add.add]
      have eq1:0=(if eq : n < N then x ⟨n, eq⟩ else 0) := by
        simp [neq]
      have eq2:0=(if eq : n < N then y ⟨n, eq⟩ else 0) := by
        simp [neq]
      generalize repl1:(if eq : n < N then x ⟨n, eq⟩ else 0)=A
      generalize repl2:(if eq : n < N then y ⟨n, eq⟩ else 0)=B
      rw [repl1] at eq1
      rw [repl2] at eq2
      clear repl1 repl2 N x y neq n
      aesop
    }
  map_smul' := by
    intro x y
    funext n
    simp [HAdd.hAdd, HSMul.hSMul, SMul.smul]
}

def I:SeqInf := fun n:ℕ => n

def ICut:SeqInf := extend ((cut 5) I)

#eval I 2
#eval ICut 2
#eval I 20
#eval ICut 20

def multLin(N: ℕ)(m: SeqFin N): SeqFin N →ₗ[ℤ] SeqFin N :=
{
  toFun: SeqFin N → SeqFin N
  | s1 => (fun n:Fin N => (s1 n)*(m n))
  map_add' := by
    intro x y
    simp
    funext n
    simp [HAdd.hAdd]
    simp [Add.add]
    generalize repl1: x n = XN
    generalize repl2: y n = YN
    generalize repl3: m n = MN
    ring
  map_smul' := by
    intro x
    simp
    intro s
    funext n
    simp [HSMul.hSMul]
    simp [SMul.smul]
    generalize repl1: m n = MN
    generalize repl2: s n = SN
    ring
}
