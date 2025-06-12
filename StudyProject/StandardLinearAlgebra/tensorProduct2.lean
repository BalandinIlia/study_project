import Mathlib.Data.Int.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Algebra.Module.Defs
import Mathlib.Data.Fin.Basic
import Mathlib.LinearAlgebra.TensorPower.Basic
import StudyProject.StandardLinearAlgebra.definitions
import StudyProject.StandardLinearAlgebra.moduleInfinite

namespace hi

open scoped TensorProduct

-- ind stays for "index"
inductive ind where
| a: ind
| b: ind
| c: ind
| d: ind

-- helper lemma prove propositions dependent on index
lemma sep(i: ind)(A: Prop):
(i=ind.a → A) →
(i=ind.b → A) →
(i=ind.c → A) →
(i=ind.d → A) →
A := by
  intro l1 l2 l3 l4
  cases i
  case a => aesop
  case b => aesop
  case c => aesop
  case d => aesop

-- sum of infinite sequence
def sum:SeqInf →ₗ[ℤ] ℤ :=
{
  toFun(s:SeqInf) := (s 0) + (s 5) + (s 9)
  map_add' := by
    intro x y
    simp [HAdd.hAdd]
    simp [Add.add]
    ring
  map_smul' := by
    intro m x
    simp [HSMul.hSMul]
    simp [SMul.smul]
    ring
}

-- main module we will be working in
@[reducible]
def univers:Type := ⨂[ℤ] _ : ind, SeqInf
#synth Module ℤ univers

-- multiplication of tensor product components
def multImp: MultilinearMap ℤ (fun _:ind => SeqInf) ℤ :=
{
  toFun(f: ind → SeqInf) := (sum (f ind.a))*
                            (sum (f ind.b))*
                            (sum (f ind.c))*
                            (sum (f ind.d))
  map_update_add':= by
    intro inst m i x y
    simp [Function.update]
    apply sep i
    all_goals intro eq
    all_goals simp [eq]
    all_goals ring
  map_update_smul':= by
    intro inst m i c x
    simp [Function.update]
    apply sep i
    all_goals intro eq
    all_goals simp [eq]
    all_goals ring
}

noncomputable
def mult:= PiTensorProduct.lift multImp

-- ex - example
def ex0:SeqInf := fun _:ℕ => 0
def exId:SeqInf := fun n:ℕ => n
def exSqr:SeqInf := fun n:ℕ => n*n

-- examples of tensors
noncomputable
def tensor1:univers := PiTensorProduct.tprodCoeff ℤ 1
  (
    fun i:ind => match i with
    | ind.a => ex0
    | ind.b => exSqr
    | ind.c => exSqr
    | ind.d => exSqr
  )

noncomputable
def tensor2:univers := PiTensorProduct.tprodCoeff ℤ 1
  (
    fun i:ind => match i with
    | ind.a => exId
    | ind.b => exSqr
    | ind.c => exSqr
    | ind.d => exSqr
  )

theorem th1: mult tensor1 = 0 := by
  simp [mult, multImp, tensor1, sum, ex0, exId, exSqr]

def val_th2:ℤ := (5+9)*(5*5+9*9)*(5*5+9*9)*(5*5+9*9)
#eval val_th2
theorem th2: mult tensor2 = val_th2 := by
  simp [mult, multImp, tensor1, tensor2, sum, ex0, exId, exSqr, val_th2]

theorem th3: mult (tensor1+tensor2) = val_th2 := by
  simp [mult, multImp, tensor1, tensor2, sum, ex0, exId, exSqr, val_th2]

theorem example_induction: ∀u:univers, (mult u) % 1 = 0 := by
  intro u
  apply PiTensorProduct.induction_on
    (motive := fun k:univers => (mult k) % 1 = 0)
  {
    clear u
    intro r f
    simp
  }
  {
    clear u
    intro x y
    intro X Y
    rw [mult.map_add]
    aesop
  }
