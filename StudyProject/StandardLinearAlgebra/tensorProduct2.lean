import Mathlib.Data.Int.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Algebra.Module.Defs
import Mathlib.Data.Fin.Basic
import Mathlib.LinearAlgebra.TensorPower.Basic
import StudyProject.StandardLinearAlgebra.definitions
import StudyProject.StandardLinearAlgebra.moduleFinite

open scoped TensorProduct

inductive nm where
| a: nm
| b: nm
| c: nm

-- sequence of three integers
@[reducible]
def triple := SeqFin 3

-- sum of sequence
def sum(t: triple):ℤ := (t 0) + (t 1) + (t 2)

def idd:triple := fun i:Fin 3 => i
#eval sum idd

-- tensor product of three triple spaces, - the space we will working with
@[reducible]
def sp:Type := ⨂[ℤ] _ : nm, triple

lemma sep(i: nm)(A: Prop):
(i=nm.a → A) →
(i=nm.b → A) →
(i=nm.c → A) →
A := by
  intro l1 l2 l3
  have v:(i=nm.a)∨(i=nm.b)∨(i=nm.c) := by
    clear A l1 l2 l3
    sorry
  aesop

def map:(MultilinearMap ℤ (fun _:nm => triple) ℤ) :=
{
  toFun(f: nm → triple) := (sum (f nm.a))*(sum (f nm.b))*(sum (f nm.c))
  map_update_add':= by
    intro inst m i x y
    simp [Function.update, sum]
    simp [HAdd.hAdd]
    simp [Add.add]
    apply sep i
    all_goals intro eq
    all_goals rw [eq]
    all_goals clear eq
    all_goals simp
    all_goals ring
  map_update_smul':= by
    intro inst m i c x
    simp [Function.update, sum]
    simp [HSMul.hSMul]
    simp [SMul.smul]
    apply sep i
    all_goals intro eq
    all_goals rw [eq]
    all_goals clear eq
    all_goals simp
    all_goals ring
}

noncomputable
def m:= PiTensorProduct.lift map

noncomputable
def ten := PiTensorProduct.tprodCoeff ℤ 1 (fun _:nm => idd)

theorem th: m ten = 27 := by
  simp [m]
  simp [map]
  simp [sum]
  simp [ten]
  simp [idd]
