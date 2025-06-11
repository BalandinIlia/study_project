import Mathlib.Data.Int.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Algebra.Module.Defs
import Mathlib.Data.Fin.Basic
import Mathlib.LinearAlgebra.TensorPower.Basic
import StudyProject.StandardLinearAlgebra.definitions

-- Here we do "mass definition" of instances.
-- There is a countable set of types SeqFin, and we define
-- AddCommMonoid instance for each type.
instance GroupFinite(N: ℕ):AddCommMonoid (SeqFin N) :=
{
  add: (SeqFin N) → (SeqFin N) → (SeqFin N)
  | f1, f2 => fun n:(Fin N) => (f1 n) + (f2 n)
  add_comm := by
    prove_by_integer_prop Int.add_comm
  add_assoc := by
    prove_by_integer_prop Int.add_assoc
  zero := fun n:Fin N => 0
  zero_add := by
    prove_by_integer_prop Int.zero_add
  add_zero := by
    prove_by_integer_prop Int.add_zero

  nsmul: ℕ → (SeqFin N) → (SeqFin N)
  | m, f => fun n:Fin N => (f n) * m
  nsmul_zero := by
    simp
    rw [OfNat.ofNat]
    rw [OfNat.ofNat]
    simp [Zero.toOfNat0]
  nsmul_succ := by
    simp
    simp [HAdd.hAdd]
    intro n x
    funext m
    generalize repl1:((↑n):ℤ)=M
    generalize repl2:(x m)=G
    simp [Add.add]
    simp [Int.mul_add G M 1]
}

-- The same "mass definition" of instances.
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
