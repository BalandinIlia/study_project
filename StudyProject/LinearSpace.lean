import Mathlib.Data.Int.Basic
import Mathlib.Data.Set.Basic
import StudyProject.RingComOne
import StudyProject.Gal
import StudyProject.RingComOne_X_RingComOne

namespace MY

class Field(elemType: Type)
           (set: Set elemType)
           (sum: elemType → elemType → elemType)
           (mul: elemType → elemType → elemType)
  extends RingComOne elemType set sum mul where
MultInv: ∀a:elemType, a∈set → ¬(a = zero) → (∃b:elemType, b∈set ∧ mul a b = one)

-- linear space
class LinSp(TCoef TVec: Type)
           (fi: Set TCoef)
           (sumC: TCoef → TCoef → TCoef)
           (mulC: TCoef → TCoef → TCoef)
           (mulV: TCoef → TVec → TVec)
           (sumV: TVec → TVec → TVec)
           extends Field TCoef fi sumC mulC
           where
  VZero: TVec
  VsumComm: ∀v1 v2: TVec, sumV v1 v2 = sumV v2 v1
  VsumAssoc: ∀v1 v2 v3: TVec, sumV (sumV v1 v2) v3 = sumV v1 (sumV v2 v3)
  VMulLin: ∀v1 v2: TVec, ∀c: TCoef, c∈fi → mulV c (sumV v1 v2) = sumV (mulV c v1) (mulV c v2)
  VMulZero: ∀v: TVec, mulV zero v = VZero
  VMulOne: ∀v: TVec, mulV one v = v

-- element of tensor product of spaces
-- sum of pairs from A and fom B
def VecTen(TVA: Type)(TVB:Type) := TVA → TVB

-- multiply element of tensor product by scalar
def VecTenMul {TCoef TVA TVB: Type}
                   (_: TCoef → TVA → TVA)
                   (mulVB: TCoef → TVB → TVB)
                   (coef: TCoef)
                   (input: VecTen TVA TVB):
                   VecTen TVA TVB :=
  fun va:TVA => mulVB coef (input va)

-- sum elements of tensor product
def VecTenSum {TVA TVB: Type}
            (_: TVA → TVA → TVA)
            (sumVB: TVB → TVB → TVB)
            (input1: VecTen TVA TVB)
            (input2: VecTen TVA TVB):
            VecTen TVA TVB :=
  fun va:TVA => sumVB (input1 va) (input2 va)

-- tensor product of two linear spaces
def TensorProduct{TCoef TVA TVB: Type}
                 {fi: Set TCoef}
                 {sumC: TCoef → TCoef → TCoef}
                 {mulC: TCoef → TCoef → TCoef}
                 {mulVA: TCoef → TVA → TVA}
                 {sumVA: TVA → TVA → TVA}
                 {mulVB: TCoef → TVB → TVB}
                 {sumVB: TVB → TVB → TVB}
                 (_: LinSp TCoef TVA fi sumC mulC mulVA sumVA)
                 (linSpB: LinSp TCoef TVB fi sumC mulC mulVB sumVB):
                 (LinSp TCoef
                        (VecTen TVA TVB)
                        fi
                        sumC
                        mulC
                        (VecTenMul mulVA mulVB)
                        (VecTenSum sumVA sumVB)) :=
  {
    VZero := fun va:TVA => linSpB.VZero
    VsumComm := by
      simp [VecTen]
      intro v1 v2
      funext va
      simp [VecTenSum]
      apply linSpB.VsumComm
    VsumAssoc := by
      simp [VecTen]
      intro v1 v2 v3
      funext va
      simp [VecTenSum]
      apply linSpB.VsumAssoc
    VMulLin := by
      simp [VecTen]
      intro v1 v2
      intro c cIn
      funext va
      simp [VecTenSum, VecTenMul]
      apply linSpB.VMulLin
      apply cIn
    VMulZero := by
      simp [VecTen]
      intro v1
      funext va
      simp [VecTenSum, VecTenMul]
      apply linSpB.VMulZero
    VMulOne := by
      simp [VecTen]
      intro v1
      funext va
      simp [VecTenSum, VecTenMul]
      apply linSpB.VMulOne
  }
--def Seqq:= ℕ → ℤ

--def mulV: ℤ → Seqq → Seqq
--| z, f => (fun n:ℕ => z*(f n))

--def sumV: Seqq → Seqq → Seqq
--| f1, f2 => (fun n:ℕ => (f1 n) + (f2 n))

--instance ls: LinSp ℤ Seqq set5 sum5 mul5 mulV sumV :=
--  {
--    VZero := (fun n:ℕ => 0)
--    VsumComm := by
--      intro v1 v2
--      simp [sumV]
--     funext n
--      omega
--    VsumAssoc := by
--      intro v1 v2 v3
--      simp [sumV]
--      funext n
--      omega
--    VMulLin := by
--      intro v1 v2
--      intro c cIn
--      simp [mulV, sumV]
--      funext n
--      generalize f: v1 n = A
--      generalize g: v2 n = B
 --     clear cIn n f g v1 v2
  --    rw [Int.mul_comm]
   --   rw [Int.mul_comm c A]
    --  rw [Int.mul_comm c B]
--      apply Int.add_mul A B c
  --  VMulZero := by
    --  intro v
      --funext n
--      simp [mulV]
  --    rw [RingComOne.zero]
    --  rw [Gal]
      --simp
--    VMulOne := by
  --    intro v
    --  simp [mulV]
      --funext n
--      rw [RingComOne.one]
  --    rw [Gal]
    --  simp
 -- }
