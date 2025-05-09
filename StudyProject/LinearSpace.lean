import Mathlib.Data.Int.Basic
import Mathlib.Data.Set.Basic
import StudyProject.Field

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

def Func:= ℕ → ℤ

def mulV: ℤ → Func → Func
| z, f => (fun n:ℕ => z*(f n))

def sumV: Func → Func → Func
| f1, f2 => (fun n:ℕ => (f1 n) + (f2 n))

instance ls: LinSp ℤ Func set5 sum5 mul5 mulV sumV :=
  {
    VZero := (fun n:ℕ => 0)
    VsumComm := by
      intro v1 v2
      simp [sumV]
      funext n
      omega
    VsumAssoc := by
      intro v1 v2 v3
      simp [sumV]
      funext n
      omega
    VMulLin := by
      intro v1 v2
      intro c cIn
      simp [mulV, sumV]
      funext n
      generalize f: v1 n = A
      generalize g: v2 n = B
      clear cIn n f g v1 v2
      rw [Int.mul_comm]
      rw [Int.mul_comm c A]
      rw [Int.mul_comm c B]
      apply Int.add_mul A B c
    VMulZero := by
      intro v
      funext n
      simp [mulV]
      rw [Field.zero]
      rw [Gal]
      simp
    VMulOne := by
      intro v
      simp [mulV]
      funext n
      rw [Field.one]
      rw [Gal]
      simp
  }
