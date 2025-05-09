import Mathlib.Data.Int.Basic
import Mathlib.Data.Set.Basic

class Field(elemType: Type)(set: Set elemType)(sum: elemType → elemType → elemType)(mul: elemType → elemType → elemType) where
  zero: elemType
  one: elemType

  sumDef: ∀a b: elemType, a∈set → b∈set → (sum a b)∈set
  mulDef: ∀a b: elemType, a∈set → b∈set → (mul a b)∈set

  sumComm: ∀a b: elemType, a∈set → b∈set → (sum a b) = (sum b a)
  sumAssoc: ∀a b c: elemType, a∈set → b∈set → c∈set → (sum (sum a b) c) = (sum a (sum b c))
  zeroEx: zero∈set
  zeroProp: (∀a:elemType, a∈set → (sum a zero) = a)
  sumRev: ∀a:elemType, a∈set → (∃b:elemType, b∈set ∧ (sum a b) = zero)

  multComm: ∀a b: elemType, a∈set → b∈set → (mul a b) = (mul b a)
  multAssoc: ∀a b c: elemType, a∈set → b∈set → c∈set → (mul (mul a b) c) = (mul a (mul b c))
  oneEx: one∈set
  oneProp: (∀a:elemType, a∈set → (mul a one) = a)
  mulRev: ∀a:elemType, a∈set → ¬(a=zero) → (∃b:elemType, b∈set ∧ (mul a b) = one)

  multDistr: ∀a b c: elemType, a∈set → b∈set → c∈set → mul c (sum a b) = sum (mul c a) (mul c b)

def set5: Set ℤ := {0, 1, 2, 3, 4}

def sum5(s1: ℤ)(s2: ℤ) := (s1+s2)%5

def mul5(s1: ℤ)(s2: ℤ) := (s1*s2)%5

instance Gal: Field ℤ set5 sum5 mul5 :=
  {
    zero := 0
    one := 1
    sumDef := by
      intro a b
      intro aIn bIn
      simp [set5] at aIn bIn
      sorry
    mulDef := by
      intro a b
      intro aIn bIn
      simp [set5] at aIn bIn
      sorry
    sumComm := by
      intro a b
      intro aIn bIn
      simp [sum5]
      omega
    sumAssoc := by
      simp [sum5]
      omega
    zeroEx := by
      simp [set5]
      sorry
    zeroProp := by
      intro a
      simp [set5]
      simp [sum5]
      intro aIn
      sorry
    sumRev := by
      simp [set5, sum5]
      intro a aIn
      exists (5-a)%5
      apply And.intro
      simp
      sorry
      simp
      omega
    multComm := by
      simp [mul5]
      intro a b aIn bIn
      rw [Int.mul_comm]
    multAssoc := by
      intro a b c aIn bIn cIn
      simp [mul5]
      sorry
    oneEx := by
      simp [set5]
      sorry
    oneProp := by
      simp [mul5, set5]
      intro a aIn
      sorry
    mulRev := by
      simp [set5]
      intro a aIn
      intro nZ
      sorry
    multDistr := by
      intro a b c aIn bIn cIn
      simp [sum5, mul5]
      sorry
  }
