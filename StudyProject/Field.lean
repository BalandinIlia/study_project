import Mathlib.Data.Int.Basic
import Mathlib.Data.Set.Basic

namespace MY

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
