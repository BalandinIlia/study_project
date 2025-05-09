import Mathlib.Data.Int.Basic
import Mathlib.Data.Set.Basic

namespace MY

-- This class specifies commutative ring with one
class RingComOne(elemType: Type)(set: Set elemType)(sum: elemType → elemType → elemType)(mul: elemType → elemType → elemType) where
  -- neutral by addition
  zero: elemType
  -- neutral by multiplication
  one: elemType

  -- Addition is defined at the set
  sumDef: ∀a b: elemType, a∈set → b∈set → (sum a b)∈set
  -- Multiplication is defined at the set
  mulDef: ∀a b: elemType, a∈set → b∈set → (mul a b)∈set

  -- Addition commutative
  sumComm: ∀a b: elemType, a∈set → b∈set → (sum a b) = (sum b a)
  -- Addition associative
  sumAssoc: ∀a b c: elemType, a∈set → b∈set → c∈set → (sum (sum a b) c) = (sum a (sum b c))
  zeroEx: zero∈set
  zeroProp: (∀a:elemType, a∈set → (sum a zero) = a)
  sumRev: ∀a:elemType, a∈set → (∃b:elemType, b∈set ∧ (sum a b) = zero)

  -- Multiplication commutative
  multComm: ∀a b: elemType, a∈set → b∈set → (mul a b) = (mul b a)
  -- Multiplication associative
  multAssoc: ∀a b c: elemType, a∈set → b∈set → c∈set → (mul (mul a b) c) = (mul a (mul b c))
  oneEx: one∈set
  oneProp: (∀a:elemType, a∈set → (mul a one) = a)

  -- Multiplication is distributive by addition
  multDistr: ∀a b c: elemType, a∈set → b∈set → c∈set → mul c (sum a b) = sum (mul c a) (mul c b)
