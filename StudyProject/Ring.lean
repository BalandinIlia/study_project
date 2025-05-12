import Mathlib.Data.Int.Basic
import Mathlib.Data.Set.Basic

-- This file defines ring object from abstract algebra
namespace MY

-- This class represents a set at which addition and multiplication
-- are defined. In other words result of addition and of multiplication is still
-- in the set
class SumMulDef(elemType: Type)
               (set: Set elemType)
               (sum: elemType → elemType → elemType)
               (mul: elemType → elemType → elemType) where
  sumDef: ∀a b: elemType, a∈set → b∈set → (sum a b)∈set
  mulDef: ∀a b: elemType, a∈set → b∈set → (mul a b)∈set

-- Commutative group
class GrComm(elemType: Type)
            (set: Set elemType)
            (sum: elemType → elemType → elemType) where
  sumComm: ∀a b: elemType, a∈set →
                           b∈set →
                           sum a b = sum b a

-- ring (not commutative, not with one)
class Ring(elemType: Type)
          (set: Set elemType)
          (sum: elemType → elemType → elemType)
          (mul: elemType → elemType → elemType)
          extends defined: SumMulDef elemType set sum mul,
                  comm: GrComm elemType set sum
          where
  -- zero and its properties
  zero: elemType
  zeroEx: zero∈set
  zeroProp: ∀a:elemType, a∈set → (sum a zero) = a

  -- sum properties
  sumAssoc: ∀a b c: elemType, a∈set →
                              b∈set →
                              c∈set →
                              sum (sum a b) c = sum a (sum b c)
  sumRev: ∀a:elemType, a∈set →
                       ∃b:elemType, b∈set ∧ (sum a b) = zero

  -- multiplication properties
  multAssoc: ∀a b c: elemType, a∈set →
                                b∈set →
                                c∈set →
                                mul (mul a b) c = mul a (mul b c)
  multDistrLeft: ∀a b c: elemType, a∈set →
                                   b∈set →
                                   c∈set →
                                   mul c (sum a b) = sum (mul c a) (mul c b)
  multDistrRight: ∀a b c: elemType, a∈set →
                                    b∈set →
                                    c∈set →
                                    mul (sum a b) c = sum (mul a c) (mul b c)
