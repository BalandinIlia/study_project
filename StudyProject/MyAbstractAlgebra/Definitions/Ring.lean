import Mathlib.Data.Int.Basic
import Mathlib.Data.Set.Basic

-- This file defines ring object from abstract algebra
namespace MY

-- Commutative group
class GrComm(elemType: Type) where
  sum: elemType → elemType → elemType
  sumComm: ∀a b: elemType, sum a b = sum b a

-- ring (not commutative, not with one)
class Ring(elemType: Type)
          extends comm: GrComm elemType
          where
  mul: elemType → elemType → elemType

  -- zero and its property
  zero: elemType
  zeroProp: ∀a:elemType, (sum a zero) = a

  -- sum properties
  sumAssoc: ∀a b c: elemType,
            sum (sum a b) c = sum a (sum b c)
  sumRev: ∀a:elemType,
          ∃b:elemType, sum a b = zero

  -- multiplication properties
  multAssoc: ∀a b c: elemType,
             mul (mul a b) c = mul a (mul b c)
  multDistrLeft: ∀a b c: elemType,
                 mul c (sum a b) = sum (mul c a) (mul c b)
  multDistrRight: ∀a b c: elemType,
                  mul (sum a b) c = sum (mul a c) (mul b c)
