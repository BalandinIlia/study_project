import Mathlib.Data.Int.Basic
import Mathlib.Data.Set.Basic
import StudyProject.MyAbstractAlgebra.Definitions.Ring

-- This file defines commutative ring with one
namespace MY

class RingComOne(elemType: Type)
                extends ring: Ring elemType where
  -- neutral by multiplication
  one: elemType
  oneProp: (∀a:elemType, mul a one = a)

  -- Multiplication commutative
  multComm: ∀a b: elemType, mul a b = mul b a
