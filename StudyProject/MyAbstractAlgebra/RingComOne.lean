import Mathlib.Data.Int.Basic
import Mathlib.Data.Set.Basic
import StudyProject.MyAbstractAlgebra.Ring

-- This file defines commutative ring with one
namespace MY

class RingComOne(elemType: Type)
                (set: Set elemType)
                (sum: elemType → elemType → elemType)
                (mul: elemType → elemType → elemType)
                extends ring: Ring elemType set sum mul where
  -- neutral by multiplication
  one: elemType
  oneEx: one∈set
  oneProp: (∀a:elemType, a∈set → (mul a one) = a)

  -- Multiplication commutative
  multComm: ∀a b: elemType, a∈set → b∈set → (mul a b) = (mul b a)
