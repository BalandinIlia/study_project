import Mathlib.Data.Int.Basic
import Mathlib.Data.Set.Basic
import StudyProject.Ring
import StudyProject.RingComOne

-- This file defines a field
namespace MY

class Field(elemType: Type)
           (set: Set elemType)
           (sum: elemType → elemType → elemType)
           (mul: elemType → elemType → elemType)
  extends ringCO: RingComOne elemType set sum mul where
MultInv: ∀a:elemType, a∈set → ¬(a = zero) → (∃b:elemType, b∈set ∧ mul a b = one)
