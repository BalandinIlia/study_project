import Mathlib.Data.Int.Basic
import Mathlib.Data.Set.Basic
import StudyProject.MyAbstractAlgebra.Definitions.Ring
import StudyProject.MyAbstractAlgebra.Definitions.RingComOne

-- This file defines a field
namespace MY

class Field(elemType: Type)
  extends ringCO: RingComOne elemType where
MultInv: ∀a:elemType, ¬(a = zero) →
                      (∃b:elemType, mul a b = one)
