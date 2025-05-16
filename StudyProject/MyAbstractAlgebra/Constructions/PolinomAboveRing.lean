import Mathlib.Data.Int.Basic
import Mathlib.Data.Set.Basic
import StudyProject.MyAbstractAlgebra.Definitions.RingComOne
import StudyProject.MyAbstractAlgebra.Examples.RingOfSets
import StudyProject.MyAbstractAlgebra.Examples.GaluaField

namespace MY

-- Utility function: sums two lists according to given sum function
def sumLists{TElem: Type}
            (zero: TElem)
            (sum: TElem → TElem → TElem)
            (l1: List TElem)
            (l2: List TElem): List TElem :=
  List.zipWithAll
  (fun z1 z2:Option TElem =>sum (z1.getD zero) (z2.getD zero))
  l1
  l2

-- tests
#eval sumLists 0 (fun z1 z2:ℤ => z1+z2) [1,2,3] []
#eval sumLists 0 (fun z1 z2:ℤ => z1+z2) [] [1,2,3]
#eval sumLists 0 (fun z1 z2:ℤ => z1+z2) [5,6] [1,2,3]
#eval sumLists 0 (fun z1 z2:ℤ => z1+z2) [5,6,7,8] [1,2,3]

-- Utility function: multiplies two lists like they are polynoms
def mulLists{TElem: Type}
            (zero: TElem)
            (sum: TElem → TElem → TElem)
            (mul: TElem → TElem → TElem)
            (l1: List TElem)
            (l2: List TElem): List TElem :=
  match l1 with
  | List.nil       => List.nil
  | List.cons x xs => sumLists zero
                               sum
                               (List.map (fun el:TElem => mul el x) l2)
                               (List.cons zero (mulLists zero sum mul xs l2))

-- tests
#eval mulLists 0 (fun z1 z2:ℤ => z1+z2) (fun z1 z2:ℤ => z1*z2) [1,2,3] []
#eval mulLists 0 (fun z1 z2:ℤ => z1+z2) (fun z1 z2:ℤ => z1*z2) [] [1,2,3]
#eval mulLists 0 (fun z1 z2:ℤ => z1+z2) (fun z1 z2:ℤ => z1*z2) [5,6] [1,2,3]
#eval mulLists 0 (fun z1 z2:ℤ => z1+z2) (fun z1 z2:ℤ => z1*z2) [5,6,7,8] [1,2,3]

instance PolyRing(TElem: Type)
                 [ring: RingComOne TElem]:
                 RingComOne (List TElem):=
  {
    sum := sumLists ring.zero ring.sum
    mul := mulLists ring.zero ring.sum ring.mul

    zero := List.nil
    one := [ring.one]

    sumComm := by sorry
    zeroProp := by sorry
    sumAssoc := by sorry
    sumRev := by sorry
    multAssoc := by sorry
    multDistrLeft := by sorry
    multDistrRight := by sorry
    oneProp := by sorry
    multComm := by sorry
  }

--instance ins:RingComOne (List ElemGal):=PolyRing ElemGal

--#check ins
