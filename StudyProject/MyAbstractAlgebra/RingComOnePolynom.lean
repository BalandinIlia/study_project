import Mathlib.Data.Int.Basic
import Mathlib.Data.Set.Basic
import StudyProject.MyAbstractAlgebra.RingComOne
import StudyProject.MyAbstractAlgebra.RingComOneSet
import StudyProject.MyAbstractAlgebra.GaluaField

namespace MY

-- Utility function: check if all elements of given list belong to given set
def inSet{TElem: Type}
         (set: Set TElem)
         (l: List TElem):Prop :=
  match l with
  | List.nil => True
  | List.cons x1 xs1 => x1∈set ∧ (@inSet TElem set xs1)

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

-- Polinom (like a*x*x+b*x+c) (in our notation coefficients follow: c,b,a)
--
-- This is polinom above given ring, so it consists of two parts:
-- 1) list of polynom coefficients
-- 2) proof of that the coefficients are in the ring
--
-- Here we have the following hierarchy:
-- 1) Polynom:
--    From Lean point of view:
--        This is a rule, which takes a ring and returns
--        pattern for a set of terms. The pattern contains
--        names of terms and their types
--    From mathematical point of view:
--        This is the most common definition of polynom:
--        arbitrary polinom above arbitrary ring. It consists
--        of coefficients and proof that they are from the
--        ring
-- 2) Polynom ring:
--    From Lean point of view:
--        This is a particular pattern for particular ring.
--        All terms have definite type, however they don't
--        have definite values.
--    From mathematical point of view:
--        This is a definition of polynom over particular ring.
-- 3) Instance of Polynom ring:
--    From Lean point of view:
--        This is a particular values of terms specified in
--        paragraph 2.
--    From mathematical point of view:
--        This is a particular polinom over particular field.
--
-- So this class is intended to have multiple instances of
-- the same type.
class Polynom{TElem: Type}
             {set: Set TElem}
             {sum: TElem → TElem → TElem}
             {mult: TElem → TElem → TElem}
             (_: RingComOne TElem set sum mult) where
  coef: List TElem
  inRing: inSet set coef

def sumPoly{TElem: Type}
           {set: Set TElem}
           {sum: TElem → TElem → TElem}
           {mult: TElem → TElem → TElem}
           (ring: RingComOne TElem set sum mult)
           (p1: Polynom ring)
           (p2: Polynom ring): Polynom ring :=
  {
    coef := sumLists ring.zero sum p1.coef p2.coef
    inRing := sorry
  }

def mulPoly{TElem: Type}
           {set: Set TElem}
           {sum: TElem → TElem → TElem}
           {mult: TElem → TElem → TElem}
           (ring: RingComOne TElem set sum mult)
           (p1: Polynom ring)
           (p2: Polynom ring): Polynom ring :=
  {
    coef := mulLists ring.zero sum mult p1.coef p2.coef
    inRing := sorry
  }

def PolyRing{TElem: Type}
            {set: Set TElem}
            {sum: TElem → TElem → TElem}
            {mult: TElem → TElem → TElem}
            (ring: RingComOne TElem set sum mult):
            RingComOne (Polynom ring)
                       ({p:Polynom ring | True})
                       (sumPoly ring)
                       (mulPoly ring) :=
  {
    sumDef := by
      simp
    mulDef := by
      simp
    zero :=
    {
      coef := List.nil
      inRing := by
        simp [inSet]
    }
    one :=
    {
      coef := [ring.one]
      inRing := by
        simp [inSet]
        apply ring.oneEx
    }
    sumComm := by sorry
    zeroEx := by
      simp
    oneEx := by
      simp
    zeroProp := by sorry
    sumAssoc := by sorry
    sumRev := by sorry
    multAssoc := by sorry
    multDistrLeft := by sorry
    multDistrRight := by sorry
    oneProp := by sorry
    multComm := by sorry
  }

def polySets := PolyRing ringSets

#print polySets
#check polySets.zero
#check polySets.one
