import Mathlib.Data.Int.Basic
import Mathlib.Data.Set.Basic
import StudyProject.RingComOne
import StudyProject.RingComOneSet
import StudyProject.GaluaField

namespace MY

def inSet{TElem: Type}
         (set: Set TElem)
         (l: List TElem):Prop :=
  match l with
  | List.nil => True
  | List.cons x1 xs1 => x1∈set ∧ (@inSet TElem set xs1)

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
      sorry
    mulDef := by sorry
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
