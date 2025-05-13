import Mathlib.Data.Int.Basic
import Mathlib.Data.Set.Basic
import StudyProject.RingComOne
import StudyProject.RingComOneSet
import StudyProject.GaluaField

namespace MY

def Polynom{TElem: Type}
           {set: Set TElem}
           {sum: TElem → TElem → TElem}
           {mult: TElem → TElem → TElem}
           (_: RingComOne TElem set sum mult):Type := List TElem

def sumPoly{TElem: Type}
           {set: Set TElem}
           {sum: TElem → TElem → TElem}
           {mult: TElem → TElem → TElem}
           (ring: RingComOne TElem set sum mult)
           (p1: Polynom ring)
           (p2: Polynom ring): Polynom ring :=
  match p1, p2 with
  | List.nil, List.nil                 => List.nil
  | l, List.nil                        => l
  | List.nil, l                        => l
  | List.cons x1 xs1, List.cons x2 xs2 => List.cons (sum x1 x2) (@sumPoly TElem set sum mult ring xs1 xs2)


def multSc{TElem: Type}
          {set: Set TElem}
          {sum: TElem → TElem → TElem}
          {mult: TElem → TElem → TElem}
          (ring: RingComOne TElem set sum mult)
          (sc: TElem)
          (p: Polynom ring): Polynom ring :=
  match p with
  | List.nil => List.nil
  | List.cons x xs => List.cons (mult sc x) (@multSc TElem set sum mult ring sc xs)

def multPoly{TElem: Type}
           {set: Set TElem}
           {sum: TElem → TElem → TElem}
           {mult: TElem → TElem → TElem}
           (ring: RingComOne TElem set sum mult)
           (p1: Polynom ring)
           (p2: Polynom ring): Polynom ring :=
  match p1, p2 with
  | List.cons x1 xs1, p =>
      sumPoly ring (@multSc TElem set sum mult ring x1 p) (List.cons ring.zero (multPoly ring xs1 p))
  | List.nil, _ => List.nil

def inRing{TElem: Type}
          {set: Set TElem}
          {sum: TElem → TElem → TElem}
          {mult: TElem → TElem → TElem}
          {ring: RingComOne TElem set sum mult}
          (p: (Polynom ring)):Prop :=
  match p with
  | List.nil => True
  | List.cons x1 xs1 => x1∈set ∧ (@inRing TElem set sum mult ring xs1)

def PolyRing{TElem: Type}
            {set: Set TElem}
            {sum: TElem → TElem → TElem}
            {mult: TElem → TElem → TElem}
            (ring: RingComOne TElem set sum mult):
            RingComOne (Polynom ring)
                       ({p:Polynom ring | inRing p})
                       (sumPoly ring)
                       (multPoly ring) :=
  {
    sumDef := by
      sorry
    mulDef := by sorry
    zero := List.nil
    one := List.cons ring.one List.nil
    sumComm := by sorry
    zeroEx := by
      simp [inRing]
    oneEx := by
      simp [inRing]
      apply ring.oneEx
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
