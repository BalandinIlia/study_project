import Mathlib.Data.Int.Basic
import Mathlib.Data.Set.Basic
import StudyProject.MyAbstractAlgebra.Definitions.RingComOne
import StudyProject.MyAbstractAlgebra.Examples.RingOfSets
import StudyProject.MyAbstractAlgebra.Examples.GaluaField

-- This file introduces "multiplication" of commutatative rings with one
namespace MY

-- Pair of elements of two types: A and B
structure Pair(A B: Type) where
f:A
s:B

-- Composes operation on type A and operation on type B into operation on type Pair A B
def OperComp{A B: Type}(sa: A → A → A)(sb: B → B → B): (Pair A B) → (Pair A B) → (Pair A B)
| (Pair.mk f1 s1), (Pair.mk f2 s2) => (Pair.mk (sa f1 f2) (sb s1 s2))

-- "Multiplies" two commutative rings with 1
-- Result is another commutative ring with 1
instance multiplyrings(A B:Type)
                 [ringA: RingComOne A]
                 [ringB: RingComOne B]:
(RingComOne (Pair A B)) :=
  {
    sum := OperComp ringA.sum ringB.sum
    mul := OperComp ringA.mul ringB.mul

    zero := @Pair.mk A B ringA.zero ringB.zero
    one := @Pair.mk A B ringA.one ringB.one

    sumComm := by
      intro c1 c2
      let ⟨a1,b1⟩ := c1
      let ⟨a2,b2⟩ := c2
      simp [OperComp]
      apply And.intro
      apply ringA.sumComm
      apply ringB.sumComm
    sumAssoc := by
      intro c1 c2 c3
      let ⟨a1,b1⟩ := c1
      let ⟨a2,b2⟩ := c2
      let ⟨a3,b3⟩ := c3
      clear c1 c2 c3
      simp [OperComp]
      apply And.intro
      apply ringA.sumAssoc
      apply ringB.sumAssoc
    zeroProp := by
      intro c1
      let ⟨a1,b1⟩ := c1
      clear c1
      simp [OperComp]
      apply And.intro
      apply ringA.zeroProp
      apply ringB.zeroProp
    sumRev := by
      intro c
      let ⟨a,b⟩ := c
      clear c
      let ⟨a_1,propA⟩ := ringA.sumRev a
      let ⟨b_1,propB⟩ := ringB.sumRev b
      exists Pair.mk a_1 b_1
      simp [OperComp]
      aesop
    multComm := by
      intro c1 c2
      let ⟨a1,b1⟩ := c1
      let ⟨a2,b2⟩ := c2
      clear c1 c2
      simp [OperComp]
      apply And.intro
      apply ringA.multComm
      apply ringB.multComm
    multAssoc := by
      intro c1 c2 c3
      let ⟨a1,b1⟩ := c1
      let ⟨a2,b2⟩ := c2
      let ⟨a3,b3⟩ := c3
      clear c1 c2 c3
      simp [OperComp]
      apply And.intro
      apply ringA.multAssoc
      apply ringB.multAssoc
    oneProp := by
      intro c1
      let ⟨a1,b1⟩ := c1
      clear c1
      simp [OperComp]
      apply And.intro
      apply ringA.oneProp
      apply ringB.oneProp
    multDistrLeft := by
      intro c1 c2 c3
      let ⟨a1,b1⟩ := c1
      let ⟨a2,b2⟩ := c2
      let ⟨a3,b3⟩ := c3
      clear c1 c2 c3
      simp [OperComp]
      apply And.intro
      apply ringA.multDistrLeft
      apply ringB.multDistrLeft
    multDistrRight := by
      intro c1 c2 c3
      let ⟨a1,b1⟩ := c1
      let ⟨a2,b2⟩ := c2
      let ⟨a3,b3⟩ := c3
      clear c1 c2 c3
      simp [OperComp]
      apply And.intro
      apply ringA.multDistrRight
      apply ringB.multDistrRight
    }

--instance ins: RingComOne (Pair (Set ℤ) ElemGal) := multiplyrings (Set ℤ) ElemGal

--def GaluaRingCO := multiplyrings GaluaField.ringCO GaluaField.ringCO

--#print GaluaRingCO
--#check GaluaRingCO.zero
--#check GaluaRingCO.one

--def exam := multiplyrings GaluaField.ringCO ringSets

--#print exam
--#check exam.zero
--#check exam.one
