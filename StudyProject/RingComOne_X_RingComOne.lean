import Mathlib.Data.Int.Basic
import Mathlib.Data.Set.Basic
import StudyProject.RingComOne
import StudyProject.GaluaField

-- This file introduces "multiplication" of commutatative rings with one
namespace MY

-- Pair of elements of two types: A and B
structure Pair(A B: Type) where
f:A
s:B

-- Cartesian product of two sets
def Sett{A B: Type}(sa: Set A)(sb: Set B): Set (Pair A B) :=
  {p: Pair A B | p.f∈sa ∧ p.s∈sb}

-- Composes operation on type A and operation on type B into operation on type Pair A B
def OperComp{A B: Type}(sa: A → A → A)(sb: B → B → B): (Pair A B) → (Pair A B) → (Pair A B)
| (Pair.mk f1 s1), (Pair.mk f2 s2) => (Pair.mk (sa f1 f2) (sb s1 s2))

-- "Multiplies" two commutative rings with 1
-- Result is another commutative ring with 1
def multiplyrings{A B:Type}
                 {setA: Set A}
                 {setB: Set B}
                 {sumA: A → A → A}
                 {mulA: A → A → A}
                 {sumB: B → B → B}
                 {mulB: B → B → B}
                 (ringA: RingComOne A setA sumA mulA)
                 (ringB: RingComOne B setB sumB mulB):
(RingComOne (Pair A B)
            (Sett setA setB)
            (OperComp sumA sumB)
            (OperComp mulA mulB)
) :=
  {
    zero := @Pair.mk A B ringA.zero ringB.zero
    one := @Pair.mk A B ringA.one ringB.one
    sumDef := by
      intro c1 c2
      let ⟨a1,b1⟩ := c1
      let ⟨a2,b2⟩ := c2
      clear c1 c2
      simp [Sett, OperComp]
      intro ha1 hb1 ha2 hb2
      apply And.intro
      apply ringA.sumDef
      apply ha1
      apply ha2
      apply ringB.sumDef
      apply hb1
      apply hb2
    mulDef := by
      intro c1 c2
      let ⟨a1,b1⟩ := c1
      let ⟨a2,b2⟩ := c2
      clear c1 c2
      simp [Sett, OperComp]
      intro ha1 hb1 ha2 hb2
      apply And.intro
      apply ringA.mulDef
      apply ha1
      apply ha2
      apply ringB.mulDef
      apply hb1
      apply hb2
    sumComm := by
      intro c1 c2
      let ⟨a1,b1⟩ := c1
      let ⟨a2,b2⟩ := c2
      clear c1 c2
      simp [Sett, OperComp]
      intro ha1 hb1 ha2 hb2
      apply And.intro
      apply ringA.sumComm
      apply ha1
      apply ha2
      apply ringB.sumComm
      apply hb1
      apply hb2
    sumAssoc := by
      intro c1 c2 c3
      let ⟨a1,b1⟩ := c1
      let ⟨a2,b2⟩ := c2
      let ⟨a3,b3⟩ := c3
      clear c1 c2 c3
      simp [Sett, OperComp]
      intro ha1 hb1 ha2 hb2 ha3 hb3
      apply And.intro
      apply ringA.sumAssoc
      apply ha1
      apply ha2
      apply ha3
      apply ringB.sumAssoc
      apply hb1
      apply hb2
      apply hb3
    zeroEx := by
      simp [Sett]
      apply And.intro
      apply ringA.zeroEx
      apply ringB.zeroEx
    zeroProp := by
      intro c1
      let ⟨a1,b1⟩ := c1
      clear c1
      simp [Sett, OperComp]
      intro ha hb
      apply And.intro
      apply ringA.zeroProp
      apply ha
      apply ringB.zeroProp
      apply hb
    sumRev := by
      intro c cIn
      let ⟨a,b⟩ := c
      clear c
      simp [Sett] at cIn
      let ⟨aIn,bIn⟩ := cIn
      let ⟨a_1,propA⟩ := ringA.sumRev a aIn
      let ⟨b_1,propB⟩ := ringB.sumRev b bIn
      exists Pair.mk a_1 b_1
      simp [Sett, OperComp]
      aesop
    multComm := by
      intro c1 c2
      let ⟨a1,b1⟩ := c1
      let ⟨a2,b2⟩ := c2
      clear c1 c2
      simp [Sett, OperComp]
      intro ha1 hb1 ha2 hb2
      apply And.intro
      apply ringA.multComm
      apply ha1
      apply ha2
      apply ringB.multComm
      apply hb1
      apply hb2
    multAssoc := by
      intro c1 c2 c3
      let ⟨a1,b1⟩ := c1
      let ⟨a2,b2⟩ := c2
      let ⟨a3,b3⟩ := c3
      clear c1 c2 c3
      simp [Sett, OperComp]
      intro ha1 hb1 ha2 hb2 ha3 hb3
      apply And.intro
      apply ringA.multAssoc
      apply ha1
      apply ha2
      apply ha3
      apply ringB.multAssoc
      apply hb1
      apply hb2
      apply hb3
    oneEx := by
      simp [Sett]
      apply And.intro
      apply ringA.oneEx
      apply ringB.oneEx
    oneProp := by
      intro c1
      let ⟨a1,b1⟩ := c1
      clear c1
      simp [Sett, OperComp]
      intro ha hb
      apply And.intro
      apply ringA.oneProp
      apply ha
      apply ringB.oneProp
      apply hb
    multDistrLeft := by
      intro c1 c2 c3
      let ⟨a1,b1⟩ := c1
      let ⟨a2,b2⟩ := c2
      let ⟨a3,b3⟩ := c3
      clear c1 c2 c3
      simp [Sett, OperComp]
      intro ha1 hb1 ha2 hb2 ha3 hb3
      apply And.intro
      apply ringA.multDistrLeft
      apply ha1
      apply ha2
      apply ha3
      apply ringB.multDistrLeft
      apply hb1
      apply hb2
      apply hb3
    multDistrRight := by
      intro c1 c2 c3
      let ⟨a1,b1⟩ := c1
      let ⟨a2,b2⟩ := c2
      let ⟨a3,b3⟩ := c3
      clear c1 c2 c3
      simp [Sett, OperComp]
      intro ha1 hb1 ha2 hb2 ha3 hb3
      apply And.intro
      apply ringA.multDistrRight
      apply ha1
      apply ha2
      apply ha3
      apply ringB.multDistrRight
      apply hb1
      apply hb2
      apply hb3
  }

def GaluaRingCO := multiplyrings GaluaField.ringCO GaluaField.ringCO

#print GaluaRingCO
#eval GaluaRingCO.zero
#eval GaluaRingCO.one
