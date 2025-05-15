import Mathlib.Data.Int.Basic
import Mathlib.Data.Set.Basic
import StudyProject.MyAbstractAlgebra.Definitions.RingComOne

namespace MY

lemma fol(A B: Prop):
(A→B)→((¬A)→B)→B := by
  intro h1
  intro h2
  have g:A∨(¬A) := by
    clear h1 h2 B
    apply by_contradiction
    aesop
  aesop

def diff(s1: Set ℤ)(s2: Set ℤ): Set ℤ :=
    {z:ℤ | z∈s1 ∧ (¬z∈s2)}

def diff2(s1: Set ℤ)(s2: Set ℤ): Set ℤ :=
    (diff s1 s2) ∪ (diff s2 s1)

def inter(s1: Set ℤ)(s2: Set ℤ): Set ℤ := s1 ∩ s2

instance ringSets: RingComOne (Set ℤ) :=
  {
    sum := diff2
    mul := inter
    sumComm := by
      intro s1 s2
      simp [diff2, inter, diff, Set.union_def]
      have helper: ∀a:ℤ, (a ∈ s1 ∧ a ∉ s2 ∨ a ∈ s2 ∧ a ∉ s1) ↔
                         (a ∈ s2 ∧ a ∉ s1 ∨ a ∈ s1 ∧ a ∉ s2) := by
        intro x
        apply fol (x∈s1)
        {
          intro h1
          simp [h1]
        }
        {
          intro h1
          simp [h1]
        }
      apply Set.ext helper
    sumAssoc := by
      intro s1 s2 s3
      simp [inter, diff2, diff]
      simp [Set.union_def]
      have helper: ∀a:ℤ, ((a∈s1 ∧ a∉s2 ∨ a∈s2 ∧ a∉s1) ∧ a∉s3 ∨ (a∈s3 ∧ (a∈s1 → a∈s2)) ∧ a∈s3 ∧ (a∈s2 → a∈s1)) ↔
                         ((a∈s1 ∧ (a∈s2 → a∈s3)) ∧ a∈s1 ∧ (a∈s3 → a∈s2) ∨ (a∈s2 ∧ a∉s3 ∨ a∈s3 ∧ a∉s2) ∧ a∉s1) := by
        intro x
        apply fol (x∈s1)
        {
          intro h1
          simp [h1]
          apply fol (x∈s2)
          {
            intro h2
            simp [h2]
          }
          {
            intro h2
            simp [h2]
          }
        }
        {
          intro h1
          simp [h1]
        }
      apply Set.ext helper
    zero := {}
    zeroProp := by
      simp [diff2, diff]
    sumRev := by
      intro s1
      exists s1
      simp [diff2]
      simp [diff]
    multComm := by
      intro s1 s2
      simp [inter, diff2, diff]
      apply Set.inter_comm
    multAssoc := by
      intro s1 s2 s3
      simp [inter, diff2, diff]
      apply Set.inter_assoc
    multDistrLeft := by
      intro s1 s2 s3
      simp [inter, diff2, diff]
      simp [Set.union_def]
      aesop
    multDistrRight := by
      intro s1 s2 s3
      simp [inter, diff2, diff]
      simp [Set.union_def]
      aesop
    one := {z:ℤ | True}
    oneProp := by
      simp [inter]
  }
