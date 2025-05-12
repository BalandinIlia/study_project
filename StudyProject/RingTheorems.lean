import Mathlib.Data.Int.Basic
import Mathlib.Data.Set.Basic
import StudyProject.Ring

-- This file provides some theorems for rings
namespace MY

theorem ringTheorem1{t: Type}
                    {s: Set t}
                    {sum: t → t → t}
                    {mul: t → t → t}
                    (ring: Ring t s sum mul):
  ∀a b c: t, a∈s →
             b∈s →
             c∈s →
             ((a = b) ↔ (sum a c = sum c b)) := by
  intro a b c
  intro aIn bIn cIn
  apply Iff.intro
  {
    intro eq
    have eq2: sum a c = sum b c := by
      aesop
    rw [ring.sumComm b c bIn cIn] at eq2
    apply eq2
  }
  {
    intro eq
    let ⟨mc, pmc⟩ := ring.sumRev c cIn
    have eq2: sum (sum a c) mc = sum (sum c b) mc := by
      aesop
    rw [ring.sumAssoc a c mc aIn cIn] at eq2
    rw [ring.sumComm c b cIn bIn] at eq2
    rw [ring.sumAssoc b c mc bIn cIn] at eq2
    simp [pmc] at eq2
    simp [ring.zeroProp a aIn] at eq2
    simp [ring.zeroProp b bIn] at eq2
    apply eq2
    aesop
    aesop
  }

theorem ringTheorem2{t: Type}
                    {s: Set t}
                    {sum: t → t → t}
                    {mul: t → t → t}
                    (ring: Ring t s sum mul):
  ∀a b c d: t, a∈s →
               b∈s →
               c∈s →
               d∈s →
               mul (sum a b) (sum c d) = sum (sum (mul a c) (mul b c)) (sum (mul a d) (mul b d)) := by
  intro a b c d
  intro aIn bIn cIn dIn

  rw [ring.multDistrLeft c d (sum a b)]
  rw [ring.multDistrRight a b c]
  rw [ring.multDistrRight a b d]

  apply aIn
  apply bIn
  apply dIn
  apply aIn
  apply bIn
  apply cIn
  apply cIn
  apply dIn
  apply ring.sumDef
  apply aIn
  apply bIn
