import Mathlib.Data.Int.Basic
import Mathlib.Data.Set.Basic
import StudyProject.MyAbstractAlgebra.Definitions.Ring

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

-- a*0=t1
-- a*(0+0)=a*(0+0)=t2
-- a*(0+0)=a*0+a*0=t3
-- a*0=a*0+a*0
-- -a*0=t4
-- a*0+(-a*0)=a*0+a*0+(-a*0)
theorem multZero{T: Type}
                {set: Set T}
                {sum: T → T → T}
                {mul: T → T → T}
                (ring: Ring T set sum mul):
  ∀a:T, a∈set → ((mul a ring.zero) = ring.zero) := by
  intro a aIn

  let t1 := mul a ring.zero
  have t1In: t1∈set := by
    apply ring.mulDef
    apply aIn
    apply ring.zeroEx
  let t2 := mul a (sum ring.zero ring.zero)
  let t3 := sum t1 t1
  let ⟨t4, tmp⟩ := ring.sumRev t1 t1In
  let ⟨t4In, t4Inv⟩ := tmp
  clear tmp

  have eq1: t1=t2 := by
    simp [t1, t2, (ring.zeroProp ring.zero ring.zeroEx)]
  have eq2: t2=t3 := by
    simp [t2, t3, ring.multDistrLeft ring.zero ring.zero a ring.zeroEx ring.zeroEx aIn, t1]
  have eq3: t1=t3 := by
    apply Eq.trans eq1 eq2
  have eq4: sum t1 t4 = sum t3 t4 := by
    simp [eq3]

  simp [t3] at eq4
  rw [t4Inv] at eq4
  rw [ring.sumAssoc t1 t1 t4 t1In t1In t4In] at eq4
  rw [t4Inv] at eq4
  rw [ring.zeroProp t1 t1In] at eq4
  simp [t1] at eq4
  rw [Eq.comm] at eq4
  apply eq4
