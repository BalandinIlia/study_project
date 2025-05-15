import Mathlib.Data.Int.Basic
import Mathlib.Data.Set.Basic
import StudyProject.MyAbstractAlgebra.Definitions.Ring

-- This file provides some theorems for rings
namespace MY

theorem ringTheorem1{t: Type}
                    (ring: Ring t):
  ∀a b c: t, ((a = b) ↔ (ring.sum a c = ring.sum c b)) := by
  intro a b c
  apply Iff.intro
  {
    intro eq
    have eq2: ring.sum a c = ring.sum b c := by
      aesop
    rw [ring.sumComm b c] at eq2
    apply eq2
  }
  {
    intro eq
    let ⟨mc, pmc⟩ := ring.sumRev c
    have eq2: ring.sum (ring.sum a c) mc = ring.sum (ring.sum c b) mc := by
      aesop
    rw [ring.sumAssoc a c mc] at eq2
    rw [ring.sumComm c b] at eq2
    rw [ring.sumAssoc b c mc] at eq2
    simp [pmc] at eq2
    simp [ring.zeroProp a] at eq2
    simp [ring.zeroProp b] at eq2
    apply eq2
  }

theorem ringTheorem2{t: Type}
                    (ring: Ring t):
  ∀a b c d: t, ring.mul (ring.sum a b) (ring.sum c d) = ring.sum (ring.sum (ring.mul a c) (ring.mul b c)) (ring.sum (ring.mul a d) (ring.mul b d)) := by
  intro a b c d

  rw [ring.multDistrLeft c d (ring.sum a b)]
  rw [ring.multDistrRight a b c]
  rw [ring.multDistrRight a b d]

-- a*0=t1
-- a*(0+0)=a*(0+0)=t2
-- a*(0+0)=a*0+a*0=t3
-- a*0=a*0+a*0
-- -a*0=t4
-- a*0+(-a*0)=a*0+a*0+(-a*0)
theorem multZero{T: Type}
                (ring: Ring T):
  ∀a:T, (ring.mul a ring.zero) = ring.zero := by
  intro a

  let t1 := ring.mul a ring.zero
  let t2 := ring.mul a (ring.sum ring.zero ring.zero)
  let t3 := ring.sum t1 t1
  let ⟨t4, t4Inv⟩ := ring.sumRev t1

  have eq1: t1=t2 := by
    simp [t1, t2, (ring.zeroProp ring.zero)]
  have eq2: t2=t3 := by
    simp [t2, t3, ring.multDistrLeft ring.zero ring.zero a, t1]
  have eq3: t1=t3 := by
    apply Eq.trans eq1 eq2
  have eq4: ring.sum t1 t4 = ring.sum t3 t4 := by
    simp [eq3]

  simp [t3] at eq4
  rw [t4Inv] at eq4
  rw [ring.sumAssoc t1 t1 t4] at eq4
  rw [t4Inv] at eq4
  rw [ring.zeroProp t1] at eq4
  simp [t1] at eq4
  rw [Eq.comm] at eq4
  apply eq4
