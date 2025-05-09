import Mathlib.Data.Int.Basic
import Mathlib.Data.Set.Basic

namespace MY

class isSumMulDef(elemType: Type)(set: Set elemType)(sum: elemType → elemType → elemType)(mul: elemType → elemType → elemType) where
  sumDef: ∀a b: elemType, a∈set → b∈set → (sum a b)∈set
  mulDef: ∀a b: elemType, a∈set → b∈set → (mul a b)∈set

class grComm(elemType: Type)(set: Set elemType)(sum: elemType → elemType → elemType) where
  sumComm: ∀a b: elemType, a∈set → b∈set → (sum a b) = (sum b a)

class isRing(elemType: Type)(set: Set elemType)(sum: elemType → elemType → elemType)(mul: elemType → elemType → elemType) extends (isSumMulDef elemType set sum mul), (grComm elemType set sum) where
  z: elemType

  sumAssoc: ∀a b c: elemType, a∈set → b∈set → c∈set → (sum (sum a b) c) = (sum a (sum b c))

  zeroEx: z∈set
  zeroProp: (∀a:elemType, a∈set → (sum a z) = a)

  sumRev: ∀a:elemType, a∈set → (∃b:elemType, b∈set ∧ (sum a b) = z)

  multAssoc: ∀a b c: elemType, a∈set → b∈set → c∈set → (mul (mul a b) c) = (mul a (mul b c))

  multDistrLeft: ∀a b c: elemType, a∈set → b∈set → c∈set → mul c (sum a b) = sum (mul c a) (mul c b)

  multDistrRight: ∀a b c: elemType, a∈set → b∈set → c∈set → mul (sum a b) c = sum (mul a c) (mul b c)

theorem th(t: Type)(s: Set t)(sum: t → t → t)(mul: t → t → t)[st: isRing t s sum mul]:
  ∀a b c: t, (a∈s) → (b∈s) → (c∈s) → ((a = b) ↔ (sum a c = sum c b)) := by
  intro a b c
  intro aIn bIn cIn
  apply Iff.intro
  {
    intro eq
    have eq2: sum a c = sum b c := by
      aesop
    rw [st.sumComm b c bIn cIn] at eq2
    apply eq2
  }
  {
    intro eq
    let ⟨mc, pmc⟩ := st.sumRev c cIn
    have eq2: sum (sum a c) mc = sum (sum c b) mc := by
      aesop
    rw [st.sumAssoc a c mc aIn cIn] at eq2
    rw [st.sumComm c b cIn bIn] at eq2
    rw [st.sumAssoc b c mc bIn cIn] at eq2
    simp [pmc] at eq2
    simp [st.zeroProp a aIn] at eq2
    simp [st.zeroProp b bIn] at eq2
    apply eq2
    aesop
    aesop
  }

theorem th2(t: Type)(s: Set t)(sum: t → t → t)(mul: t → t → t)[st: isRing t s sum mul]:
  ∀a b c d: t, (a∈s)→(b∈s)→(c∈s)→(d∈s)→ mul (sum a b) (sum c d) = sum (sum (mul a c) (mul b c)) (sum (mul a d) (mul b d)) := by
  intro a b c d
  intro aIn bIn cIn dIn

  rw [st.multDistrLeft c d (sum a b)]
  rw [st.multDistrRight a b c]
  rw [st.multDistrRight a b d]

  apply aIn
  apply bIn
  apply dIn
  apply aIn
  apply bIn
  apply cIn
  apply cIn
  apply dIn
  apply st.sumDef
  apply aIn
  apply bIn

def Func := ℤ → ℤ

def allFunc:Set Func := {f:Func | ∀x y:ℤ, f (x+y) = f x + f y}

def tr1: Func → Func → Func
| f1, f2 => (fun x:ℤ => (f1 x) + (f2 x))

def tr2: Func → Func → Func
| f1, f2 => (fun x:ℤ => (f1 (f2 x)))

instance hi: isRing Func allFunc tr1 tr2 :=
  {
    z := (fun x:ℤ => 0)
    sumDef := by
      intro a b
      intro aC bC
      rw [tr1]
      rw [allFunc]
      simp
      intro x y
      have eqa: a (x+y) = a x + a y := by
        aesop
      rw [eqa]
      have eqb: b (x+y) = b x + b y := by
        aesop
      rw [eqb]
      omega
    mulDef := by
      intro a b
      intro aC bC
      rw [tr2]
      rw [allFunc]
      intro x y
      simp
      have eq: b (x+y) = b x + b y := by
        aesop
      rw [eq]
      aesop
    sumComm := by
      intro a b
      intro aC bC
      simp [tr1, Func]
      funext x
      apply Int.add_comm
    sumAssoc := by
      intro a b c
      intro aC bC cC
      simp [tr1, Func]
      funext x
      apply Int.add_assoc
    zeroEx := by
      simp [allFunc]
    zeroProp := by
      intro a
      intro aC
      clear aC
      simp [tr1]
    sumRev := by
      intro a
      intro aIn
      exists (fun x:ℤ => -(a x))
      simp [allFunc, tr1]
      apply And.intro
      {
        intro x y
        have eq: a (x+y) = a x + a y := by
          aesop
        rw [eq]
        generalize hX: a x = X
        generalize hY: a y = Y
        clear hX hY a aIn x y eq
        omega
      }
      {
        funext x
        omega
      }
    multAssoc := by
      intro a b c
      intro aIn bIn cIn
      simp [tr2]
    multDistrLeft := by
      intro a b c
      intro aIn bIn cIn
      simp [tr1, tr2]
      funext x
      aesop
    multDistrRight := by
      intro a b c
      intro aIn bIn cIn
      simp [tr1, tr2]
  }

theorem th2f:
  ∀a b c d: Func, (a∈allFunc)→(b∈allFunc)→(c∈allFunc)→(d∈allFunc)→ tr2 (tr1 a b) (tr1 c d) = tr1 (tr1 (tr2 a c) (tr2 b c)) (tr1 (tr2 a d) (tr2 b d)) := by
  apply th2 Func allFunc tr1 tr2
