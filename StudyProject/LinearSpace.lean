import Mathlib.Data.Int.Basic
import Mathlib.Data.Set.Basic
import StudyProject.RingComOne
import StudyProject.Gal
import StudyProject.RingComOne_X_RingComOne

namespace MY

class Field(elemType: Type)
           (set: Set elemType)
           (sum: elemType → elemType → elemType)
           (mul: elemType → elemType → elemType)
  extends RingComOne elemType set sum mul where
MultInv: ∀a:elemType, a∈set → ¬(a = zero) → (∃b:elemType, b∈set ∧ mul a b = one)

-- list length
def length{T:Type}: List T → ℕ
| List.nil => 0
| List.cons _ l => Nat.succ (length l)

-- list prop
def listProp{T:Type}: List T → (T → Prop) → Prop
| List.nil, _         => 0=0
| (List.cons x l), pr => (pr x) ∧ (listProp l pr)

-- linear space
class LinSp(TCoef TVec: Type)
           (fi: Set TCoef)
           (sumF: TCoef → TCoef → TCoef)
           (mulF: TCoef → TCoef → TCoef)
           (mulV: TCoef → TVec → TVec)
           (sumV: TVec → TVec → TVec)
           extends Field TCoef fi sumF mulF
           where
  -- basic axioms
  VZero: TVec
  VSumComm: ∀v1 v2: TVec, sumV v1 v2 = sumV v2 v1
  VSumAssoc: ∀v1 v2 v3: TVec, sumV (sumV v1 v2) v3 = sumV v1 (sumV v2 v3)
  VMultLin: ∀v1 v2: TVec, ∀c: TCoef, c∈fi → mulV c (sumV v1 v2) = sumV (mulV c v1) (mulV c v2)
  VMultZero: ∀v: TVec, mulV zero v = VZero
  VMultOne: ∀v: TVec, mulV one v = v
  VMultVZero: ∀v: TVec, sumV VZero v = v

-- linear combination
def linCombImp{TCoef TVec: Type}
           {fi: Set TCoef}
           {sumF: TCoef → TCoef → TCoef}
           {mulF: TCoef → TCoef → TCoef}
           {mulV: TCoef → TVec → TVec}
           {sumV: TVec → TVec → TVec}
           (inst: LinSp TCoef TVec fi sumF mulF mulV sumV)
           (lCoef: List TCoef)
           (lVec: List TVec): TVec :=
match lCoef, lVec with
| List.nil, List.nil                 => inst.VZero
| (List.cons c lc), (List.cons v lv) => sumV (mulV c v) (linCombImp inst lc lv)
| (List.cons _ _), List.nil          => inst.VZero
| List.nil, (List.cons _ _)          => inst.VZero

-- linear combination
def linComb{TCoef TVec: Type}
           {fi: Set TCoef}
           {sumF: TCoef → TCoef → TCoef}
           {mulF: TCoef → TCoef → TCoef}
           {mulV: TCoef → TVec → TVec}
           {sumV: TVec → TVec → TVec}
           (inst: LinSp TCoef TVec fi sumF mulF mulV sumV)
           (lCoef: List TCoef)
           (lVec: List TVec)
           (_: length lCoef = length lVec)
           (_: listProp lCoef (fun c:TCoef => c∈fi)):
           TVec := linCombImp inst lCoef lVec

-- finite-dimension linear space
class LinSpFD(TCoef TVec: Type)
             (fi: Set TCoef)
             (sumF: TCoef → TCoef → TCoef)
             (mulF: TCoef → TCoef → TCoef)
             (mulV: TCoef → TVec → TVec)
             (sumV: TVec → TVec → TVec)
             extends base:LinSp TCoef TVec fi sumF mulF mulV sumV
             where
  Basis: List TVec
  ax1(aC: List TCoef)
     (p1: length aC = length Basis)
     (p2: listProp aC (fun c:TCoef => c∈fi)):
        linComb base aC Basis p1 p2 = VZero →
        listProp aC (fun c:TCoef => c=zero)
  ax2(v:TVec):
    ∃aC: List TCoef,
    ∃p1:length aC = length Basis,
    ∃p2:listProp aC (fun c:TCoef => c∈fi),
    @linComb TCoef TVec fi sumF mulF mulV sumV base aC Basis p1 p2 = v

theorem th(TCoef TVec: Type)
          (fi: Set TCoef)
          (sumF: TCoef → TCoef → TCoef)
          (mulF: TCoef → TCoef → TCoef)
          (mulV: TCoef → TVec → TVec)
          (sumV: TVec → TVec → TVec)
          (linSp: LinSpFD TCoef TVec fi sumF mulF mulV sumV)
          (aC1: List TCoef)
          (aC2: List TCoef)
          (pLen1: length aC1 = length linSp.Basis)
          (pIn1: listProp aC1 (fun c:TCoef => c∈fi))
          (pLen2: length aC2 = length linSp.Basis)
          (pIn2: listProp aC2 (fun c:TCoef => c∈fi))
          (eq: linComb linSp.base aC1 linSp.Basis pLen1 pIn1 = linComb linSp.base aC2 linSp.Basis pLen2 pIn2):
          aC1 = aC2 := by
  sorry
