import Mathlib.Data.Int.Basic
import Mathlib.Data.Set.Basic
import StudyProject.MyAbstractAlgebra.Definitions.Ring
import StudyProject.MyAbstractAlgebra.Definitions.RingComOne
import StudyProject.MyAbstractAlgebra.Examples.GaluaField
import StudyProject.MyAbstractAlgebra.Definitions.Field

namespace MY

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
           (mulV: TCoef → TVec → TVec)
           (sumV: TVec → TVec → TVec)
           extends f:Field TCoef
           where
  -- basic axioms
  VZero: TVec
  VSumComm: ∀v1 v2: TVec, sumV v1 v2 = sumV v2 v1
  VSumAssoc: ∀v1 v2 v3: TVec, sumV (sumV v1 v2) v3 = sumV v1 (sumV v2 v3)
  VMultLin: ∀v1 v2: TVec, ∀c: TCoef, mulV c (sumV v1 v2) = sumV (mulV c v1) (mulV c v2)
  VMultZero: ∀v: TVec, mulV zero v = VZero
  VMultOne: ∀v: TVec, mulV one v = v
  VMultVZero: ∀v: TVec, sumV VZero v = v

-- linear combination
def linCombImp{TCoef TVec: Type}
           {mulV: TCoef → TVec → TVec}
           {sumV: TVec → TVec → TVec}
           (inst: LinSp TCoef TVec mulV sumV)
           (lCoef: List TCoef)
           (lVec: List TVec): TVec :=
match lCoef, lVec with
| List.nil, List.nil                 => inst.VZero
| (List.cons c lc), (List.cons v lv) => sumV (mulV c v) (linCombImp inst lc lv)
| (List.cons _ _), List.nil          => inst.VZero
| List.nil, (List.cons _ _)          => inst.VZero

-- linear combination
def linComb{TCoef TVec: Type}
           {mulV: TCoef → TVec → TVec}
           {sumV: TVec → TVec → TVec}
           (inst: LinSp TCoef TVec mulV sumV)
           (lCoef: List TCoef)
           (lVec: List TVec)
           (_: length lCoef = length lVec):
           TVec := linCombImp inst lCoef lVec

-- finite-dimension linear space
class LinSpFD(TCoef TVec: Type)
             (mulV: TCoef → TVec → TVec)
             (sumV: TVec → TVec → TVec)
             extends base:LinSp TCoef TVec mulV sumV
             where
  Basis: List TVec
  ax1(aC: List TCoef)
     (p1: length aC = length Basis):
        linComb base aC Basis p1 = VZero →
        listProp aC (fun c:TCoef => c=zero)
  ax2(v:TVec):
    ∃aC: List TCoef,
    ∃p1:length aC = length Basis,
    @linComb TCoef TVec mulV sumV base aC Basis p1 = v

theorem tq(TCoef TVec: Type)
          (mulV: TCoef → TVec → TVec)
          (sumV: TVec → TVec → TVec)
          (linSp: LinSpFD TCoef TVec mulV sumV)
          (aC1: List TCoef)
          (aC2: List TCoef)
          (pLen1: length aC1 = length linSp.Basis)
          (pLen2: length aC2 = length linSp.Basis)
          (eq: linComb linSp.base aC1 linSp.Basis pLen1 = linComb linSp.base aC2 linSp.Basis pLen2):
          aC1 = aC2 := by
  generalize repl1: linComb linSp.base aC1 linSp.Basis pLen1 = lc1
  generalize repl2: linComb linSp.base aC2 linSp.Basis pLen2 = lc2
  sorry
