import Mathlib.Data.Int.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Tactic.IntervalCases
import StudyProject.MyAbstractAlgebra.Definitions.Field

-- This file gives an example of field: Galua filed mod 5
namespace MY

def univers: Set ℤ := {0, 1, 2, 3, 4}

structure ElemGal where
val: ℤ
prop: val∈univers

def sumGal(a b: ElemGal): ElemGal :=
{
  val := (a.val+b.val)%5
  prop := by
    simp [univers]
    generalize repl:(a.val+b.val)%5=A
    omega
}

def mulGal(a b: ElemGal): ElemGal :=
{
  val := (a.val*b.val)%5
  prop := by
    simp [univers]
    generalize repl:(a.val+b.val)%5=A
    omega
}

def zeroGal:ElemGal :=
    {
      val := 0
      prop := by
        simp [univers]
    }

instance GaluaField: Field ElemGal :=
  {
    sum := sumGal
    mul := mulGal

    zero := zeroGal
    one :=
    {
      val := 1
      prop := by
        simp [univers]
    }

    sumComm := by
      intro a b
      simp [sumGal]
      omega
    sumAssoc := by
      simp [sumGal]
      omega
    zeroProp := by
      intro a
      simp [sumGal]
      have eq:a.val%5=a.val := by
        cases a.prop
        case inl => omega
        case inr pr => cases pr
                       case inl => omega
                       case inr pr2 => cases pr2
                                       case inl => omega
                                       case inr pr3 => cases pr3
                                                       case inl => omega
                                                       case inr pr4 => simp at pr4
                                                                       omega
      simp [eq, zeroGal]
    sumRev := by
      intro a
      exists
      {
        val := (5-a.val)%5
        prop := by
          simp [univers]
          cases a.prop
          case inl => aesop
          case inr pr => cases pr
                         case inl => aesop
                         case inr pr2 => cases pr2
                                         case inl => omega
                                         case inr pr3 => cases pr3
                                                         case inl => omega
                                                         case inr pr4 => simp at pr4
                                                                         omega
      }
      simp [sumGal, zeroGal]
    multComm := by
      simp [mulGal]
      intro a b
      rw [Int.mul_comm]
    multAssoc := by
      intro a b c
      simp [mulGal]
      cases a.prop
      case inl => aesop
      case inr h =>
        cases h
        case inl eq =>
          simp [eq]
          cases b.prop
          case inl => aesop
          case inr h =>
          cases h
          case inl => aesop
          case inr h =>
          cases h
          case inl => aesop
          case inr h =>
          cases h
          case inl => aesop
          case inr => aesop
        case inr h =>
          cases h
          case inl eq =>
            simp [eq]
            cases b.prop
            case inl => aesop
            case inr h =>
            cases h
            case inl h =>
              simp [h]
              omega
            case inr h =>
            cases h
            case inl h =>
              simp [h]
              omega
            case inr h =>
            cases h
            case inl h =>
              simp [h]
              omega
            case inr h =>
              simp at h
              simp [h]
              omega
          case inr eq =>
            cases eq
            case inl h =>
              simp [h]
              cases b.prop
              case inl => aesop
              case inr h =>
              cases h
              case inl h =>
                simp [h]
                omega
              case inr h =>
              cases h
              case inl h =>
                simp [h]
                omega
              case inr h =>
              cases h
              case inl h =>
                simp [h]
                omega
              case inr h =>
                simp at h
                simp [h]
                omega
            case inr h =>
              simp at h
              simp [h]
              cases b.prop
              case inl => aesop
              case inr h =>
              cases h
              case inl h =>
                simp [h]
                omega
              case inr h =>
              cases h
              case inl h =>
                simp [h]
                omega
              case inr h =>
              cases h
              case inl h =>
                simp [h]
                omega
              case inr h =>
                simp at h
                simp [h]
                omega
    oneProp := by
      simp [mulGal]
      intro a
      have eq:a.val%5=a.val := by
        cases a.prop
        case inl => omega
        case inr pr => cases pr
                       case inl => omega
                       case inr pr2 => cases pr2
                                       case inl => omega
                                       case inr pr3 => cases pr3
                                                       case inl => omega
                                                       case inr pr4 => simp at pr4
                                                                       omega
      simp [eq]
    MultInv := by
      intro a
      intro nz
      cases a.prop
      case inl h =>
        rw [zeroGal] at nz
        apply False.elim
        have eq:a = { val := 0, prop := zeroGal._proof_5 } := by
          clear nz
          cases a
          case mk z prz =>
            aesop
        aesop
      case inr pr => cases pr
                     case inl h =>
                       exists
                       {
                         val := 1
                         prop := by
                           simp [univers]
                       }
                       simp [h, mulGal]
                     case inr pr2 => cases pr2
                                     case inl h =>
                                       exists
                                       {
                                         val := 3
                                         prop := by
                                           simp [univers]
                                       }
                                       simp [h, mulGal]
                                     case inr pr3 => cases pr3
                                                     case inl h =>
                                                       exists
                                                       {
                                                         val := 2
                                                         prop := by
                                                           simp [univers]
                                                       }
                                                       simp [h, mulGal]
                                                     case inr pr4 =>
                                                       exists
                                                       {
                                                         val := 4
                                                         prop := by
                                                           simp [univers]
                                                       }
                                                       simp [pr4, mulGal]
                                                       simp at pr4
                                                       simp [pr4]
    multDistrLeft := by
      intro a b c
      simp [sumGal, mulGal]
      cases a.prop
      case inl h =>
        simp [h]
        cases b.prop
        case inl => aesop
        case inr h =>
        cases h
        case inl => aesop
        case inr h =>
        cases h
        case inl => aesop
        case inr h =>
        cases h
        case inl => aesop
        case inr => aesop
      case inr h =>
        cases h
        case inl eq =>
          simp [eq]
          cases b.prop
          case inl => aesop
          case inr h =>
          cases h
          case inl h =>
            simp [h]
            omega
          case inr h =>
          cases h
          case inl =>
            cases c.prop
            case inl => aesop
            case inr h =>
            cases h
            case inl => aesop
            case inr h =>
            cases h
            case inl => aesop
            case inr h =>
            cases h
            case inl => aesop
            case inr => aesop
          case inr h =>
          cases h
          case inl h =>
            simp [h]
            omega
          case inr h =>
            simp at h
            simp [h]
            omega
        case inr h =>
          cases h
          case inl eq =>
            simp [eq]
            cases b.prop
            case inl => aesop
            case inr h =>
            cases h
            case inl h =>
              simp [h]
              omega
            case inr h =>
            cases h
            case inl h =>
              simp [h]
              omega
            case inr h =>
            cases h
            case inl h =>
              simp [h]
              omega
            case inr h =>
              simp at h
              simp [h]
              omega
          case inr eq =>
            cases eq
            case inl h =>
              simp [h]
              cases b.prop
              case inl => aesop
              case inr h =>
              cases h
              case inl h =>
                simp [h]
                omega
              case inr h =>
              cases h
              case inl h =>
                simp [h]
                omega
              case inr h =>
              cases h
              case inl h =>
                simp [h]
                omega
              case inr h =>
                simp at h
                simp [h]
                omega
            case inr h =>
              simp at h
              simp [h]
              cases b.prop
              case inl => aesop
              case inr h =>
              cases h
              case inl h =>
                simp [h]
                omega
              case inr h =>
              cases h
              case inl h =>
                simp [h]
                omega
              case inr h =>
              cases h
              case inl h =>
                simp [h]
                omega
              case inr h =>
                simp at h
                simp [h]
                omega
    multDistrRight := by
      intro a b c
      simp [sumGal, mulGal]
      cases a.prop
      case inl h =>
        simp [h]
        cases b.prop
        case inl => aesop
        case inr h =>
        cases h
        case inl => aesop
        case inr h =>
        cases h
        case inl => aesop
        case inr h =>
        cases h
        case inl => aesop
        case inr => aesop
      case inr h =>
        cases h
        case inl eq =>
          simp [eq]
          cases b.prop
          case inl => aesop
          case inr h =>
          cases h
          case inl h =>
            simp [h]
            omega
          case inr h =>
          cases h
          case inl =>
            cases c.prop
            case inl => aesop
            case inr h =>
            cases h
            case inl => aesop
            case inr h =>
            cases h
            case inl => aesop
            case inr h =>
            cases h
            case inl => aesop
            case inr => aesop
          case inr h =>
          cases h
          case inl h =>
            simp [h]
            omega
          case inr h =>
            simp at h
            simp [h]
            omega
        case inr h =>
          cases h
          case inl eq =>
            simp [eq]
            cases b.prop
            case inl => aesop
            case inr h =>
            cases h
            case inl h =>
              simp [h]
              omega
            case inr h =>
            cases h
            case inl h =>
              simp [h]
              omega
            case inr h =>
            cases h
            case inl h =>
              simp [h]
              omega
            case inr h =>
              simp at h
              simp [h]
              omega
          case inr eq =>
            cases eq
            case inl h =>
              simp [h]
              cases b.prop
              case inl => aesop
              case inr h =>
              cases h
              case inl h =>
                simp [h]
                omega
              case inr h =>
              cases h
              case inl h =>
                simp [h]
                omega
              case inr h =>
              cases h
              case inl h =>
                simp [h]
                omega
              case inr h =>
                simp at h
                simp [h]
                omega
            case inr h =>
              simp at h
              simp [h]
              cases b.prop
              case inl => aesop
              case inr h =>
              cases h
              case inl h =>
                simp [h]
                omega
              case inr h =>
              cases h
              case inl h =>
                simp [h]
                omega
              case inr h =>
              cases h
              case inl h =>
                simp [h]
                omega
              case inr h =>
                simp at h
                simp [h]
                omega
  }
