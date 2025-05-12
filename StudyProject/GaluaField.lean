import Mathlib.Data.Int.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Tactic.IntervalCases
import StudyProject.Field

-- This file gives an example of field: Galua filed mod 5
namespace MY

def set5: Set ℤ := {0, 1, 2, 3, 4}

def sum5(s1: ℤ)(s2: ℤ) := (s1+s2)%5

lemma summ5(s1: ℤ)(s2: ℤ) : (sum5 s1 s2)∈set5 := by
  generalize repl: sum5 s1 s2 = A
  rw [Eq.comm] at repl
  have neq1: A < 5 := by
    simp [sum5] at repl
    rw [repl]
    omega
  have neq2: A ≥ 0 := by
    simp [sum5] at repl
    rw [repl]
    omega
  clear s1 s2 repl
  have trans(g: ℤ): g≥0 → g<5 → g∈set5 := by
    clear A neq1 neq2
    simp [set5]
    intro h1 h2
    interval_cases g
    aesop
    aesop
    aesop
    aesop
    aesop
  apply trans
  aesop
  clear trans neq2
  aesop

def mul5(s1: ℤ)(s2: ℤ) := (s1*s2)%5

lemma mull5(s1: ℤ)(s2: ℤ) : (mul5 s1 s2)∈set5 := by
  generalize repl: mul5 s1 s2 = A
  rw [Eq.comm] at repl
  have neq1: A < 5 := by
    simp [mul5] at repl
    rw [repl]
    omega
  have neq2: A ≥ 0 := by
    simp [mul5] at repl
    rw [repl]
    omega
  clear s1 s2 repl
  have trans(g: ℤ): g≥0 → g<5 → g∈set5 := by
    clear A neq1 neq2
    simp [set5]
    intro h1 h2
    interval_cases g
    aesop
    aesop
    aesop
    aesop
    aesop
  apply trans
  aesop
  clear trans neq2
  aesop

instance Gal: Field ℤ set5 sum5 mul5 :=
  {
    zero := 0
    one := 1
    sumDef := by
      intro a b
      intro aIn bIn
      apply summ5
    mulDef := by
      intro a b
      intro aIn bIn
      simp [set5] at aIn bIn
      apply mull5
    sumComm := by
      intro a b
      intro aIn bIn
      simp [sum5]
      omega
    sumAssoc := by
      simp [sum5]
      omega
    zeroEx := by
      simp [set5]
    zeroProp := by
      intro a
      simp [set5]
      simp [sum5]
      intro aIn
      cases aIn
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
    sumRev := by
      simp [set5, sum5]
    multComm := by
      simp [mul5]
      intro a b aIn bIn
      rw [Int.mul_comm]
    multAssoc := by
      intro a b c aIn bIn cIn
      simp [mul5]
      cases aIn
      case inl => aesop
      case inr h =>
        cases h
        case inl eq =>
          simp [eq]
          cases bIn
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
            cases bIn
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
              cases bIn
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
              cases bIn
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
    oneEx := by
      simp [set5]
    oneProp := by
      simp [mul5, set5]
    mulRev := by
      simp [set5]
      simp [mul5]
    multDistr := by
      intro a b c aIn bIn cIn
      simp [sum5, mul5]
      cases aIn
      case inl h =>
        simp [h]
        cases bIn
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
          cases bIn
          case inl => aesop
          case inr h =>
          cases h
          case inl h =>
            simp [h]
            omega
          case inr h =>
          cases h
          case inl =>
            cases cIn
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
            cases bIn
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
              cases bIn
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
              cases bIn
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
