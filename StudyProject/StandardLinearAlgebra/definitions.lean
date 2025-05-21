import Mathlib.Data.Int.Basic

-- Infinite sequence of integer numbers
def SeqInf:Type := ℕ → ℤ

-- Finite sequence of integer numbers
def SeqFin(N: ℕ):Type := (Fin N) → ℤ
