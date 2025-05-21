import Mathlib.Data.Int.Basic

-- Infinite sequence of integer numbers
-- Technically this is one type
def SeqInf:Type := ℕ → ℤ

-- Finite sequence of integer numbers
-- Technically this is countable set of types
-- (set of types isomorphic to natural numbers)
def SeqFin(N: ℕ):Type := (Fin N) → ℤ
#check SeqFin
