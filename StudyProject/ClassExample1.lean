import Mathlib.Data.Int.Basic

class exm (func: ℤ → ℤ) (val: ℤ) where
  arg: ℤ
  prop: func arg = val

theorem gh(v: ℤ)(f: ℤ→ℤ)[df: exm f v]:
  ∃g:ℤ, f g = v := by
  exists df.arg
  simp [df.prop]

instance ins1 : exm (fun x:ℤ => x*x) 4 :=
{
  arg := 2
  prop := by
    simp
}

instance ins2 : exm (fun x:ℤ => x*x) 4 :=
{
  arg := -2
  prop := by
    simp
}

theorem ghi: ∃g:ℤ, g*g=4 := by
  apply @gh 4 (fun x:ℤ => x*x) ins1
