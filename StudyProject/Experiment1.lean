import Mathlib.Data.Int.Basic

instance inss2:HAdd ℕ Bool ℕ :=
{
  hAdd(v: ℕ)(b: Bool): ℕ := if b then v+v+v else v
}

#eval 2+true
#eval 2+false
