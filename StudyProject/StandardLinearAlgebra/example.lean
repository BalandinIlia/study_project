import Mathlib.Data.Int.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Field.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Basis.Submodule
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Algebra.Module.Defs
import Mathlib.Data.Fin.Basic
import Mathlib.LinearAlgebra.DirectSum.Basis
import Mathlib.LinearAlgebra.Matrix.Basis

def SeqInf:Type := ℕ → ℤ

def SeqFin(N: ℕ):Type := (Fin N) → ℤ

instance GroupInfinite:AddCommMonoid SeqInf :=
{
  add: SeqInf → SeqInf → SeqInf
  | f1, f2 => fun n:ℕ => (f1 n) + (f2 n)
  add_assoc := by
    simp [HAdd.hAdd]
    simp [Add.add]
    intro a b c
    funext n
    omega
  zero := fun n:ℕ => 0
  zero_add := by
    simp [HAdd.hAdd]
    simp [Add.add]
    intro a
    funext n
    simp [OfNat.ofNat]
  add_zero := by
    simp [HAdd.hAdd]
    simp [Add.add]
    intro a
    funext n
    simp [OfNat.ofNat]
  add_comm := by
    simp [HAdd.hAdd]
    simp [Add.add]
    intro a b
    funext n
    omega

  nsmul: ℕ → SeqInf → SeqInf
  | m, f => fun n:ℕ => (f n) * m
  nsmul_zero := by
    simp
    intro x
    funext n
    simp [OfNat.ofNat]
  nsmul_succ := by
    simp
    intro n x
    funext m
    simp [Nat.cast]
    simp [HAdd.hAdd]
    simp [Add.add]
    generalize repl: x m = A
    simp [OfNat.ofNat]
    simp [One.one]
    simp [NatCast.natCast]
    simp [Nat.cast]
    rw [Int.mul_add]
    omega
}

instance GroupFinite(N: ℕ):AddCommMonoid (SeqFin N) :=
{
  add: (SeqFin N) → (SeqFin N) → (SeqFin N)
  | f1, f2 => fun n:(Fin N) => (f1 n) + (f2 n)
  add_assoc := by
    simp [HAdd.hAdd]
    simp [Add.add]
    intro a b c
    funext n
    omega
  zero := fun n:Fin N => 0
  zero_add := by
    simp [HAdd.hAdd]
    simp [Add.add]
    intro a
    funext n
    simp [OfNat.ofNat]
  add_zero := by
    simp [HAdd.hAdd]
    simp [Add.add]
    intro a
    funext n
    simp [OfNat.ofNat]
  add_comm := by
    simp [HAdd.hAdd]
    simp [Add.add]
    intro a b
    funext n
    omega

  nsmul: ℕ → (SeqFin N) → (SeqFin N)
  | m, f => fun n:Fin N => (f n) * m
  nsmul_zero := by
    simp
    intro x
    funext n
    simp [OfNat.ofNat]
  nsmul_succ := by
    simp
    intro n x
    funext m
    simp [Nat.cast]
    simp [HAdd.hAdd]
    simp [Add.add]
    generalize repl: x m = A
    simp [OfNat.ofNat]
    simp [One.one]
    simp [NatCast.natCast]
    simp [Nat.cast]
    rw [Int.mul_add]
    omega
}

instance ModuleInfinite: Module ℤ SeqInf :=
{
  smul(z: ℤ)(f: SeqInf) := fun n:ℕ => (f n) * z
  one_smul := by
    simp [HSMul.hSMul]
  smul_zero := by
    simp [HSMul.hSMul]
    simp [OfNat.ofNat]
    simp [Zero.zero]
  smul_add := by
    simp [HSMul.hSMul]
    intro a x y
    funext n
    simp [HAdd.hAdd]
    simp [Add.add]
    generalize r1: x n = X
    generalize r2: y n = Y
    rw [Int.add_mul X Y a]
  add_smul := by
    simp [HSMul.hSMul]
    intro a x y
    funext n
    simp [HAdd.hAdd]
    simp [Add.add]
    generalize r2: y n = Y
    rw [Int.mul_add]
  zero_smul := by
    simp [HSMul.hSMul]
    simp [OfNat.ofNat]
    simp [Zero.zero]
  mul_smul := by
    simp [HSMul.hSMul]
    intro a x y
    funext n
    generalize r2: y n = Y
    rw [Int.mul_comm a x]
    rw [Int.mul_assoc]
}

instance ModuleFinite(N: ℕ): Module ℤ (SeqFin N) :=
{
  smul(z: ℤ)(f: SeqFin N) := fun n:Fin N => (f n) * z
  one_smul := by
    simp [HSMul.hSMul]
  smul_zero := by
    simp [HSMul.hSMul]
    simp [OfNat.ofNat]
    simp [Zero.zero]
  smul_add := by
    simp [HSMul.hSMul]
    intro a x y
    funext n
    simp [HAdd.hAdd]
    simp [Add.add]
    generalize r1: x n = X
    generalize r2: y n = Y
    rw [Int.add_mul X Y a]
  add_smul := by
    simp [HSMul.hSMul]
    intro a x y
    funext n
    simp [HAdd.hAdd]
    simp [Add.add]
    generalize r2: y n = Y
    rw [Int.mul_add]
  zero_smul := by
    simp [HSMul.hSMul]
    simp [OfNat.ofNat]
    simp [Zero.zero]
  mul_smul := by
    simp [HSMul.hSMul]
    intro a x y
    funext n
    generalize r2: y n = Y
    rw [Int.mul_comm a x]
    rw [Int.mul_assoc]
}

def cut(N: ℕ): SeqInf →ₗ[ℤ] SeqFin N :=
{
  toFun(s:SeqInf):SeqFin N := fun n:Fin N => s n
  map_add' := by
    intro x y
    funext n
    simp [HAdd.hAdd]
    simp [Add.add]
  map_smul' := by
    intro x y
    funext n
    simp [HAdd.hAdd, HSMul.hSMul, SMul.smul]
}

lemma Var(A B: Prop): (A→B) → ((¬A)→B) → B := by
  intro h1 h2
  have helper:(A∨(¬A))→B:= by
    aesop
  apply helper
  clear h1 h2 helper B
  by_contra
  aesop
#print axioms Var

def extend{N: ℕ}: SeqFin N →ₗ[ℤ] SeqInf :=
{
  toFun(s:SeqFin N):SeqInf :=
    fun n:ℕ => if eq:n<N then s (Fin.mk n eq)
                         else 0
  map_add' := by
    intro x y
    funext n
    apply Var (n<N)
    {
      intro neq
      simp [neq]
      simp [HAdd.hAdd, HSMul.hSMul, SMul.smul]
      simp [Add.add]
      have eq1:x ⟨n, neq⟩=(if eq : n < N then x ⟨n, eq⟩ else 0) := by
        aesop
      rw [eq1]
      aesop
    }
    {
      intro neq
      simp [neq]
      simp [HAdd.hAdd, HSMul.hSMul, SMul.smul]
      simp [Add.add]
      have eq1:0=(if eq : n < N then x ⟨n, eq⟩ else 0) := by
        simp [neq]
      have eq2:0=(if eq : n < N then y ⟨n, eq⟩ else 0) := by
        simp [neq]
      generalize repl1:(if eq : n < N then x ⟨n, eq⟩ else 0)=A
      generalize repl2:(if eq : n < N then y ⟨n, eq⟩ else 0)=B
      rw [repl1] at eq1
      rw [repl2] at eq2
      clear repl1 repl2 N x y neq n
      aesop
    }
  map_smul' := by
    intro x y
    funext n
    simp [HAdd.hAdd, HSMul.hSMul, SMul.smul]
}

def I:SeqInf := fun n:ℕ => n

def ICut:SeqInf := extend ((cut 5) I)

#eval I 2
#eval ICut 2
#eval I 20
#eval ICut 20

--instance jkl(N: ℕ): AddCommMonoid (SeqFin N →ₗ[ℤ] SeqFin N) :=
--{
--  add(l1 l2: (SeqFin N →ₗ[ℤ] SeqFin N)):(SeqFin N →ₗ[ℤ] SeqFin N):=
--  {
--    toFun(s: SeqFin N):SeqFin N := (l1 s) + (l2 s)
--    map_add' := by
--      intro x y
--      have eq1: l1 (x+y)=l1 x + l1 y := by
--        aesop
--      have eq2: l2 (x+y)=l2 x + l2 y := by
--        aesop
--      rw [eq1, eq2]
--      generalize replA: l1 x = A
--      generalize replB: l1 y = B
--      generalize replC: l2 x = C
--      generalize replD: l2 y = D
--      clear replA replB replC replD eq1 eq2 l1 l2
--      module
--    map_smul' := by
--      intro m x
--      have eq1:l1 (m • x) = m • (l1 x) := by
--        aesop
--      have eq2:l2 (m • x) = m • (l2 x) := by
--        aesop
--      have eq3:(RingHom.id ℤ) m • (l1 x + l2 x) = m • (l1 x) + m • (l2 x) := by
--        aesop
--      rw [eq1, eq2, eq3]
--  }
--  add_comm := by
--    sorry
--  add_assoc := by
--    sorry
--  zero_add := by
--    sorry
--  add_zero := by
--    sorry
--}
