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
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Algebra.Module.Submodule.Bilinear
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.Data.Matrix.Kronecker

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

def Z(n:ℕ):ℤ:=n

instance jkl(N: ℕ): AddCommMonoid (SeqFin N →ₗ[ℤ] SeqFin N) :=
{
  add(l1 l2: (SeqFin N →ₗ[ℤ] SeqFin N)):(SeqFin N →ₗ[ℤ] SeqFin N):=
  {
    toFun(s: SeqFin N):SeqFin N := (l1 s) + (l2 s)
    map_add' := by
      intro x y
      have eq1: l1 (x+y)=l1 x + l1 y := by
        aesop
      have eq2: l2 (x+y)=l2 x + l2 y := by
        aesop
      rw [eq1, eq2]
      generalize replA: l1 x = A
      generalize replB: l1 y = B
      generalize replC: l2 x = C
      generalize replD: l2 y = D
      clear replA replB replC replD eq1 eq2 l1 l2
      module
    map_smul' := by
      intro m x
      have eq1:l1 (m • x) = m • (l1 x) := by
        aesop
      have eq2:l2 (m • x) = m • (l2 x) := by
        aesop
      have eq3:(RingHom.id ℤ) m • (l1 x + l2 x) = m • (l1 x) + m • (l2 x) := by
        aesop
      rw [eq1, eq2, eq3]
  }
  add_comm := by
    intro a b
    ext s
    simp [HAdd.hAdd]
    generalize replA:a s=A
    generalize replB:b s=B
    clear a b s replA replB
    simp [Add.add]
    funext n
    ring
  add_assoc := by
    intro a b c
    ext s
    simp [HAdd.hAdd]
    generalize replA:a s=A
    generalize replB:b s=B
    generalize replC:c s=C
    clear a b c s replA replB replC
    simp [Add.add]
    funext n
    ring
  zero :=
  {
    toFun(s: SeqFin N):SeqFin N := (fun n: Fin N => 0)
    map_add' := by
      intro x y
      aesop
    map_smul' := by
      intro m
      intro x
      funext n
      simp [HSMul.hSMul]
      simp [SMul.smul]
  }
  zero_add := by
    intro a
    ext s
    simp [HAdd.hAdd]
    simp [Add.add]
    funext n
    simp [Zero.zero]
    aesop
  add_zero := by
    intro a
    ext s
    simp [HAdd.hAdd]
    simp [Add.add]
    funext n
    simp [Zero.zero]
    aesop

  nsmul(n:ℕ)(lm: (SeqFin N →ₗ[ℤ] SeqFin N)):(SeqFin N →ₗ[ℤ] SeqFin N) :=
  {
    toFun(s: SeqFin N) := (Z n)•(lm s)
    map_add' := by
      aesop
    map_smul' := by
      intro m
      intro x
      have eq: lm (m • x) = m • (lm x) := by
        aesop
      rw [eq]
      module
  }
  nsmul_zero := by
    intro leftMul
    simp [HSMul.hSMul]
    simp [SMul.smul]
    ext argument
    simp
    funext n
    rw [Zero.toOfNat0]
    simp [Z]
    aesop
  nsmul_succ := by
    intro n
    intro leftMul
    simp [HSMul.hSMul]
    simp [SMul.smul]
    ext argument
    simp
    funext x
    simp [Z]
    simp [HAdd.hAdd]
    simp [Add.add]
    ring
}

open TensorProduct

def pair:Type:=(SeqFin 2) ⊗[ℤ] (SeqFin 2)
#synth Module ℤ ((SeqFin 2) ⊗[ℤ] (SeqFin 2))
#synth CommSemiring ℤ
#check instModule
#check @instModule
#check @instModule ℤ Int.instCommSemiring (SeqFin 2) (SeqFin 2)
#synth AddCommMonoid (SeqFin 2)
#synth Module ℤ (SeqFin 2)
#check @instModule ℤ Int.instCommSemiring (SeqFin 2) (SeqFin 2) (GroupFinite 2) (GroupFinite 2) (ModuleFinite 2) (ModuleFinite 2)

noncomputable
def resT:=@instModule ℤ Int.instCommSemiring (SeqFin 2) (SeqFin 2) (GroupFinite 2) (GroupFinite 2) (ModuleFinite 2) (ModuleFinite 2)
#check resT
#check resT.smul

def simp:Type:=ℤ ⊗[ℤ] ℤ

def sumZero(N: ℕ)(seq: SeqFin N) := (∑ i:Fin N, seq i) = 0

def f(N: ℕ): Submodule ℤ (SeqFin N) :=
{
  carrier := {seq: SeqFin N | sumZero N seq}
  add_mem' := by
    intro a b
    intro A B
    simp at A
    simp at B
    simp
    simp [sumZero] at A B
    simp [sumZero]
    simp [HAdd.hAdd]
    simp [Add.add]
    have eq: ∑ x, (a x + b x) = ∑ x, a x + ∑ x, b x := by
      clear A B
      simp [SeqFin] at a b
      apply Finset.sum_add_distrib
    rw [eq]
    rw [A, B]
    simp
  zero_mem' := by
    simp [sumZero]
    simp [OfNat.ofNat]
    simp [Zero.zero]
  smul_mem' := by
    intro c x
    simp
    intro CX
    simp [sumZero] at CX
    simp [sumZero]
    simp [HSMul.hSMul]
    simp [SMul.smul]
    have eq: ∑ i, x i * c = c * ∑ i, x i := by
      simp [Finset.mul_sum]
      apply Finset.sum_congr
      simp
      intro i
      intro I
      generalize repl:x i = XI
      simp [Int.mul_comm]
    rw [eq]
    rw [CX]
    simp
}

#check Basis
#check @Basis.mk
#synth Semiring ℤ
noncomputable
def rl(N: ℕ):Basis (Fin N) ℤ (SeqFin N) :=
@Basis.mk (Fin N)
          ℤ
          (SeqFin N)
          Int.instSemiring
          (GroupFinite N)
          (ModuleFinite N)
          (fun i:Fin N => (fun x: Fin N => if(x==i) then 1 else 0))
          (by
            simp [LinearIndependent]
            simp [Finsupp.linearCombination]
            simp [Function.Injective]
            intro a₁ a₂
            simp [HSMul.hSMul]
            simp [SMul.smul]
            simp [Finsupp.sum]
            intro A
            rw [Finset.sum] at A
            rw [Finset.sum] at A
            generalize s1:(∑ x ∈ a₁.support, fun n => if n = x then a₁ x else 0) = Seq1
            simp [SeqFin] at A
            #check congr_fun
            #check congr_fun A
            let AA := congr_fun A
            #check congr_arg
            simp at AA
            have eq: ∀a:Fin N →₀ ℤ,
                     ∀k:Fin N,
                     a k = (∑ x ∈ a.support, fun n => if n = x then a x else 0) k := by
                     simp
                     aesop
            apply Finsupp.ext
            intro aaa
            rw [eq a₁]
            rw [eq a₂]
            apply AA aaa
          )
          (by
            simp [LE.le]
            intro x
            simp [Submodule.span]
            intro p
            simp [Set.range]
            sorry
          )

#check LinearMap.toMatrix
#check Matrix.toLin

def mult(N: ℕ)(m: SeqFin N): SeqFin N →ₗ[ℤ] SeqFin N :=
{
  toFun: SeqFin N → SeqFin N
  | s1 => (fun n:Fin N => (s1 n)*(m n))
  map_add' := by
    intro x y
    simp
    funext n
    simp [HAdd.hAdd]
    simp [Add.add]
    generalize repl1: x n = XN
    generalize repl2: y n = YN
    generalize repl3: m n = MN
    ring
  map_smul' := by
    intro x
    simp
    intro s
    funext n
    simp [HSMul.hSMul]
    simp [SMul.smul]
    generalize repl1: m n = MN
    generalize repl2: s n = SN
    ring
}

#check LinearMap.toMatrix (rl 5) (rl 5) (mult 5 (fun n:Fin 5 => n))
noncomputable
def mat:=LinearMap.toMatrix (rl 5) (rl 5) (mult 5 (fun n:Fin 5 => n))
#check mat
#check mat 1 1

#check Matrix.toLin (rl 3) (rl 3)
noncomputable
def op := Matrix.toLin (rl 3) (rl 3) !![1, 2, 1; 1, 2, 1; 1, 2, 1]
