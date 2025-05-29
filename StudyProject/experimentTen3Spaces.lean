import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Module.Defs
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Subalgebra
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Algebra.Module.Submodule.Bilinear
import StudyProject.StandardLinearAlgebra.definitions
import StudyProject.StandardLinearAlgebra.moduleFinite
import StudyProject.StandardLinearAlgebra.moduleInfinite
import StudyProject.StandardLinearAlgebra.linearMaps
import StudyProject.StandardLinearAlgebra.basis

open TensorProduct

-- A pair of integers
@[ext]
structure Coup where
f: ℤ
s: ℤ

-- prove tactic for module of pairs
macro "pr":tactic =>
`(tactic|(
  intros;
  simp [HAdd.hAdd, HSMul.hSMul, OfNat.ofNat];
  try all_goals simp [Zero.zero, Add.add, SMul.smul];
  try ext;
  try apply And.intro;
  all_goals simp [instAddNat, instMulNat, Int.instAdd, Int.instMul, OfNat.ofNat];
  all_goals ring
))

@[instance]
instance mon: AddCommMonoid Coup :=
{
  add(c1 c2: Coup):Coup := Coup.mk (c1.f+c2.f) (c1.s+c2.s)
  zero := Coup.mk 0 0
  add_assoc := by pr
  zero_add := by pr
  add_zero := by pr
  add_comm := by pr

  nsmul(n: ℕ)(c:Coup) := Coup.mk ((n:ℤ)*c.f) ((n:ℤ)*c.s)
  nsmul_zero := by pr
  nsmul_succ := by pr
}

@[instance]
instance mod: Module ℤ Coup :=
{
  smul(z:ℤ)(c: Coup) := Coup.mk (z*c.f) (z*c.s)
  one_smul := by pr
  mul_smul := by pr
  smul_zero := by pr
  smul_add := by pr
  add_smul := by pr
  zero_smul := by pr
}

-- Here we start the purpose of this file
-- triple is a "Tensor cube" of Coup
@[reducible]
def triple:Type := (Coup ⊗[ℤ] Coup) ⊗[ℤ] Coup

-- helper macro
macro "proveTP":tactic =>
`(tactic|(
  try apply TensorProduct.tmul_add
  try apply TensorProduct.tmul_smul
  try apply TensorProduct.smul_tmul
  try apply TensorProduct.smul_tmul'
  try apply TensorProduct.add_tmul
))

-- FUNCTION PURPOSE
-- This function is a core of the transformation.
-- In fact this function defines transformation of triple instances.
-- However it defines it explicitly only for pure states: c₁⊗c₂⊗c₃.
-- This funcition is later lifted to define transformation for entangled states.
--
-- HOW THIS PARTICULAR INSTANCE WORKS
-- This particular instance takes the following parameters:
-- n: number of element unit transformation should be applied to (c₁ or c₂ or c₃)
-- tr: unit transformation
-- x: first element
-- y: second element
-- z: third element
noncomputable
def core(n: ℕ)
        (tr: Coup →ₗ[ℤ] Coup)
        (x: Coup)
        (y: Coup)
        (z:Coup):
        triple :=
if (n=1) then TensorProduct.tmul ℤ
                                 (TensorProduct.tmul ℤ (tr x) y)
                                 z
else if (n=2) then TensorProduct.tmul ℤ
                                      (TensorProduct.tmul ℤ x (tr y))
                                      z
else if (n=3) then TensorProduct.tmul ℤ
                                      (TensorProduct.tmul ℤ x y)
                                      (tr z)
else TensorProduct.tmul ℤ
                        (TensorProduct.tmul ℤ x y)
                        z

-- Just a helper lemma. It allows to divide an arbitrary case into:
-- n=1
-- n=2
-- n=3
-- other
lemma help(n:ℕ)(A:Prop):
((n=1)→A) →
((n=2)→A) →
((n=3)→A) →
(¬(n=1)→¬(n=2)→¬(n=3)→A) →
A := by
  intro c1 c2 c3 cn
  cases n
  case zero=>aesop
  case succ m => cases m
                 case zero => aesop
                 case succ k => cases k
                                case zero => aesop
                                case succ r => cases r
                                               case zero => aesop
                                               case succ f => aesop

-- Here we start transforming core into linear map to linear map...
-- This is the first step: we eliminate the first parameter of core
noncomputable
def coreLin1(n: ℕ)
            (sw: Coup →ₗ[ℤ] Coup)
            (x y: Coup):
            Coup →ₗ[ℤ] triple :=
{
  toFun(z:Coup) := core n sw x y z
  map_add' := by
    simp [core]
    apply help n
    {
      intro eq
      simp [eq]
      intro x1 y1
      proveTP
    }
    {
      intro eq
      simp [eq]
      intro x1 y1
      proveTP
    }
    {
      intro eq
      simp [eq]
      intro x1 y1
      proveTP
    }
    {
      intro eq1 eq2 eq3
      simp [eq1, eq2, eq3]
      intro x1 y1
      proveTP
    }
  map_smul' := by
    simp [core]
}

macro "unfoldTensorPrSum":tactic =>
`(tactic|(
  try rw [TensorProduct.tmul_add];
  try rw [TensorProduct.add_tmul];
  try rw [TensorProduct.tmul_add];
  try rw [TensorProduct.add_tmul];
  try rw [TensorProduct.tmul_add];
  try rw [TensorProduct.add_tmul];
  try rw [TensorProduct.tmul_add];
  try rw [TensorProduct.add_tmul];
  try rw [TensorProduct.tmul_add];
  try rw [TensorProduct.add_tmul];
  try rw [TensorProduct.tmul_add];
  try rw [TensorProduct.add_tmul];
  try rw [TensorProduct.tmul_add];
  try rw [TensorProduct.add_tmul];
  try rw [TensorProduct.tmul_add];
  try rw [TensorProduct.add_tmul];
  try rw [TensorProduct.tmul_add];
  try rw [TensorProduct.add_tmul];
  try rw [TensorProduct.tmul_add];
  try rw [TensorProduct.add_tmul]
))

macro "extractSc":tactic =>
`(tactic|(
  try apply TensorProduct.tmul_smul;
  try apply TensorProduct.smul_tmul;
  try apply TensorProduct.tmul_smul;
  try apply TensorProduct.smul_tmul;
  try apply TensorProduct.tmul_smul;
  try apply TensorProduct.smul_tmul;
  try apply TensorProduct.tmul_smul;
  try apply TensorProduct.smul_tmul;
  try apply TensorProduct.tmul_smul;
  try apply TensorProduct.smul_tmul;
  try apply TensorProduct.tmul_smul;
  try apply TensorProduct.smul_tmul;
  try apply TensorProduct.tmul_smul;
  try apply TensorProduct.smul_tmul
))

-- Here we continue transforming core into linea map.
-- Here we eliminate the second parameter of core.
noncomputable
def coreLin2(n: ℕ)
            (sw: Coup →ₗ[ℤ] Coup)
            (x: Coup):
            Coup →ₗ[ℤ] (Coup →ₗ[ℤ] triple) :=
{
  toFun(y:Coup) := coreLin1 n sw x y
  map_add' := by
    intro x1 y1
    ext g
    simp [coreLin1]
    simp [core]
    unfoldTensorPrSum
    apply help n
    all_goals aesop
  map_smul' := by
    intro x1 y1
    ext g
    simp [coreLin1]
    simp [core]
    apply help n
    all_goals aesop
}

-- Here we transformed code into linear map
-- However this map is: core + some its properties proven
-- In other words this map still works only with c₁⊗c₂⊗c₃ and can't work with arbitrary triple
noncomputable
def coreLin3(n: ℕ)
            (sw: Coup →ₗ[ℤ] Coup):
            Coup →ₗ[ℤ] (
                      Coup →ₗ[ℤ] (
                                 Coup →ₗ[ℤ] triple
                                 )
                      ) :=
{
  toFun(c:Coup) := coreLin2 n sw c
  map_add' := by
    intro x1 y1
    ext g
    simp [coreLin1, coreLin2]
    simp [core]
    unfoldTensorPrSum
    apply help n
    all_goals aesop
  map_smul' := by
    intro x1 y1
    ext g
    simp [coreLin1, coreLin2]
    simp [core]
    apply help n
    all_goals aesop
}

-- Here we start lifting core to space of all triples.
-- Here we lift it from acting on c₁⊗c₂⊗c₃ to acting on c₁₂⊗c₃
noncomputable
def coreLift1(n: ℕ)
             (sw: Coup →ₗ[ℤ] Coup): (Coup ⊗[ℤ] Coup) →ₗ[ℤ] (Coup →ₗ[ℤ] triple) :=
TensorProduct.lift (coreLin3 n sw)

-- Final: Core lifted to c₁₂₃
noncomputable
def final(n:ℕ)(sw: Coup →ₗ[ℤ] Coup): triple →ₗ[ℤ] triple := TensorProduct.lift (coreLift1 n sw)

-- Here we are having an example to make sure the abovementioned functionality works as expected

-- transformation
def swap: Coup →ₗ[ℤ] Coup :=
{
  toFun(c:Coup) := Coup.mk c.s c.f
  map_add' := by pr
  map_smul' := by pr
}

-- triple examples
noncomputable
def ex1:triple := TensorProduct.tmul ℤ (TensorProduct.tmul ℤ (Coup.mk 1 2) (Coup.mk 3 4)) (Coup.mk 5 6)
noncomputable
def ex2:triple := TensorProduct.tmul ℤ (TensorProduct.tmul ℤ (Coup.mk 10 20) (Coup.mk 30 40)) (Coup.mk 50 60)

-- first test theorem to make sure that final works as expected
theorem test1:final 1 swap ex1 = TensorProduct.tmul ℤ (TensorProduct.tmul ℤ (Coup.mk 2 1) (Coup.mk 3 4)) (Coup.mk 5 6) := by
  simp [ex1]
  simp [final]
  simp [coreLift1]
  simp [coreLin3, coreLin2, coreLin1]
  simp [core]
  simp [swap]

theorem test2:final 2 swap ex1 = TensorProduct.tmul ℤ (TensorProduct.tmul ℤ (Coup.mk 1 2) (Coup.mk 4 3)) (Coup.mk 5 6) := by
  simp [ex1]
  simp [final]
  simp [coreLift1]
  simp [coreLin3, coreLin2, coreLin1]
  simp [core]
  simp [swap]

theorem test3:final 2 swap (ex1+ex2) =
            TensorProduct.tmul ℤ (TensorProduct.tmul ℤ (Coup.mk 1 2) (Coup.mk 4 3)) (Coup.mk 5 6) +
            TensorProduct.tmul ℤ (TensorProduct.tmul ℤ (Coup.mk 10 20) (Coup.mk 40 30)) (Coup.mk 50 60) := by
  have eq: final 2 swap (ex1+ex2) = (final 2 swap ex1) + (final 2 swap ex2) := by
    aesop
  rw [eq]
  clear eq

  simp [ex1, ex2]
  simp [final]
  simp [coreLift1]
  simp [coreLin3, coreLin2, coreLin1]
  simp [core]
  simp [swap]

theorem test4:final 3 swap ex1 = TensorProduct.tmul ℤ (TensorProduct.tmul ℤ (Coup.mk 1 2) (Coup.mk 3 4)) (Coup.mk 6 5) := by
  simp [ex1]
  simp [final]
  simp [coreLift1]
  simp [coreLin3, coreLin2, coreLin1]
  simp [core]
  simp [swap]
