import Mathlib.Data.Int.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Algebra.Module.Defs
import Mathlib.Data.Set.Basic
import Mathlib.Data.Quot
import Mathlib.Algebra.Module.Submodule.Basic
import StudyProject.StandardLinearAlgebra.definitions
import StudyProject.StandardLinearAlgebra.moduleInfinite

namespace myFactor

-- This is binder between two infinite sequences.
-- This binder is the base for quotient type.
def binded(s₁ s₂: SeqInf): Prop := ∀n:ℕ, n > 5 → s₁ n = s₂ n

-- Quotient type. Each instance of this type is a set of infinite sequences.
@[reducible]
def pr:Type := Quot binded

-- This function sums given infinite sequence s to given set of binded sequences
def sumImpl(s: SeqInf): pr → pr :=
-- We use lifting: we take function which take SeqInf and lift it to function which takes pr.
-- However we can't just do it. We need to prove that for any pr instance function result will exist.
-- In other words we need to prove that result is the same for any two sequences belonging to the same pr instance.
Quot.lift
(f := fun x:SeqInf => Quot.mk binded (s+x))
(
  by
  intro a b
  intro h
  simp
  rw [Quot.eq (r := binded) (x:=s+a) (y:=s+b)]
  apply Relation.EqvGen.rel
  simp [binded]
  simp [binded] at h
  intro n
  intro nn
  let eqq := h n nn
  simp [HAdd.hAdd]
  simp [Add.add]
  simp [eqq]
)

-- sum of two pr instance
def sum: pr → (pr → pr) :=
-- We have function SeqInf → (pr → pr).
-- We lift the function to pr → (pr → pr).
Quot.lift sumImpl
(
  by
  intro a b
  intro h
  ext g
  -- Here we use induction:
  -- We have a function pr→Prop (β down).
  -- We want to prove that β r is True for any r:pr.
  -- So goal is: ∀r:pr, β r.
  -- The induction allows us to reformulate the goal into:
  -- ∀a:SeqInf, β (pr a), where pr a is equivalence class a belongs to.
  apply Quot.induction_on (β := fun x:pr => sumImpl a x = sumImpl b x)
  intro x
  simp [sumImpl]
  rw [Quot.eq]
  apply Relation.EqvGen.rel
  simp [binded]
  simp [binded] at h
  intro n
  intro nn
  let eqq := h n nn
  simp [HAdd.hAdd]
  simp [Add.add]
  simp [eqq]
)

def mul(c: ℤ): pr → pr :=
Quot.lift (f := fun x:SeqInf => Quot.mk binded (c•x))
(
  by
  intro a b
  intro h
  simp
  rw [Quot.eq (r := binded) (x:=c•a) (y:=c•b)]
  apply Relation.EqvGen.rel
  simp [binded]
  simp [binded] at h
  intro n
  intro nn
  let eqq := h n nn
  simp [HSMul.hSMul]
  simp [SMul.smul]
  simp [eqq]
)

#synth Module ℤ SeqInf

instance i1:AddCommMonoid pr :=
{
  zero := Quot.mk binded 0
  add := sum
  add_comm := by
    intro a b
    apply Quot.induction_on (β := fun x:pr => ((sum a x) = (sum x a)))
    intro x
    apply Quot.induction_on (β := fun y:pr => sum y (Quot.mk binded x) = sum (Quot.mk binded x) y)
    intro y
    simp [sum, sumImpl]
    have eq: x+y=y+x := by apply AddCommMonoid.add_comm
    rw [eq]
  add_assoc := by
    intro a b c
    simp [HAdd.hAdd]
    apply Quot.induction_on (β := fun x:pr => sum (sum x b) c = sum x (sum b c))
    intro x
    apply Quot.induction_on (β := fun y:pr => sum (sum (Quot.mk binded x) y) c = sum (Quot.mk binded x) (sum y c))
    intro y
    apply Quot.induction_on (β := fun z:pr => sum (sum (Quot.mk binded x) (Quot.mk binded y)) z = sum (Quot.mk binded x) (sum (Quot.mk binded y) z))
    intro z
    simp [sum, sumImpl]
    have eq: x+y+z = x+(y+z) := by
      clear a b c
      sorry
    rw [eq]
  zero_add := sorry
  add_zero := sorry
  nsmul := sorry
  nsmul_zero := sorry
  nsmul_succ := sorry
}

def agr(N: ℕ): Submodule ℤ SeqInf :=
{
  carrier := {seq: SeqInf | ∀n:ℕ, n>N → seq n = 0}
  add_mem' := by
    intro a b
    simp
    intro h₁ h₂
    intro n h
    have tr: (a n) + (b n) = 0 → (a+b) n = 0 := by
      clear N h₁ h₂ h
      aesop
    apply tr
    clear tr
    let ht₁ := h₁ n h
    let ht₂ := h₂ n h
    aesop
  zero_mem' := by
    simp
    aesop
  smul_mem' := by
    simp
    have tr: ∀c:ℤ, ∀x:SeqInf, ∀n:ℕ, (c•x) n = c*(x n) := by
      simp [HSMul.hSMul]
      simp [SMul.smul]
      intro q w e
      generalize r: w e = j
      clear N r w e
      simp [Int.mul_comm]
    simp [tr]
    aesop
}

open Submodule

def binded2(s₁ s₂: SeqInf): Prop := (s₁ + ((-1)•s₂)) ∈ agr 45
