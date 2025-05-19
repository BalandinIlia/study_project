import Mathlib.Control.Monad.Basic
import Mathlib.Control.Applicative

namespace MonadExperiment

-- Integer numbers
inductive Z where
-- zero
| zero: Z
-- next
| next: Z → Z
-- previous
| prev: Z → Z

def str(z:Z):String:=match z with
| Z.zero => "0"
| Z.next z => String.append "+" (str z)
| Z.prev z => String.append "-" (str z)

-- All types are
-- Z or
-- Z->Z or Z->Z->Z or ...

-- Type name in order to distinguish types
class TypeType(T: Type) where
  name: String

instance ins1: TypeType Z := {name:="value"}
instance ins2: TypeType (Z→Z) := {name:="function"}
instance ins3: TypeType (Z→Z→Z) := {name:="function"}
instance ins4: TypeType (Z→Z→Z→Z) := {name:="function"}
instance ins5: TypeType (Z→Z→Z→Z→Z) := {name:="function"}
instance ins6: TypeType (Z→Z→Z→Z→Z→Z) := {name:="function"}
instance ins7: TypeType (Z→Z→Z→Z→Z→Z→Z) := {name:="function"}
instance ins8: TypeType (Z→Z→Z→Z→Z→Z→Z→Z) := {name:="function"}
instance ins9: TypeType T := {name:="other"}

-- Does z contain only next constructors?
def allNext(z:Z):Bool :=
match z with
| Z.zero => true
| Z.next z => allNext z
| Z.prev _ => false

-- Does z contain only prev constructors?
def allPrev(z:Z):Bool :=
match z with
| Z.zero => true
| Z.next _ => false
| Z.prev z => allPrev z

-- canonical form
def IsCanon(z:Z):Bool := allNext z || allPrev z

-- canonical values
inductive Canon where
-- For just Z:
--     Term is not granted to have canonical form
-- For function result:
--     Function is not granted to return canonical form
-- For function obtained by partial application:
--     There was a parameter, whose canonical form is not granted
| notGr: Canon
-- For just Z:
--     Term is granted to have canonical form
-- For function result:
--     Function is granted to have canonical form if all
--     input parameters are canonical form
-- For function obtained by partial application:
--     Canonical form of all applied parameters is granted.
| granted: Canon
-- For just Z:
--     Term is granted to have canonical form
-- For function result:
--     Function is granted to return canonical form
-- For function obtained by partial application:
--     Canonical form of all applied parameters is granted.
| super: Canon

structure Spec(T: Type) where
val: T
canon: Canon

instance f:ToString (Spec Z):=
{
  toString(a: Spec Z) := match a.canon with
  | Canon.notGr => String.append "Not Granted:" (str a.val)
  | Canon.granted => String.append "Granted:" (str a.val)
  | Canon.super => String.append "Super:" (str a.val)
}

def pureImp{T: Type}(a: T)[n: TypeType T]: Spec T :=
if n.name=="value" then Spec.mk a Canon.notGr
                   else Spec.mk a Canon.granted

def pureImp2{T: Type}(a: T): Spec T := pureImp a

def bindImp{α β : Type}
           (a: Spec α)
           (f: α → Spec β)
           [n: TypeType β]: Spec β :=
if n.name=="value" then
  match a.canon with
  | Canon.notGr => match (f a.val).canon with
                   | Canon.notGr => Spec.mk (f a.val).val Canon.notGr
                   | Canon.granted => Spec.mk (f a.val).val Canon.notGr
                   | Canon.super => Spec.mk (f a.val).val Canon.granted
  | Canon.granted  => match (f a.val).canon with
                   | Canon.notGr => Spec.mk (f a.val).val Canon.notGr
                   | Canon.granted => Spec.mk (f a.val).val Canon.granted
                   | Canon.super => Spec.mk (f a.val).val Canon.granted
  | Canon.super  => match (f a.val).canon with
                   | Canon.notGr => Spec.mk (f a.val).val Canon.notGr
                   | Canon.granted => Spec.mk (f a.val).val Canon.granted
                   | Canon.super => Spec.mk (f a.val).val Canon.granted
else
  match a.canon with
  | Canon.notGr => Spec.mk (f a.val).val Canon.notGr
  | Canon.granted => Spec.mk (f a.val).val Canon.granted
  | Canon.super => Spec.mk (f a.val).val Canon.granted

def bindImp2{α β : Type}
            (a: Spec α)
            (f: α → Spec β): Spec β := bindImp a f

instance mon: Monad Spec :=
{
  pure := pureImp2
  bind := bindImp2
}

def apply{α β : Type}
          (a: Spec α)
          (f: Spec (α → Spec β))
          [n: TypeType β] :=
if n.name=="function" then
  match (f.val a.val).canon with
  | Canon.super => Spec.mk (f.val a.val).val Canon.granted
  | Canon.notGr => Spec.mk (f.val a.val).val Canon.notGr
  | Canon.granted => match f.canon with
                     | Canon.super => Spec.mk (f.val a.val).val a.canon
                     | Canon.granted => Spec.mk (f.val a.val).val a.canon
                     | Canon.notGr => Spec.mk (f.val a.val).val Canon.notGr
else
  match f.canon with
  | Canon.notGr => Spec.mk (f.val a.val).val Canon.notGr
  | Canon.granted => Spec.mk (f.val a.val).val a.canon
  | Canon.super => Spec.mk (f.val a.val).val a.canon

def zero1 := Spec.mk Z.zero Canon.granted

def zero2 := Spec.mk (Z.prev (Z.next (Z.zero))) Canon.notGr

def increm(z: Z): Spec Z := Spec.mk (Z.next z) Canon.notGr
def decrem(z: Z): Spec Z := Spec.mk (Z.prev z) Canon.notGr

def incremCl(z: Z): Spec Z :=
match z with
| Z.zero => Spec.mk (Z.next z) Canon.granted
| Z.next _ => Spec.mk (Z.next z) Canon.granted
| Z.prev zz => Spec.mk zz Canon.granted
def decremCl(z: Z): Spec Z :=
match z with
| Z.zero => Spec.mk (Z.prev z) Canon.granted
| Z.prev _ => Spec.mk (Z.prev z) Canon.granted
| Z.next zz => Spec.mk zz Canon.granted

def NO(z:Z):Z:=
match z with
| Z.zero => z
| Z.next zz => Z.next (NO zz)
| Z.prev zz => NO zz
def PO(z:Z):Z:=
match z with
| Z.zero => z
| Z.prev zz => Z.prev (PO zz)
| Z.next zz => PO zz
def nextOnly(z:Z):Spec Z := Spec.mk (NO z) Canon.super
def prevOnly(z:Z):Spec Z := Spec.mk (PO z) Canon.super
def sumImp(z1 z2: Z):Z:=
match z1, z2 with
| Z.zero, x => x
| x, Z.zero => x
| Z.next x1, Z.prev x2 => sumImp x1 x2
| Z.prev x1, Z.next x2 => sumImp x1 x2
| Z.next x1, Z.next _ => Z.next (sumImp x1 z2)
| Z.prev x1, Z.prev _ => Z.prev (sumImp x1 z2)
def norm(z:Z):Spec Z := Spec.mk (sumImp (PO z) (NO z)) Canon.super
def sum(z1 z2:Z):Spec Z := Spec.mk (sumImp z1 z2) Canon.granted

#eval zero1
#eval zero2

#eval bindImp zero1 increm
#eval bindImp zero1 incremCl

#eval bindImp zero1 nextOnly
#eval bindImp zero2 nextOnly

#eval bindImp (bindImp zero2 increm) prevOnly

#eval apply zero1 (bindImp zero1 (fun z:Z => pureImp (sum z)))
#eval apply zero1 (bindImp zero2 (fun z:Z => pureImp (sum z)))
#eval apply zero2 (bindImp zero1 (fun z:Z => pureImp (sum z)))
#eval apply zero2 (bindImp zero2 (fun z:Z => pureImp (sum z)))

#eval apply zero1 (bindImp (bindImp zero2 norm) (fun z:Z => mon.pure (sum z)))

#eval bindImp (bindImp zero2 norm) incremCl
#eval bindImp (bindImp zero2 norm) increm
