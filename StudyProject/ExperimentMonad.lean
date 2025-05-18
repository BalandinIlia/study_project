import Mathlib.Control.Monad.Basic

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
| notGr: Canon
-- For just Z:
--     Term is granted to have canonical form
-- For function result:
--     Function is granted to have canonical form if all
--     input parameters are canonical form
| granted: Canon
-- For just Z:
--     Term is granted to have canonical form
-- For function result:
--     Function is granted to return canonical form
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

def pureImp{T: Type}(a: T): Spec T := Spec.mk a Canon.notGr

def bindImp{α β : Type}(a: Spec α)(f: α → Spec β): Spec β :=
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

instance ins: Monad Spec :=
{
  pure := pureImp
  bind := bindImp
}

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
| Z.prev zz => Z.prev (NO zz)
| Z.next zz => NO zz
def nextOnly(z:Z):Spec Z := Spec.mk (NO z) Canon.super
def prevOnly(z:Z):Spec Z := Spec.mk (PO z) Canon.super

#eval zero1
#eval zero2

#eval ins.bind zero1 increm
#eval ins.bind zero1 incremCl

#eval ins.bind zero1 nextOnly
#eval ins.bind zero2 nextOnly

#eval ins.bind (ins.bind zero2 increm) prevOnly
