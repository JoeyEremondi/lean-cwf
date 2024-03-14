import CwF.Fam
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.NatTrans
import Mathlib.Data.Opposite
import Mathlib.CategoryTheory.Limits.Shapes.Terminal


import CwF.Basics
import CwF.Properties
import CwF.TypeFormers.PiSigma


open CategoryTheory

-- Pi type structure in a category with families


namespace CwF
open Fam
open CwFProp
open CwFExt


class Democratic {C : Type u} [Category.{v}  C] (cwf: CwF C) : Type _ where
  asTy : C → Ty (tmTy := cwf.tmTy) (cwf.cwfExt.empty)
  demIso : Γ ≅ cwf.cwfExt.snoc empty (asTy Γ)

open Democratic

-- We can define telescopes over a CwF if there's another CwF structure on the same
-- category that is democratic
class Telescoping {C : Type u} [cat : Category.{v}  C] (tmF : CategoryTheory.Functor Cᵒᵖ Fam)  : Type _ where
  telecwf : @CwF C cat
  teleDemo : Democratic telecwf
  teleNat : NatTrans tmF telecwf.tmTy.tmTyF

attribute [instance] Telescoping.teleDemo

variable  {C : Type u} [Category.{v}  C] [cwf: CwF C] [teleInst : Telescoping (cwf.tmTy.tmTyF)]

open Telescoping


def Tele (Γ : C) := Ty (tmTy := teleInst.telecwf.tmTy) Γ

def teleSub {Δ Γ : C} (Ts : Tele Γ) (θ : Δ ⟶ Γ) : Tele Δ
  := tySub (tmTy := teleInst.telecwf.tmTy) Ts θ


def Env {Γ : C} (Ts : Tele Γ) := Tm (tmTy := teleInst.telecwf.tmTy) Ts


def envSub {Δ Γ : C} {Ts : Tele Γ} (e : Env Ts) (θ : Δ ⟶ Γ) : Env (teleSub Ts θ)
  := tmSub (tmTy := teleInst.telecwf.tmTy) e θ

def emptyTele (Γ : C) : Tele Γ :=
   teleSub (teleInst.teleDemo.asTy empty) (by simp)

def teleSnoc (Γ : C) (T̂ : Tele Γ) : teleInst.telecwf.cwfExt.snoc

-- class HasDemo :

-- structure Telescope (Γ : C) where
--   fields : C
--   asType : Ty Γ
--   iso : fields ≅ Tm (asType)
