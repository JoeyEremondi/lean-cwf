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
  asTy : C → Ty (tmTy := cwf.tmTy) (cwf.empty)
  demIso : Γ ≅ cwf.cwfExt.snoc cwf.empty (asTy Γ)

open Democratic

-- We can define telescopes over a CwF if there's another CwF structure on the same
-- category that is democratic
class Telescoping {C : Type u} [cat : Category.{v}  C] (tmF : CategoryTheory.Functor Cᵒᵖ Fam)  : Type _ where
  cwf : @CwF C cat
  demo : Democratic cwf
  nat : NatTrans tmF cwf.tmTy.tmTyFam


variable  {C : Type u} [cat : Category.{v}  C] [basecwf : CwF C] [tInst : Telescoping (basecwf.tmTy.tmTyFam)]

open Telescoping

def tcwf := tInst.cwf

instance : Democratic (@tcwf C cat basecwf tInst ) := tInst.demo

def Tele (Γ : C) := Ty (tmTy := tcwf.tmTy) Γ

def teleSub {Δ Γ : C} (Ts : Tele Γ) (θ : Δ ⟶ Γ) : Tele Δ
  := tySub (tmTy := tcwf.tmTy) Ts θ


def Env {Γ : C} (Ts : Tele Γ) := Tm (tmTy := tcwf.tmTy) Ts


def envSub {Δ Γ : C} {Ts : Tele Γ} (e : Env Ts) (θ : Δ ⟶ Γ) : Env (teleSub Ts θ)
  := tmSub (tmTy := tcwf.tmTy) e θ

def emptyTele (Γ : C) : Tele Γ :=
   teleSub (asTy tcwf.empty) (tcwf.toEmpty)

def teleSnoc {Γ : C} (Ts : Tele Γ) (T : Ty Γ) : Tele Γ :=
  asTy (by simp)

-- class HasDemo :

-- structure Telescope (Γ : C) where
--   fields : C
--   asType : Ty Γ
--   iso : fields ≅ Tm (asType)
