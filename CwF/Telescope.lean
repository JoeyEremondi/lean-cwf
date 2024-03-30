import CwF.Fam
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.NatTrans
import Mathlib.CategoryTheory.Equivalence
import Mathlib.Data.Opposite
import Mathlib.CategoryTheory.Limits.Shapes.Terminal


import CwF.Basics
import CwF.Properties
import CwF.TypeFormers.Pi
import CwF.TypeFormers.Sigma
import CwF.Democracy


open CategoryTheory

-- Pi type structure in a category with families


namespace CwF
open Fam
open CwFProp
open CwFExt




-- We can define telescopes over a CwF if there's another CwF structure on the same
-- category that is democratic and has Sigma types.
-- We also require that we can inject from single types/terms into telescopes/envs,
-- and that this respects substitution
-- (expressed by a natural transformation)
class IsoTelescoping (C : Type u) {D : Type u}
    [Category.{v'} C] [dcat : Category.{v'} D] [cwf : CwF C] (tcwf : CwF D) : Type _ where
  equ : Equivalence C D
  -- isDem : Democratic tcwf
  uinst : HasUnit D
  sigma : HasSigma D
  nat : NatTrans cwf.tmTy.tmTyFam (Functor.comp equ.op.functor tcwf.tmTy.tmTyFam)


section

  variable {C D : Type u} [cat : Category.{v'}  C] [dcat : Category D]
    [cwf: @CwF C cat] [tcwf : @CwF D dcat] [tele : IsoTelescoping C tcwf]


  open IsoTelescoping
  local instance : CwF D := tcwf
  def tty := tcwf.tmTy


  -- @[default_instance]
  -- local instance  : @CwF C cat  := cwf
  -- def ttm : TmTy C := tele.tcwf.tmTy

  abbrev Tele (Γ : C) : Type u :=
    Ty  (tmTy := tty) (tele.equ.functor.obj Γ)

  abbrev Env {Γ : C} (TT : Tele (tele := tele) Γ) : Type u :=
    Tm  (tmTy := tty) TT

  def emptyTele : Tele (tele := tele) ⬝ := by
    dsimp only [Tele]
    apply tele.uinst.Unit



end

