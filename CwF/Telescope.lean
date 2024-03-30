import CwF.Fam
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.NatTrans
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
class Telescoping {C : Type u} [cat : Category.{v'}  C] (cwf: CwF C) : Type _ where
  tcwf : CwF C
  isDem : Democratic tcwf
  uinst : @HasUnit C cat tcwf
  sigma : @HasSigma C cat tcwf
  nat : NatTrans cwf.tmTy.tmTyFam tcwf.tmTy.tmTyFam


section

  -- variable {C : Type u} [cat : Category.{v'}  C] {cwf: @CwF C cat} [tele : @Telescoping C cat cwf]


  open Telescoping


  -- @[default_instance]
  -- local instance  : @CwF C cat  := cwf
  -- def ttm : TmTy C := tele.tcwf.tmTy

  def Tele {C : Type u} [cat : Category.{v'}  C] {cwf: @CwF C cat} [tele : @Telescoping C cat cwf]
  (Γ : C) : Type u :=
    Ty  (tmTy := tele.tcwf.tmTy) Γ

  def Env {C : Type u} [cat : Category.{v'}  C] {cwf: @CwF C cat} [tele : @Telescoping C cat cwf]
    {Γ : C}
    (TT : Tele (tele := tele) Γ) : Type u :=
    Tm (tmTy := tele.tcwf.tmTy) TT

  def emptyTele {C : Type u} [cat : Category.{v'}  C] {cwf: @CwF C cat} [tele : @Telescoping C cat cwf]
    {Γ : C} : Tele (tele := tele) Γ := by
    apply tySub (tmTy := tele.tcwf.tmTy)
    . apply uinst.Unit
    simp


end

