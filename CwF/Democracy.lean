
import CwF.Fam
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.NatTrans
import Mathlib.Data.Opposite
import Mathlib.CategoryTheory.Limits.Shapes.Terminal


import CwF.Basics
import CwF.Util.ULift
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

section
    variable {C : Type u} [Category.{v}  C] [cwf: CwF C] [dem : Democratic cwf]

    def demTm {Γ : C}
      : (Tm (asTy Γ)) ↑≅ ⬝ ⟶ Γ :=  by
      apply Iso.trans
      . apply closedSnocIso
      . apply Functor.mapIso uliftFunctor
        let yNatIso := Functor.mapIso (yoneda (C := C)) (X := ⬝▹(asTy Γ)) (Y := Γ) demIso.symm
        apply yNatIso.app (Opposite.op ⬝)

    -- instance demSigma : HasSigma C where
    --   Sigma {Γ} S T := (asTy (Γ▹S)▹T)⦃‼⦄
    --   pair s t := by
    --     apply tmSub _ ‼
    --     apply demTm


    def demSnoc {Γ : C} {T : Ty Γ}
      : Tm (asTy (Γ ▹ T)) ≅ ((γ : Tm (asTy Γ)) × Tm (tySub T (γ⁻ ≫ demIso.inv))) where
      hom t :=
        let θ := (demTm.hom (ULift.up t)).down
        by admit
      -- apply viaUlift
      -- . apply demTm
      -- . let sn := (snocIso (Δ := Γ) (T := T)).symm
      --   simp [uliftIsoMax]
      --   apply sn.symm
      -- . fconstructor
      --   . intros θ
      --     apply SplitEpi.mk (‼ ≫ θ) (by
      --       simp
      --       simp)
      -- apply Iso.trans
      -- . apply demTm
      -- apply termSecPreserveIso
      -- trans
      -- . apply emptySecIso
      -- . fconstructor
      --   . intros f
      --     fconstructor
      --     . apply CategoryStruct.comp (‼ ≫ f)


-- end


-- end CwF
