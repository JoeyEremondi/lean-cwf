
import CwF.Fam
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Yoneda
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

section
    variable {C : Type u} [Category.{v}  C] [cwf: CwF C] [dem : Democratic cwf]

    def demTm {Γ : C}
      : (Tm (asTy Γ)) ≃ (⬝ ⟶ Γ) :=  by
      apply Equiv.trans
      . apply closedSnocIso
      . apply Iso.toEquiv
        let yNatIso := Functor.mapIso (yoneda (C := C)) (X := ⬝▹(asTy Γ)) (Y := Γ) demIso.symm
        apply yNatIso.app (Opposite.op ⬝)


    /-- Snoc is exactly the dependent product in a democratic CwF -/
    def demSnoc {Γ : C} {T : Ty Γ}
      : Tm (asTy (Γ ▹ T)) ≅ ((γ : Tm (asTy Γ)) × Tm (tySub T (γ⁻ ≫ demIso.inv))) := by
      apply Equiv.toIso
      apply Equiv.trans demTm
      apply Equiv.trans snocIso
      fapply Equiv.sigmaCongr
      . apply demTm.symm
      . intros γ
        simp [demTm, closedSnocIso, termSecEquiv, emptySecIso, toTerm, toSub]
        apply Equiv.cast
        apply  congrArg Tm
        apply congrArg (tySub T)
        symm
        rw [Iso.comp_inv_eq, ext_inj_general]
        aesop_cat

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
