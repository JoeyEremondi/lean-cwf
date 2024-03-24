
import CwF.Fam
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.NatTrans
import Mathlib.Data.Opposite
import Mathlib.CategoryTheory.Limits.Shapes.Terminal

import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Equiv.Basic


import CwF.Basics
import CwF.Properties
import CwF.TypeFormers.Pi
import CwF.TypeFormers.Sigma


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


    open HasPi

    -- With democracy, arrows from Δ to Γ are precisely terms of type Γ
    -- with a variable of type Δ
    def demOpenEquiv  {Γ Δ : C}
      : (Δ ⟶ Γ) ≃ Tm ((asTy Γ)⦃p (T := asTy Δ )⦄) := by
          let yΓ := Functor.mapIso yoneda (dem.demIso (Γ := Γ))
          let yΓ' := yΓ.app (Opposite.op Δ)
          simp at yΓ'
          let yΔ := Functor.mapIso coyoneda (dem.demIso (Γ := Δ)).op
          let yΔ' := (yΔ.app  (⬝ ▹ (asTy Γ)))
          simp at yΔ'
          let lem : ((⬝ ▹ (asTy Δ)) ⟶ (⬝ ▹ (asTy Γ))) ≅ (Δ ⟶ Γ) :=
            yΔ' ≪≫ yΓ'.symm
          symm
          apply Equiv.trans _ lem.toEquiv
          apply Equiv.trans _ snocIso.symm
          simp
          symm
          apply Equiv.trans (Equiv.sigmaEquivProd _ _)
          apply Equiv.trans (Equiv.prodComm _ _)
          apply Equiv.prodUnique

    -- If we have democracy and η, then each hom-set is equivalent to a function type
    def demPiEquiv [HasPiEta C] {Γ Δ : C}
      :  (Δ ⟶ Γ) ≃ (Tm (Pi (asTy Δ) (asTy Γ)⦃p⦄)) := by
          apply Equiv.trans demOpenEquiv
          symm
          apply piIso.toEquiv


   -- TODO: can we get Sigma types from democracy?
