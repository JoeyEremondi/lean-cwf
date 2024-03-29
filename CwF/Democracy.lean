
import CwF.Fam
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Comma.Over
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.NatTrans
import Mathlib.Data.Opposite
import Mathlib.CategoryTheory.Limits.Shapes.Terminal

import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Equiv.Basic


import CwF.Basics
import CwF.Properties
import CwF.TypeFormers.EmptyUnit
import CwF.TypeFormers.Pi
import CwF.TypeFormers.Sigma


open CategoryTheory

-- Pi type structure in a category with families


namespace CwF
open Fam
open CwFProp
open CwFExt


class Democratic {C : Type u} [Category.{v'}  C] (cwf: CwF C) : Type _ where
  asTy : C → Ty (tmTy := cwf.tmTy) (cwf.empty)
  demIso : Γ ≅ cwf.cwfExt.snoc cwf.empty (asTy Γ)

open Democratic

section
    variable {C : Type u} [Category.{v'}  C] [cwf: CwF C] [dem : Democratic cwf]

    def demTm {Γ : C}
      : (Tm (asTy Γ)) ≃ (⬝ ⟶ Γ) :=  by
      apply Equiv.trans
      . apply closedSnocIso
      . apply Iso.homCongr (Iso.refl _)
        apply demIso.symm


    -- Isomorphic contexts have isomorphic term-sets.
    def preserveIso {Γ Δ : C} (iso : Γ ≅ Δ) :
      Tm (asTy Γ) ≅ Tm (asTy Δ) := by
        apply Equiv.toIso
        apply Equiv.trans demTm
        symm
        apply Equiv.trans demTm
        apply Iso.homCongr (Iso.refl _)
        apply iso.symm




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



    -- With democracy, arrows from Δ to Γ are precisely terms of type Γ
    -- with a variable of type Δ
    def demOpenEquiv  {Γ Δ : C}
      : (Δ ⟶ Γ) ≃ Tm ((asTy Γ)⦃p_ (asTy Δ) ⦄) := by
          let lem : ((⬝ ▹ (asTy Δ)) ⟶ (⬝ ▹ (asTy Γ))) ≃ (Δ ⟶ Γ) := by
            apply Iso.homCongr <;> apply dem.demIso.symm
          symm
          apply Equiv.trans _ lem
          apply Equiv.trans _ snocIso.symm
          simp
          symm
          apply Equiv.trans (Equiv.sigmaEquivProd _ _)
          apply Equiv.trans (Equiv.prodComm _ _)
          apply Equiv.prodUnique




    def demEmptyEquiv  {Γ Δ : C}
      : (Δ ⟶ Γ) ≃ Tm ((asTy Γ)⦃⟨⟩(⬝▹(asTy Δ))⦄) := by
      let ret := demOpenEquiv (Γ := Γ) (Δ := Δ)
      simp at ret
      apply ret

    def demOpenEquivCtx  {Γ Δ : C}
      : (Δ ⟶ Γ) ≃ Tm (asTy Γ)⦃ (‼ : Δ ⟶ ⬝) ⦄ := by
          apply demOpenEquiv.trans
          simp
          apply closedWeakenIso
          apply demIso.symm


    instance initUniqueTm' {Δ : C} : Unique (Tm ((asTy ⬝)⦃p_ (asTy Δ )⦄)) := by
      let eq := (demOpenEquiv (Δ := Δ) (Γ := ⬝)).symm
      apply eq.unique


    def initUniqueTm_snoc {Δ : C} {θ : ⬝▹(asTy Δ) ⟶ ⬝} : Unique (Tm  ((asTy ⬝)⦃θ⦄)) := by
      let peq := toEmptyUnique (C := C) (θ := p_ (asTy Δ))
      let peq2 := toEmptyUnique (C := C) (θ := θ)
      let peq3 := Eq.trans peq2 peq.symm
      cases peq3
      apply initUniqueTm'


    instance initUniqueTm {Δ : C} {θ : Δ ⟶ ⬝} : Unique (Tm  ((asTy ⬝)⦃θ⦄)) := by
      let iso := closedWeakenIso (Γ := ⬝ ▹ (asTy Δ)) (Δ := Δ) (T := asTy ⬝) (dem.demIso.symm)
      let uniq := @Equiv.unique _ _ (initUniqueTm_snoc) iso.symm
      aesop_cat


    --All democratic CwFs have a unit type
    instance : HasUnitEta C where
      Unit := asTy ⬝
      unit := demTm.invFun ‼
      unitElim {Γ} {P} {x} pu := by
        let uniq := (initUniqueTm (Δ := Γ) (θ := ‼)).uniq
        let xeq := uniq x
        let ueq := uniq (demTm.invFun ‼)⦃‼⦄
        let eq := xeq.trans ueq.symm
        cases eq
        apply pu
      ηUnit := by
        intros Δ
        fconstructor
        intros x y
        simp at x y
        let uniq := (initUniqueTm (Δ := Δ) (θ := ‼)).uniq
        aesop

    -- instance [Limits.HasInitial C] : HasEmptyEta C where
    --   Empty := asTy (Limits.initial C)
    --   exfalso fls := by
    --     apply toTerm
    --     fconstructor
    --     let f := toSub fls
    --     apply (f ≫ _)
    --     fapply ext
    --     . apply p
    --     .

    open HasPi
    -- If we have democracy and η, then each hom-set is equivalent to a function type
    def demPiEquiv [HasPiEta C] {Γ Δ : C}
      :  (Δ ⟶ Γ) ≃ (Tm (Pi (asTy Δ) (asTy Γ)⦃p⦄)) := by
          apply Equiv.trans demOpenEquiv
          symm
          apply piIso.toEquiv

    def funToDemTm [HasPiEta C] {Γ Δ : C} {θ : Δ ⟶ ⬝}
      (f : Tm (asTy Δ)⦃p_ (asTy Δ)⦄ → Tm (asTy Γ)) : Tm (asTy Γ)⦃θ⦄ := by
      simp
      apply (closedWeakenIso (dem.demIso (Γ := Δ))).invFun
      apply demEmptyEquiv.toFun
      apply demPiEquiv.invFun
      apply fromFun
      intros δ
      apply tmSub
      apply f
      apply δ

    --With functions, every type yields a context whose corresponding type has isomorphic terms
    --i.e. We can freely treat types as contexts and vice versa
    def asCtx [HasPi C] {Γ : C} (T : Ty Γ)
      : C := ⬝ ▹ (Pi (asTy Γ) T⦃demIso.inv⦄)

    def asCtxIso [HasPiEta C] {Γ : C} {T : Ty Γ} :
      Tm T ≅ Tm (asTy (asCtx T)) := by
      symm
      apply Equiv.toIso
      apply Equiv.trans demTm
      apply Equiv.trans closedSnocIso.symm
      apply Equiv.trans depPiIso.toEquiv
      apply (ctxIsoToTm demIso).toEquiv.symm

    --TODO I think we can get this to work from extensional equality types
    --since it lets
    -- instance [HasPiEta C] : HasSigma C where
    --   Sigma {Γ} S T := by
    --     apply tySub _ ‼
    --     fapply Pi
    --     . apply (asTy Γ)
    --     . apply bindTy
    --       intros γ
    --       apply tySub _ ‼
    --       apply asTy
    --       fapply snoc
    --       . fapply snoc
    --         . fapply snoc
    --           . apply Γ
    --           . apply S
    --         . apply T
    --       .
