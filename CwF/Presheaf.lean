

import CwF.Fam
import CwF.Util
import CwF.Sigma
import CwF.CwFProperties
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.NatTrans
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Presheaf
import Mathlib.CategoryTheory.Elements
import Mathlib.Data.Opposite
import Mathlib.CategoryTheory.Types

import CwF.PresheafTmTy
import CwF.PresheafSnoc

import CwF.CwF

open CategoryTheory


universe u v u₂
variable {C : Type u} [CCat : Category.{v}  C]







def pshCwF : CwF (Cᵒᵖ ⥤ Type u₂) where
  empty := Limits.terminal _

  emptyUnique := Limits.uniqueToTerminal

  snoc := pshSnoc


  p :=
    ⟨ fun k γτ =>  γτ.fst
    , @fun k1 k2 f => by
      aesop_cat
    ⟩

  v := @fun Γ T =>
  by
    simp only [pshTmTyFunctor, Tm, TmTy.F]
    apply famForInv.inv
    fconstructor
    . intros k γ
      simp [tySub, pshTySub, mapIx]
      simp at γ
      exact γ.snd
    . aesop_cat

  ext := @fun Γ Δ T θ t => {
    app := fun k δ => ⟨θ.app k δ, (famForInv.hom t).tmFun k δ⟩
    naturality := @fun k1 k2 f => by
      funext δ
      simp
      fconstructor
      . apply congrFun (θ.naturality f) δ
      . let teq := symm ((famForInv.hom t).tmNat _ _ f δ)
        simp at teq
        fapply heq_of_eq_of_heq teq
        fapply pshTyMapSubArg
  }

  ext_p := by aesop_cat
  ext_pHelper := by aesop_cat
  ext_v := by simp
  ext_unique := by simp
