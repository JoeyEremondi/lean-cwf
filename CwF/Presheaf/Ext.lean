import CwF.Fam
import CwF.Util
import CwF.Sigma
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.NatTrans
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Presheaf
import Mathlib.CategoryTheory.Elements
import Mathlib.Data.Opposite
import Mathlib.CategoryTheory.Types

import CwF.Presheaf.TmTy
import CwF.Presheaf.Snoc

import CwF.Basics

open CategoryTheory


universe u v u₂
variable {C : Type u} [CCat : Category.{v}  C]

def pshExt {Γ Δ : Cᵒᵖ ⥤ Type u₂}
  {T : Ty Γ} (θ : Δ ⟶ Γ) (t : pshTm (pshTySub T θ))
    : Δ ⟶ pshSnoc Γ T where

    app k δ :=  ⟨θ.app k δ, t.tmFun k δ⟩

    naturality := @fun k1 k2 f => by
      funext δ
      simp
      fconstructor
      . apply congrFun (θ.naturality f) δ
      . let teq := symm (t.tmNat _ _ f δ)
        simp at teq
        fapply heq_of_eq_of_heq teq
        fapply pshTyMapSubArg


theorem pshExtP : {Γ Δ : Cᵒᵖ ⥤ Type u₂} → {T : pshTy Γ}
    → {θ : Δ ⟶ Γ} → {t : pshTm (pshTySub T θ)}
    → (pshExt θ t) ≫ pshP = θ := by aesop_cat


theorem pshExt_pHelper : {Γ Δ : Cᵒᵖ ⥤ Type u₂} → {T : pshTy Γ}
    → {θ : Δ ⟶ Γ} → {t : pshTm (pshTySub T θ)} → {T : pshTy Γ}
    → (pshTySub (pshTySub T pshP) (pshExt θ t))  = pshTySub  T θ := by aesop_cat


theorem pshExtV {Γ Δ : Cᵒᵖ ⥤ Type u₂}  {T : pshTy Γ} (θ : Δ ⟶ Γ) (t : pshTm (pshTySub T θ))
    : pshTmSub pshV (pshExt θ t) = cast (by simp [pshExt_pHelper]) t  := by aesop_cat
  -- The extension is unique

theorem pshExt_unique {Γ Δ : Cᵒᵖ ⥤ Type u₂} {T : pshTy Γ} (f : Δ ⟶ Γ)
    (t : pshTm (pshTySub T f))
    (g : Δ ⟶ pshSnoc Γ T)
    (peq :  g ≫ pshP = f)
    (veq : pshTmSub pshV g = (cast (by aesop) t) )
    : g = pshExt f t := by aesop_cat

