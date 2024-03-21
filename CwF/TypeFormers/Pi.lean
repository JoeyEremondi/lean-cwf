
import CwF.Fam
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.Data.Opposite
import Mathlib.CategoryTheory.Limits.Shapes.Terminal


import CwF.Basics
import CwF.Properties
import CwF.TypeFormers.DepTyFormer

open CategoryTheory

-- Pi type structure in a category with families


namespace CwF

universe u v u2


class HasPi (C : Type u) [Category.{v} C] [CwF C] : Type _ where
  Pi : DepTypeFormer C
  lam  {Γ : C} {S : Ty Γ} {T : Ty (Γ ▹ S)}
    : Tm T → Tm (Pi S T)
  app {Γ : C} {S : Ty Γ} {T : Ty (Γ ▹ S)}
    : (f : Tm (Pi S T)) → (x : Tm S) → Tm (T⦃x⁻⦄)
  -- Laws for functions: beta reduction and substitution
  Piβ : app (lam t) s = t⦃s⁻⦄
  PiS : DepSubCongr Pi
  LamS {Γ Δ : C} {S : Ty Γ} {T : Ty (Γ ▹ S)} {t : Tm T} {θ : Δ ⟶ Γ}
    : (lam t)⦃θ⦄ =ₜ (lam (t⦃wk θ⦄))
  AppS {Γ Δ : C} {S : Ty Γ} {T : Ty (Γ ▹ S)} {θ : Δ ⟶ Γ} {f : Tm (Pi S T)} {s : Tm S}
    :  (app f s)⦃θ⦄ =ₜ (app (T := T⦃wk θ⦄) (castTm (f⦃θ⦄) (by rw [PiS]) ) s⦃θ⦄)



-- set_option pp.notation false

open CwFExt
open CwFProp


open HasPi

attribute [simp] Piβ PiS LamS AppS

-- theorem app_heq {C : Type u} [Category.{v} C] [CwF C] [HasPi C]
--   {Γ : C} {S S' : Ty Γ } {T : Ty Γ▹S} {T' : Ty Γ▹S'} {f : Tm (Pi S T)} {g : Tm (Pi S' T')}
--   {x : Tm S} {y : Tm S'}
--   (eq : Tm (T⦃x⁻⦄) = Tm (T'⦃y⁻⦄))
--   (eq1 : HEq f g) (eq2 : HEq x y)
--   : (app f x) = (cast (eq.symm) (app g y) ) := by aesop_cat



def ηBody {C : Type u} [Category.{v} C] [CwF C] [HasPi C]
  {Γ : C} {S : Ty Γ} {T : Ty Γ▹S} (f : Tm (HasPi.Pi S T))
  : Tm T
  := (castTm (app (↑ₜ f⦃p⦄) v) (by
            simp [toSub]
            apply ty_id
            rw [ext_inj_general]
            aesop_cat
            ))


def ηExpand  {C : Type u} [Category.{v} C] [CwF C] [HasPi C]
  {Γ : C} {S : Ty Γ} {T : Ty Γ▹S} (f : Tm (HasPi.Pi S T))
  : Tm (HasPi.Pi S T)
  :=  lam (S := S) (ηBody f)


class HasEta (C : Type u) [Category.{v} C] [CwF C] extends HasPi C : Type _ where
  Piη {Γ : C} {S : Ty Γ} {T : Ty Γ▹S} {f : Tm (HasPi.Pi S T)}
    : f = ηExpand f


def piIso [Category.{v} C] [CwF C] [HasEta C]
  {Γ : C} {S T : Ty Γ}
  : Tm (Pi S T⦃p⦄) ≅ Tm T⦃p (T := S)⦄ where
  hom f := ηBody f
  inv := lam
  hom_inv_id := by
    funext f
    simp
    symm
    apply HasEta.Piη
  inv_hom_id := by
    funext f
    simp [ηBody]
    symm
    apply tm_id
    simp [wk]
    rw [ext_inj_general]
    aesop_cat


-- class HasRecords {C : Type u} [Category.{v} C] [CwF C] : Type _ where
--   BigSigma {Γ : C}
--     : (Over Γ ) → Ty Γ

--   mkBigSigma  {Γ : C} {fields : Over Γ}
--     : (_ ⟶ fields) → Tm (BigSigma tele)


end CwF
