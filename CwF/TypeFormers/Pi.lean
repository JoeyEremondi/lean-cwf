
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

-- class HasRecords {C : Type u} [Category.{v} C] [CwF C] : Type _ where
--   BigSigma {Γ : C}
--     : (Over Γ ) → Ty Γ

--   mkBigSigma  {Γ : C} {fields : Over Γ}
--     : (_ ⟶ fields) → Tm (BigSigma tele)


end CwF
