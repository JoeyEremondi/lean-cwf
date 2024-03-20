
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


class HasPi {C : Type u} [Category.{v} C] [CwF C] : Type _ where
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


open HasPi

attribute [simp] Piβ PiS LamS AppS

-- set_option pp.notation false

open CwFExt
open CwFProp

-- attribute [aesop unsafe 50% simp] Category.assoc

class HasSigma {C : Type u} [Category.{v} C] [CwF C] : Type _ where
  Sigma : DepTypeFormer C
  pair  {Γ : C} {S : Ty Γ} {T : Ty (Γ ▹ S)}
     : (s : Tm S) → Tm T⦃s⁻⦄ → Tm (Sigma S T)
  proj1  {Γ : C} {S : Ty Γ} {T : Ty (Γ ▹ S)}
     : Tm (Sigma S T) → Tm S
  proj2  -- {Γ : C} {S : Ty Γ} {T : Ty (Γ ▹ S)}
     : (x : Tm (Sigma S T)) → Tm T⦃(proj1 x)⁻⦄
  -- Projection reduction and substitution congruence
  SigmaProj1 : proj1 (pair s t) = s
  SigmaProj2 : proj2 (T := T) (pair s t) = castTm t (by simp [SigmaProj1])
  SigmaS : DepSubCongr Sigma
  ProjS1 {Γ Δ : C} {S : Ty Γ} {T : Ty (Γ ▹ S)} {θ : Δ ⟶ Γ} {x : Tm (Sigma S T)}
    : (proj1 x)⦃θ⦄ = proj1 (T := T⦃wk θ⦄) (castTm x⦃θ⦄ (by simp [SigmaS (P := T)]))

  /-- Proof that (proj₂ x)⦃θ⦄ =ₜ proj₂ (↑ₜ x⦃θ⦄),
      but aesop can't figure the type equalities out on its own  -/
  ProjS2 {Γ Δ : C} {S : Ty Γ} {T : Ty (Γ ▹ S)} {θ : Δ ⟶ Γ} {x : Tm (Sigma S T)}
    {x : Tm (Sigma S T)}
    :  (proj2 x)⦃θ⦄ =ₜ  (proj2 (T := T⦃wk θ⦄) (castTm x⦃θ⦄ (by simp [SigmaS (P := T)])))

  PairS  {Γ Δ : C} {S : Ty Γ} {T : Ty (Γ ▹ S)}  {θ : Δ ⟶ Γ} (s : Tm S) (t : Tm T⦃s⁻⦄)
    :  (pair s t)⦃θ⦄ =ₜ (pair (T := tySub T (wk θ)) s⦃θ⦄ (↑ₜ t⦃θ⦄ ))


open HasPi
open HasSigma

attribute [simp] Piβ PiS LamS AppS
attribute [simp] SigmaProj1 SigmaProj2 SigmaS ProjS1 ProjS2 PairS

-- class HasRecords {C : Type u} [Category.{v} C] [CwF C] : Type _ where
--   BigSigma {Γ : C}
--     : (Over Γ ) → Ty Γ

--   mkBigSigma  {Γ : C} {fields : Over Γ}
--     : (_ ⟶ fields) → Tm (BigSigma tele)


end CwF
