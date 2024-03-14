
import CwF.Fam
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.Data.Opposite
import Mathlib.CategoryTheory.Limits.Shapes.Terminal


import CwF.CwF
import CwF.Properties
import CwF.TypeFormers.DepTyFormer

open CategoryTheory

-- Pi type structure in a category with families


universe u v u2
variable {C : Type u} [Category.{v} C] [CwF C]


class HasPi : Type _ where
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
    : eqModCast
      (app f s)⦃θ⦄
      (app (T := T⦃wk θ⦄) (castTm (f⦃θ⦄) (by rw [PiS]) ) s⦃θ⦄)
      (by
          rw [tySubComp]
          rw [tySubComp]
          rw [wkTm]
      )

open HasPi

attribute [simp] Piβ PiS LamS AppS

-- set_option pp.notation false

open CwFExt
open CwFProp

class HasSigma : Type _ where
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
  ProjS1 {Γ Δ : C} {S : Ty Γ} {T : Ty (Γ ▹ S)} {t : Tm T} {θ : Δ ⟶ Γ} {x : Tm (Sigma S T)}
    : (proj1 x)⦃θ⦄ = proj1 (T := T⦃wk θ⦄) (castTm x⦃θ⦄ (by simp [SigmaS (P := T)]))

  ProjS2 {Γ Δ : C} {S : Ty Γ} {T : Ty (Γ ▹ S)} {t : Tm T} {θ : Δ ⟶ Γ} {x : Tm (Sigma S T)}
    {x : Tm (Sigma S T)}
    : eqModCast
        (proj2 x)⦃θ⦄
        (proj2 (T := T⦃wk θ⦄) (castTm x⦃θ⦄ (by simp [SigmaS (P := T)])))
        (by
            simp only [tySubComp] <;> try aesop_cat
            apply  congrArg (tySub T) <;> try aesop_cat
            simp
            rw [ext_inj]
            fconstructor
            . simp [toSub]
              apply congrArg (fun x => CategoryStruct.comp x θ)


        )
  -- PairS : (pair s t)⦃θ⦄ = pair s⦃θ⦄ t⦃wk θ⦄

open HasPi

attribute [simp] Piβ PiS LamS AppS
