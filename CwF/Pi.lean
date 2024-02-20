
import CwF.Fam
import CwF.CwFProperties
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.Data.Opposite
import Mathlib.CategoryTheory.Limits.Shapes.Terminal


import CwF.CwF

open CategoryTheory

-- Pi type structure in a category with families


universe u v u2
variable {C : Type u} [Category.{v}  C] [TmTy.{u,v} C] [Limits.HasTerminal C] [CwF C]

-- variable {Γ Δ : C} {S : Ty Γ} {T : Ty (Γ ▹ S)} {f : Pi S T } {s : Tm S} {t : Tm T} {θ : Δ ⟶ Γ}

class HasPi : Type _ where
  Pi : {Γ : C} → (S : Ty Γ)
    → (T : Ty (Γ ▹ S)) → Ty Γ
  lam  {Γ : C} {S : Ty Γ} {T : Ty (Γ ▹ S)}
    : Tm T → Tm (Pi S T)
  app {Γ : C} {S : Ty Γ} {T : Ty (Γ ▹ S)}
    : (f : Tm (Pi S T)) → (x : Tm S) → Tm (T⦃x⁻⦄)
  -- Laws for functions: beta reduction and substitution
  Piβ : app (lam t) s = t⦃s⁻⦄
  PiS : (Pi S T)⦃θ⦄ = Pi (S⦃θ⦄) (T⦃wk θ⦄)
  LamS {Γ Δ : C} {S : Ty Γ} {T : Ty (Γ ▹ S)} {t : Tm T} {θ : Δ ⟶ Γ}
    : (lam t)⦃θ⦄ =ₜ (lam (t⦃wk θ⦄))
  AppS {Γ Δ : C} {S : Ty Γ} {T : Ty (Γ ▹ S)} {θ : Δ ⟶ Γ} {f : Tm (Pi S T)} {s : Tm S}
    : eqModCast ((app f s)⦃θ⦄) (app (↑ₜ (f⦃θ⦄)) (s⦃θ⦄)) (by
    rw [tySubComp]
    rw [tySubComp]
    rw [wkTm]
    )
