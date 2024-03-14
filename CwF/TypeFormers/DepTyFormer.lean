import CwF.CwF
import CwF.Properties


import Mathlib.CategoryTheory.Category.Basic
open CategoryTheory



universe u v u2
def DepTypeFormer (C : Type u) [Category.{v}  C] [cwf: CwF C] : Type _ :=
  {Γ : C} → (S : Ty Γ) → (P : Ty (Γ ▹ S)) → Ty Γ

def DepSubCongr {C : Type u} [Category.{v}  C] [cwf: CwF C] (X : DepTypeFormer C) : Prop :=
  {Δ Γ : C} → {S : Ty Γ} → {P : Ty (Γ ▹ S)} → {θ : Δ ⟶ Γ }
    → (X S P)⦃θ⦄  = X S⦃θ⦄ P⦃wk θ⦄
