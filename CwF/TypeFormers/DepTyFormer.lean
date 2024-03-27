import CwF.Basics
import CwF.Properties


import Mathlib.CategoryTheory.Category.Basic


open CategoryTheory

namespace CwF

abbrev DepTypeFormer (C : Type u) [Category.{v'}  C] [cwf: CwF C] : Type _ :=
  {Γ : C} → (S : Ty Γ) → (P : Ty (Γ ▹ S)) → Ty Γ

abbrev DepSubCongr {C : Type u} [Category.{v'}  C] [cwf: CwF C] (X : DepTypeFormer C) : Prop :=
  {Δ Γ : C} → {S : Ty Γ} → {P : Ty (Γ ▹ S)} → {θ : Δ ⟶ Γ }
    → (X S P)⦃θ⦄  = X S⦃θ⦄ P⦃wk θ⦄


end CwF
