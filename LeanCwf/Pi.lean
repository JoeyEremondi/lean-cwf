
import LeanCwf.Fam
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.Data.Opposite
import Mathlib.CategoryTheory.Limits.Shapes.Terminal


import LeanCwF.CwF
open CwF

open CategoryTheory

-- Pi type structure in a category with families


universe u v u2
variable {C : Type u} [Category.{v}  C] [TmTy.{u,v} C] [Limits.HasTerminal C] [CwF C]

class HasPi : Type _ where
  Pi : {Γ : C} → (S : Ty Γ) → (T : Ty (Γ ▹ S)) → Ty Γ
  -- lam : {Γ : C} → {S : Ty Γ} → {T : Ty (Γ ▹ S)} → Tm T → Tm (Pi S T)
  -- app : {Γ : C} → {S : Ty Γ} → {T : Ty (Γ ▹ S)} → (f : Tm (Pi S T)) → (x : Tm S) → Tm (T⦃x̂⦄)
