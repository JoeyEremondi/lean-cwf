
import CwF.Fam
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Types
import Mathlib.Data.Opposite
import Mathlib.CategoryTheory.Limits.Shapes.Terminal


import CwF.Basics
import CwF.Properties
import CwF.TypeFormers.DepTyFormer

import Mathlib.CategoryTheory.EpiMono

open CategoryTheory

-- Pi type structure in a category with families


namespace CwF

class HasExtEq (C : Type u) [Category.{v'} C] [CwF C] : Type _ where
  EEq {Γ : C} {T : Ty Γ} : Ty ((Γ ▹ T)▹ T⦃p⦄)
  refl {Γ : C} {T : Ty Γ} {t : Tm T} : Tm (EEq⦃(t⦃p⦄)⁻⦄⦃t⁻⦄)
  elim {Γ : C} {T : Ty Γ} {s t : Tm T} : Tm (EEq⦃(t⦃p⦄)⁻⦄⦃s⁻⦄) → s = t
