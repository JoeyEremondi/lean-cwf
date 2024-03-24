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

universe u v u2


class HasFalse (C : Type u) [Category.{v} C] [CwF C] : Type _ where
  False : Ty (C := C) ⬝
  exfalso : {Γ: C} → {T : Ty Γ} → Tm (False⦃‼⦄ : Ty Γ ) → Tm T



class HasTrue (C : Type u) [Category.{v} C] [CwF C] : Type _ where
  True : Ty (C := C) ⬝
  unit : Tm True
  unitElim : {Γ : C} → {P : Ty (Γ▹True⦃‼⦄)} → {x : Tm (True⦃‼⦄ : Ty Γ)}
    → Tm P⦃unit⦃‼⦄⁻⦄  → Tm (P⦃x⁻⦄)
