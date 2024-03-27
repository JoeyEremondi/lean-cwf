import CwF.Fam
import Mathlib.CategoryTheory.Category.Basic
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



class HasEmpty (C : Type u) [Category.{v'} C] [CwF C] : Type _ where
  Empty : Ty (C := C) ⬝
  exfalso : {Γ: C} → {T : Ty Γ} → Tm (Empty⦃‼⦄ : Ty Γ ) → Tm T

class HasEmptyEta (C : Type u) [Category.{v'} C] [CwF C] extends HasEmpty C : Type _ where
  ηEmpty : {Γ : C} → Subsingleton (Tm (Empty⦃‼⦄ : Ty Γ))




class HasUnit (C : Type u) [Category.{v'} C] [CwF C] : Type _ where
  Unit : Ty (C := C) ⬝
  unit : Tm Unit
  unitElim : {Γ : C} → {P : Ty (Γ▹Unit⦃‼⦄)} → {x : Tm (Unit⦃‼⦄ : Ty Γ)}
    → Tm P⦃unit⦃‼⦄⁻⦄  → Tm (P⦃x⁻⦄)


class HasUnitEta (C : Type u) [Category.{v'} C] [CwF C] extends HasUnit C : Type _ where
  ηUnit : {Γ : C} → Subsingleton (Tm (Unit⦃‼⦄ : Ty Γ))
