import Mathlib.CategoryTheory.Comma.Arrow
import Mathlib.CategoryTheory.Types
import Mathlib.CategoryTheory.Comma.Over
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.Data.Opposite
import Mathlib.CategoryTheory.Equivalence


open CategoryTheory
open Opposite


-- universe  u

-- Objects of Fam are an indexing type
-- and a family of types indexed by it
abbrev TypeFam : Type (u + 1)
  := (A : Type u ) × (A -> Type u)


-- The category of Indexed Families
-- Arrows are index-respecting dependent functions
-- Composition and identity work pair-wise
instance famCat : LargeCategory.{u} TypeFam.{u} where
  Hom :=  fun
  | AB, AB' => (f : AB.fst -> AB'.fst) × ({a : AB.fst} -> AB.snd a -> AB'.snd (f a))

  id  := fun
  | ⟨ A , B⟩ => ⟨ id , id⟩

  comp := fun
  | ⟨fA , fB⟩, ⟨gA , gB⟩ => ⟨ gA ∘ fA , gB ∘ fB⟩


