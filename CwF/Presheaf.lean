
import CwF.Fam
import CwF.CwFProperties
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.NatTrans
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Elements
import Mathlib.Data.Opposite
import Mathlib.CategoryTheory.Types



import CwF.CwF

open CategoryTheory

-- Pi type structure in a category with families


universe u v u₂
variable {C : Type u} [CCat : Category.{v}  C]

-- abbrev PShC : Type _ :=
--   Cᵒᵖ ⥤ Type u₂

-- def PshCat : Category.{max u u₂,max u v (u₂ + 1)} PShC  :=
--   @Functor.category (Cᵒᵖ) _ (Type u₂) _

-- A type is a presheaf over the elements of Γ
abbrev pshTy  (Γ : Cᵒᵖ ⥤ Type u₂) : Type (max u v (u₂ + 1)) :=
  Functor.Elements Γ ⥤ Type u₂

-- A term is a mapping from stages and its context's elements at that stage
-- to the type's elements at that stage and element
abbrev pshTm  (Γ : Cᵒᵖ ⥤ Type u₂) (T : pshTy Γ) : Type (max u v (u₂ + 1)) :=
  (i : Cᵒᵖ) -> (ρ : Γ.obj i) -> ULift.{max u v (u₂ + 1)} (T.obj ⟨i , ρ⟩)

def pshTySub {Γ Δ : Cᵒᵖ ⥤ Type u₂} (θ : Δ ⟶ Γ) (T : pshTy Γ) : pshTy Δ :=
  (CategoryOfElements.map θ) ⋙ T

def pshTmSub {Γ Δ : Cᵒᵖ ⥤ Type u₂} (θ : Δ ⟶ Γ) (T : pshTy Γ) (t : pshTm Γ T) :
  pshTm Δ (pshTySub θ T) := (fun i => fun δ =>
    t i (θ.app i δ))



def pshTmTy : (Cᵒᵖ ⥤ Type u₂)ᵒᵖ ⥤ ArrFam where
  obj
  | ⟨ Γ ⟩ => mkFam
    (pshTy Γ)
    (pshTm Γ)

  map := @fun ⟨X⟩ ⟨Y⟩ ⟨ θ ⟩  =>
    unmapFam
      (pshTySub θ)
      (@fun T x => by
        simp_all [ixSet, mkFam]
        simp at x
        let ret := pshTmSub θ T
        )
  -- by
  --   simp_all
  --   intros
  --   fapply unmapFam
  --   . intros a
  --     apply pshTySub
  --     simp [ixSet] at a
  --     simp [mkFam] at a
  --     simp [pshTy] at a
  --     let θa := θ.app a
  --   . intros

  map_id := by admit

  map_comp := by admit


--   map θ := _

--   map_id := by admit

--   map_comp := by admit

-- instance : TmTy (Cᵒᵖ ⥤ Type u₂) where
--   F := by
--     _
