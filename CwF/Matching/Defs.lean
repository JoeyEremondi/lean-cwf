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

import Mathlib.Data.Multiset.Basic
import Mathlib.CategoryTheory.Sites.Sieves

open CategoryTheory

-- Pi type structure in a category with families


namespace CwF


variable {C : Type u} [cat : Category.{v'}  C] [cwf: CwF C]

-- A cover is a list of patterns containing a context (e.g. defining free pattern variables)
-- and a morphism, which defines how to map those variables into the covered context Γ.
-- Note that a pair (Δ : C × Δ ⟶ Γ ) is just a member of C/Γ,
-- which is also a finite Presieve over Γ
abbrev PatCover (Γ : C) := List (Over Γ)

-- Each cover can be treated as a presieve, like Sites.Coverage uses
def toPresieve {Γ : C} (c : PatCover Γ) : Presieve Γ := @fun _ =>
  {f | Over.mk f ∈ c }

theorem toPresieveEquiv {Γ : C} (c : PatCover Γ) {Δ : C} {f : Δ ⟶ Γ}
  : (Over.mk f) ∈ c ↔ toPresieve c f  := by aesop


theorem toPresieveEquiv' {Γ : C} (c : PatCover Γ)  {f : Over Γ}
  : f ∈ c ↔ toPresieve c f.hom  := by aesop

-- We use a multiset so we don't have to prove uniqueness,
-- and since the pattern matching laws ensure that duplicate covers
-- don't make a difference anyways
abbrev PatCoverage := (Γ : C) → Set (PatCover Γ)

--A simple match on a cover for a closed type T assigns each pattern in the cover
--a right-hand-side, which is an element of T that may refer to the free
--pattern variables of that cover
abbrev SimpleMatchOn {Γ : C} (cov : PatCover Γ) (T : Ty (cwf.empty)) :=
  ∀ Δθ, List.Mem Δθ cov → Tm (T⦃⟨⟩Δθ.left⦄)


--A dependent match on a Γ-cover for a type T (defined over variables of Γ)
--assigns, to each pattern in the cover,
--a right-hand-side, which is an element of T with the Γ variables
--replaced by Δ-variables according to the pattern θ
abbrev MatchOn {Γ : C} (cov : PatCover Γ) (T : Ty Γ) : Type _ :=
  ∀ {Δθ}, Δθ ∈ cov → Tm (T⦃Δθ.hom⦄)




class MatchWithCoverage (coverage : PatCoverage (cat := cat)) : Type _ where
 -- There is a term corresponding to each match on a cover in a coverage
  mkMatch : ∀ {Γ : C} {T : Ty Γ}, ∀ {cov}, (cov ∈ (coverage Γ)) →
    MatchOn cov T → Tm T

 -- Note that this assumes we have agreement on duplicates in the patterns, so
 -- it really only assigns semantics to non-overlapping patterns.
  matchesBranch  {Γ : C} {T : Ty Γ} {cov}
    (isCover : cov ∈ (coverage Γ))
    {Δθ}
    (pos : Δθ ∈ cov)
    (branches : MatchOn cov T)
    : (mkMatch isCover branches)⦃Δθ.hom⦄ = branches pos
