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

open CategoryTheory

-- Pi type structure in a category with families


namespace CwF


variable {C : Type u} [cat : Category.{v'}  C] [cwf: CwF C]

-- A cover is a context (e.g. defining free pattern variables)
-- and a morphism, which defines
abbrev Cover (Γ : C) := List ((Δ : C) × (Δ ⟶ Γ))

-- We use a multiset so we don't have to prove uniqueness,
-- and since the pattern matching laws ensure that duplicate covers
-- don't make a difference anyways
abbrev Coverage := (Γ : C) → Set (Cover Γ)

--A simple match on a cover for a closed type T assigns each pattern in the cover
--a right-hand-side, which is an element of T that may refer to the free
--pattern variables of that cover
abbrev SimpleMatchOn {Γ : C} (cov : Cover Γ) (T : Ty (cwf.empty)) :=
  ∀ Δθ, List.Mem Δθ cov → Tm (T⦃⟨⟩Δθ.fst⦄)


--A dependent match on a Γ-cover for a type T (defined over variables of Γ)
--assigns, to each pattern in the cover,
--a right-hand-side, which is an element of T with the Γ variables
--replaced by Δ-variables according to the pattern θ
abbrev MatchOn {Γ : C} (cov : Cover Γ) (T : Ty Γ) : Type _ :=
  ∀ {Δθ}, Δθ ∈ cov → Tm (T⦃Δθ.snd⦄)




class MatchWithCoverage (coverage : Coverage (cat := cat)) : Type _ where
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
    : (mkMatch isCover branches)⦃Δθ.snd⦄ = branches pos
