
import CwF.Fam
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Types
import Mathlib.CategoryTheory.Comma.Over
import Mathlib.Data.Opposite
import Mathlib.CategoryTheory.Limits.Shapes.Terminal


import CwF.Basics
import CwF.Properties
import CwF.TypeFormers.DepTyFormer

import Mathlib.CategoryTheory.EpiMono

import Mathlib.Data.Multiset.Basic

import CwF.Matching.Defs

import Mathlib.CategoryTheory.Sites.Pretopology
import Mathlib.CategoryTheory.Sites.Canonical
import Mathlib.CategoryTheory.Sites.Grothendieck

import Mathlib.Tactic

open CategoryTheory


namespace CwF

--TODO: phrase as coverages without pullbacks?
--The assumption here is that we're working in a presheaf or sheaf CwF, so
--we have all pullbacks.
--The term model doesn't have all pullbacks without extensional equality, but it
--also doesn't have proper coverages without extensional equality, so we don't use this to define its
--pattern matching semantics anyways.
variable {C : Type u} [cat : Category.{v'}  C] [cwf: CwF C] [Limits.HasPullbacks C]


def underlyingSieve {Γ Δ : C} (θ : Δ ⟶ Γ) (sieve : Sieve (Over.mk θ)) : Sieve Δ where
  arrows Ξ f := ∃ (g : Ξ ⟶ Γ), ∃ (fOver : Over.mk g  ⟶ Over.mk θ) , sieve.arrows fOver ∧ fOver.left = f
  downward_closed {Ξ} {Ξ'} f pf g := by
    simp_all
    rcases pf with ⟨gg, fOver, arrs, eq⟩
    -- rcases fOver with ⟨f, rt , eq2⟩
    cases eq
    let eq2 := fOver.w
    simp at eq2
    -- simp at eq2
    fconstructor
    . apply (g ≫ gg)
    . fapply Exists.intro
      . fapply Over.homMk
        . apply (g ≫ fOver.left)
        . simp
          apply congrArg (fun x => g ≫ x)
          assumption
      . simp
        let foo := sieve.downward_closed (Z := Over.mk (g ≫ gg)) arrs
        apply sieve.downward_closed arrs

def canonicalSlice (Γ : C) : GrothendieckTopology (Over Γ) where
  sieves
  | ⟨Δ , _ ,  θ⟩ , sieve =>
    let lifted : Sieve Δ := {
      arrows := fun Ξ f => sieve.arrows (Over.homMk f (by simp))
    }
    lifted ∈ ((Sheaf.canonicalTopology C).sieves Δ)

def canonicalPretopology := Pretopology.ofGrothendieck C (Sheaf.canonicalTopology C)

class IsSubcanonical (coverage : Coverage (cat := cat)) : Type _ where
