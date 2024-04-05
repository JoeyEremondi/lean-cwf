
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

import Mathlib.CategoryTheory.Sites.Coverage
import Mathlib.CategoryTheory.Sites.Canonical
import Mathlib.CategoryTheory.Sites.Grothendieck
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.CategoryTheory.Sites.Sieves
import Mathlib.CategoryTheory.Sites.SheafOfTypes

import Mathlib.Tactic

import Mathlib.Order.GaloisConnection

open CategoryTheory


namespace CwF

--TODO: phrase as coverages without pullbacks?
--The assumption here is that we're working in a presheaf or sheaf CwF, so
--we have all pullbacks.
--The term model doesn't have all pullbacks without extensional equality, but it
--also doesn't have proper coverages without extensional equality, so we don't use this to define its
--pattern matching semantics anyways.
variable {C : Type u} [cat : Category.{v'}  C] [cwf: CwF C] [Limits.HasPullbacks C]



-- A slice of the canonical topology is subcanonical
def canonicalSlice (Γ : C) : Sheaf.Subcanonical (GrothendieckTopology.over (Sheaf.canonicalTopology C) Γ) := by
  apply Sheaf.Subcanonical.of_yoneda_isSheaf
  intros X
  simp [Presieve.IsSheaf]
  intros Y sieve isCover
  let ysieve := ((Sieve.overEquiv Y).toFun sieve)
  let lem := GrothendieckTopology.mem_over_iff (Sheaf.canonicalTopology C) (X := Γ) (Y := X)
  admit

-- Turn a presieve in the slice into one in the base category
def forgetOverPresieve {Γ : C} {θ : Over Γ} (R : Presieve θ)
  : Presieve θ.left :=  @fun Δ =>
        ⨆ f, Set.image CommaMorphism.left (@R (Over.mk f))

def toSlicePresieve {Γ : C} (θ : Over Γ) (R : Presieve θ.left)
  : Presieve θ := @fun Δi => {f | f.left ∈ @R Δi.left}
-- Without the sieve condition, we don't have equivalence between
-- a presieve in the over-category and its forgetful version, e.g. because it could
-- be partitioned more finely in the over-category based on what morphism
-- we're factoring through
-- TODO explain better
def forgetOverMem {Γ : C} {θ : Over Γ} (R : Presieve θ) (f : Over Γ) (g : f ⟶ θ)
  : g ∈ (@R f) → g.left ∈ @forgetOverPresieve _ _ _ _ R f.left := by
    simp [forgetOverPresieve]
    intros H
    exists (f.hom)
    exists g

-- def forgetOverId {Γ Δ : C} {θ : Over Γ} (R : Presieve θ) (g : Δ ⟶ θ.left)
--   :  g ∈ @forgetOverPresieve _ _ _ _  R Δ → (Over.homMk g (by simp)) ∈ (@R (Over.mk (𝟙 Γ))) := by
--     simp

def canonicalCoverage := Coverage.ofGrothendieck C (Sheaf.canonicalTopology C)

--Every representable is a sheaf for any cover in the canonical coverage
def coverage_isSheaf_yondea_obj
  {Γ : C} {R : Presieve Γ} (mem : R ∈ canonicalCoverage.covering Γ) (Δ : C)
  : Presieve.IsSheafFor (yoneda.obj Δ) R := by
    let gi_eq := GaloisInsertion.l_u_eq (Coverage.gi C) (Sheaf.canonicalTopology C)
    let ⟨toLem , _⟩ := (Presieve.isSheaf_coverage canonicalCoverage (yoneda.obj Δ))
    apply toLem
    dsimp only [canonicalCoverage]
    rw [gi_eq]
    apply Sheaf.isSheaf_yoneda_obj
    assumption


--We try to follow the notation/naming from Elephant C2.2.17, even though
--it doesn't quite match our usual stuff
def slicePreserveSubcanonical {Γ : C} (f : Over Γ)
  {R : Presieve f.left} (mem : R ∈ canonicalCoverage.covering f.left) {g : Over Γ}
  : Presieve.IsSheafFor (yoneda.obj g) (toSlicePresieve f R) :=
    by
      intros Xᵢ compat
      let baseFam :  Presieve.FamilyOfElements (yoneda.obj g.left) R :=
        fun _ k mem =>
          (Xᵢ (Y := Over.mk (k ≫ f.hom)) (Over.homMk k) mem).left
      let baseShf := coverage_isSheaf_yondea_obj mem
      let baseCompat : Presieve.FamilyOfElements.Compatible baseFam :=
        by admit
      let ⟨h, hAmalg, hUnique⟩ := baseShf _ baseFam baseCompat
      simp [Presieve.FamilyOfElements.IsAmalgamation] at h hAmalg hUnique
      let foo := @hAmalg
      simp at foo
      let hOver : f ⟶ g := Over.homMk h (by
        simp
        )



--If we can amalgamate along representables in the base category,
--we can in the slice category.
--Variable names try to match 2.2.17 from the Elephant
def amalgInSlice {Γ : C}  {R : Presieve Γ}
   (baseShf : ∀ {Δ}, Presieve.IsSheafFor (yoneda.obj Δ) R)
    {θ : Over Γ}
   : Presieve.IsSheafFor (yoneda.obj θ) (toSlicePresieve (Over.mk (𝟙 Γ)) R) := by
   intros Xᵢ compat
   simp [Presieve.IsSheafFor] at baseShf
   let baseFam :  Presieve.FamilyOfElements (yoneda.obj θ.left) R := by
      intros Δ f mem
      let x := Xᵢ (Y := Over.mk f) (Over.homMk f) mem
      let ret := x.left
      simp at ret
      exact ret
   let baseCompat : Presieve.FamilyOfElements.Compatible baseFam  := by
     admit
   let ⟨h , isAmalg, isUnique⟩ := baseShf baseFam baseCompat
   simp at  isAmalg isUnique
   fconstructor
   . fapply Over.homMk <;> simp
     . apply h
     . simp



def coverSlicePresieve {Γ : C} (cov : PatCover Γ) : Presieve (Over.mk (𝟙 Γ)) :=
  toSlicePresieve (Over.mk (𝟙 Γ)) (toPresieve cov)

def branchesToFam {Γ : C} {cov : PatCover Γ} {T : Ty Γ}
  (branches : MatchOn cov T)
  : Presieve.FamilyOfElements (yoneda.obj (tyToSlice T)) (coverSlicePresieve cov) := by
    intros Γᵢ θᵢ mem
    simp
    simp [coverSlicePresieve, toSlicePresieve, setOf] at mem
    simp [MatchOn] at branches
    apply termSliceEquiv'.toFun
    apply branches
    simp [Membership.mem, Set.Mem] at mem
    let eq := θᵢ.w
    simp at eq
    rw [eq] at mem
    rw [<- toPresieveEquiv'] at mem
    apply mem

-- class IsSubcanonical (coverage : Coverage (cat := cat)) : Type _ where

-- Relies on Axiom of choice. Alternately we can add an extra constraint that
-- the sheaf is constructive.
instance (coverage : CwF.PatCoverage (C := C))   : MatchWithCoverage coverage where
  -- Scratch work, just admit a bunch of stuff to find out what we need
  mkMatch {Γ} {T} cov inCov branches := by
    simp [MatchOn] at branches
    apply termSliceEquivId.invFun
    let isSheaf : Presieve.IsSheafFor (yoneda.obj (tyToSlice T)) (coverSlicePresieve cov) := by
      dsimp [coverSlicePresieve]
      apply amalgInSlice
    let compat : Presieve.FamilyOfElements.Compatible (branchesToFam branches) :=
      by admit
    let amalg := isSheaf (branchesToFam branches) compat
    apply Classical.choose amalg
