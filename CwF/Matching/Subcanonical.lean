
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


namespace GrothendieckTopology

def baseFamily {U V W : C} {f : V ⟶ U} {g : W ⟶ U}
  (R : Sieve (Over.mk f))
  (hₖs : Presieve.FamilyOfElements (yoneda.obj (Over.mk g)) R.arrows)
  : Presieve.FamilyOfElements (C := C)
      (yoneda.obj W)
      (Sieve.overEquiv (Over.mk f) R).arrows
    := by
      intros k hk in_hₖs
      let inR := (Sieve.overEquiv_iff R hk).mp in_hₖs
      let sliceArrow := hₖs _ inR
      apply sliceArrow.left

  def baseArrowsIff {U V : C} {f : V ⟶ U}
  (R : Sieve (Over.mk f : Over U))
  {Y : Over U}
  (θ : Y ⟶ Over.mk f)
  : R.arrows θ ↔ (Sieve.overEquiv (Over.mk f) R) θ.left := by
    have unfld :  R.arrows = (Sieve.overEquiv (Over.mk f)).symm (Sieve.overEquiv (Over.mk f) R) := by aesop
    rw [unfld]
    apply Sieve.overEquiv_symm_iff

  def baseFamilyCompat {U V W : C} {f : V ⟶ U} {g : W ⟶ U}
    (R : Sieve (Over.mk f))
    {hₖs : Presieve.FamilyOfElements (yoneda.obj (Over.mk g)) R.arrows}
    (compat : Presieve.FamilyOfElements.Compatible hₖs)
    : Presieve.FamilyOfElements.Compatible (baseFamily R hₖs) := by
    intros Ξ1 Ξ2 Δ g1 g2 f1 f2 inBase1 inBase2 eq
    simp
    simp at f1 f2
    let foo :=  baseFamily R hₖs f1 inBase1
    let inR1 := (Sieve.overEquiv_iff R _).mp inBase1
    let inR2 := (Sieve.overEquiv_iff R _).mp inBase2
    simp at foo
    admit
    -- simp [Presieve.FamilyOfElements.Compatible] at compat f1 f2
    -- let eqf : (g1 ≫ f1 ≫ f) = (g2 ≫ f2 ≫ f) := by
    --   let pf := congrArg (fun x => x ≫ f) eq
    --   simp at pf
    --   apply pf
    -- let Δarr : Over U := Over.mk (Y := Δ) (g1 ≫ f1 ≫ f)
    -- let Ξarr1 : Over U := Over.mk (Y := Ξ1) (f1 ≫ f)
    -- let Ξarr2 : Over U := Over.mk (Y := Ξ2) (f2 ≫ f)
    -- let g1' : Δarr ⟶ Ξarr1 := Over.homMk g1
    -- let g2' : Δarr ⟶ Ξarr2 := by
    --   simp
    --   rw [eqf]
    --   apply Over.homMk _ _ <;> simp
    --   . apply g2
    --   . simp
    -- let foo := compat g1' g2' inR1 inR2 (by admit)
      -- (by
      --   simp
      --   apply Over.OverMorphism.ext
      --   apply Eq.trans eq
      --   simp
      --   apply congrArg (fun x => x ≫ f2)
      --   admit
      --   )
      --

   def overAmalgFactor
   {U V W : C} {f : V ⟶ U}  {g : W ⟶ U} {h : V ⟶ W}
    (R : Sieve (Over.mk f))
    {hₖs : Presieve.FamilyOfElements (yoneda.obj (Over.mk g)) R.arrows}
     (isAmalg : Presieve.FamilyOfElements.IsAmalgamation (baseFamily R hₖs) h )
     (compat : Presieve.FamilyOfElements.Compatible hₖs)
     (isSheaf : Presieve.IsSheafFor (yoneda.obj U) (Sieve.overEquiv (Over.mk f) R).arrows )
     : h ≫ g = f := by
       let fₖs
         : Presieve.FamilyOfElements (yoneda.obj U) (Sieve.overEquiv (Over.mk f) R).arrows :=
           Presieve.FamilyOfElements.compPresheafMap (yoneda.map g) (baseFamily R hₖs)
       let fCompat :=
         Presieve.FamilyOfElements.Compatible.compPresheafMap (yoneda.map g) (baseFamilyCompat R compat)
       have ⟨f', f'Amalg, uniq⟩ : ∃! t, Presieve.FamilyOfElements.IsAmalgamation fₖs t :=
         isSheaf fₖs fCompat
       have hgAmalg : Presieve.FamilyOfElements.IsAmalgamation fₖs (h ≫ g)  := by
         intros X θ inR
         let hAmalg := isAmalg θ inR
         simp [baseFamily] at hAmalg
         simp [Presieve.FamilyOfElements.compPresheafMap, baseFamily]
         rw [<- hAmalg]
         simp
       have fAmalg : Presieve.FamilyOfElements.IsAmalgamation fₖs f  := by
         intros X θ inR
         let hAmalg := isAmalg θ inR
         simp [Presieve.FamilyOfElements.compPresheafMap, baseFamily]
       simp [Presieve.FamilyOfElements.IsAmalgamation, Sieve.overEquiv, Presieve.functorPushforward, baseFamily] at isAmalg



   def transferArrows {U V : C} {f : V ⟶ U} {Y : Over U} {g : Y.left ⟶ V} {pf1 pf2 : g ≫ f = Y.hom} (R : Sieve (Over.mk f)) (inR : R.arrows (Over.homMk g pf1))
     : R.arrows (Over.homMk g pf2) := by
       apply inR

   def famLeft {U V W : C} {f : V ⟶ U}  {g : W ⟶ U}
    (R : Sieve (Over.mk f))
    {hₖs : Presieve.FamilyOfElements (yoneda.obj (Over.mk g)) R.arrows}
    {Y : Over U}
    {θ1 θ2 : Y ⟶ Over.mk f}
    {in1 : R.arrows θ1}
    {in2 : R.arrows θ2}
    (eq : (hₖs θ1 in1) = (hₖs θ2 in2))
    : (hₖs θ1 in1).left = (hₖs θ2 in2).left := by aesop



   def overPreserveAmalg {U V W : C}  {g : W ⟶ U} {h : V ⟶ W}
    (R : Sieve (Over.mk (h ≫ g)))
    {hₖs : Presieve.FamilyOfElements (yoneda.obj (Over.mk g)) R.arrows}
     (isAmalg : Presieve.FamilyOfElements.IsAmalgamation (baseFamily R hₖs) h )
     : Presieve.FamilyOfElements.IsAmalgamation hₖs (Over.homMk h) := by
       simp [Presieve.FamilyOfElements.IsAmalgamation, baseFamily] at isAmalg
       simp [Presieve.FamilyOfElements.IsAmalgamation, baseFamily]
       intros Y θ inR
       let inRbase := (baseArrowsIff R θ).mp inR
       let lem := isAmalg θ.left inRbase
       apply Over.OverMorphism.ext
       simp
       apply Eq.trans lem
       have θeq : ∀ {pf}, Over.homMk θ.left pf = θ := by
         let ⟨θ , rt, eq⟩ := θ
         simp [Over.homMk, CostructuredArrow.homMk]
         have eq {x : _} :  x = rt := by aesop_cat
         simp [eq]
       have arrEq {p1} {p2} : (hₖs (Over.homMk θ.left p1) p2) = (hₖs θ inR) := by
         let ⟨θ , rt, eq⟩ := θ
         have rteq {x : _} :  x = rt := by aesop_cat
         simp [Over.homMk, CostructuredArrow.homMk]
         rfl
       apply @famLeft _ _ U V W (h ≫ g) g R hₖs Y _ _ _ inR  arrEq
       reduce
       rw [arrEq]


def subcanonicalSlice {J : GrothendieckTopology C}
  (issub : Sheaf.Subcanonical J )
  : Sheaf.Subcanonical (GrothendieckTopology.over J U) := by
  apply Sheaf.Subcanonical.of_yoneda_isSheaf
  let allBaseReprSheaf := Sheaf.Subcanonical.isSheaf_of_representable issub
  intros X
  let ⟨W, _, g⟩ := X
  simp at g
  simp [Presieve.IsSheaf]
  intros Y R Rcover
  let ⟨V, _, f⟩ := Y
  simp at f
  -- let lem := GrothendieckTopology.mem_over_iff J (X := U) (Y := Y)
  intros hₖs compat
  simp [Presieve.FamilyOfElements, Presieve.FamilyOfElements.Compatible] at hₖs compat
  -- Construct a family of elements in the base category for yoneda X
  let xs' := baseFamily R hₖs
    -- This family is compatible
  have compat' : Presieve.FamilyOfElements.Compatible xs' :=
    baseFamilyCompat R compat
  -- Base site is subcanonical, so we can amalgamate the family
  have ⟨h, isAmalg, uniq⟩ : ∃! t, Presieve.FamilyOfElements.IsAmalgamation xs' t := by
    apply allBaseReprSheaf
    apply Iff.mp
    apply GrothendieckTopology.mem_over_iff J (X := U) (Y := Over.mk f)
    apply Rcover
    apply compat'
  simp at h isAmalg uniq
  simp [Presieve.FamilyOfElements.IsAmalgamation] at isAmalg
  let h' : Over.mk f ⟶ Over.mk g := Over.homMk h (by
    simp
    admit
    )
  exists h'
  simp
  fconstructor
  . simp
    simp [Presieve.FamilyOfElements.IsAmalgamation]
    intros θ σ σinR
    apply Over.OverMorphism.ext
    simp
    have rew : σ = Over.homMk σ.left (by let w := σ.w ; simp at w ; apply w) := by
      cases σ
      simp [Over.homMk, CostructuredArrow.homMk]
      apply CommaMorphism.ext
      simp
      rfl
    rw [rew] at σinR
    -- cases σ
    let inR' := (Sieve.overEquiv_iff R σ.left).mpr
    -- let ⟨arr , _ , pf⟩ := σ
    simp  at inR'
    let inR := inR' (by admit)
    let baseAmalg := isAmalg σ.left (by admit)
    apply Eq.trans baseAmalg
    simp [baseFamily]
    let foo := (hₖs σ σinR)
    rfl
  . simp


  exists amalg

  admit
end GrothendieckTopology


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

theorem canonicalCoverageGenerate {Γ : C} (R : Presieve Γ)
  (mem : R ∈ canonicalCoverage.covering Γ)
  : Sieve.generate R ∈ (Sheaf.canonicalTopology C).sieves Γ :=
    (Coverage.ofGrothendieck_iff (Sheaf.canonicalTopology C)).mp mem

theorem generateToSlice  {Γ : C} (θ : Over Γ) (R : Presieve θ.left) {Δi : Over Γ} {f : Δi ⟶ θ}
  : Sieve.generate (toSlicePresieve θ R) f ↔ toSlicePresieve θ (Sieve.generate R).arrows f :=
  by
    simp [toSlicePresieve, setOf]
    fconstructor <;> intros H
    . choose Y h g mem eq using H
      cases eq
      reduce
      aesop_cat
    . simp at H
      choose Y h g mem eq using H
      cases eq
      reduce
      apply H
      aesop_cat
      
    aesop_cat

-- Helper lemma between sieves and covers
def helperCompose
  {R : Presieve Γ} (mem : R ∈ canonicalCoverage.covering Γ)

--We try to follow the notation/naming from Elephant C2.2.17, even though
--it doesn't quite match our usual stuff
def slicePreserveSubcanonical {Γ : C} (f : Over Γ)
  {R : Presieve f.left} (mem : R ∈ canonicalCoverage.covering f.left) {g : Over Γ}
  : Presieve.IsSheafFor (yoneda.obj g) (toSlicePresieve f R) :=
    by
      intros Xᵢ compat
      let Xsieve : Presieve.FamilyOfElements
        (yoneda.toPrefunctor.obj g)
        (Sieve.generate (toSlicePresieve f R)).arrows := by
        intros θ fθ mem
        rw [Sieve.generate_apply] at mem
        -- Uses choice, since sieve stuff is not constructive
        -- TODO document
        choose Mid left right mem' eq using mem
        let retPart := Xᵢ _ mem'
        simp at retPart
        simp
        cases eq
        apply (left ≫ retPart)
      let baseFam :  Presieve.FamilyOfElements (yoneda.obj g.left) (Sieve.generate R).arrows :=
        fun _ k mem =>
          (Xsieve (Y := Over.mk (k ≫ f.hom)) (Over.homMk k) (by dsimp only)).left
      let baseShf := Sheaf.isSheaf_yoneda_obj (Sheaf.canonicalTopology C)
      -- coverage_isSheaf_yondea_obj mem
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
