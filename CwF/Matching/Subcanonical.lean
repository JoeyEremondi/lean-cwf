
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
variable {C : Type u} [cat : Category.{v'}  C] [cwf: CwF C] -- [Limits.HasPullbacks C]

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
    let inR1 := (Sieve.overEquiv_iff R _).mp inBase1
    let inR2 := (Sieve.overEquiv_iff R _).mp inBase2
    let Ξ1' := Over.mk (f1 ≫ f)
    let Ξ2' := Over.mk (f2 ≫ f)
    let Δ' := Over.mk (g1 ≫ f1 ≫ f)
    have inSlice2 : g2 ≫ Ξ2'.hom = Δ'.hom := by
      simp
      rw [<- Category.assoc]
      rw [<- eq]
      simp
    let lem :=
      @compat Ξ1' Ξ2' Δ' (Over.homMk g1) (Over.homMk g2 inSlice2) _ _ inR1 inR2
      (by apply Over.OverMorphism.ext ; simp ; apply eq)
    simp at lem
    let lemCongr := congrArg (fun x => x.left) lem
    simp at lemCongr
    apply lemCongr


   def overAmalgFactor
   {U V W : C} {f : V ⟶ U}  {g : W ⟶ U} {h : V ⟶ W}
    (R : Sieve (Over.mk f))
    {hₖs : Presieve.FamilyOfElements (yoneda.obj (Over.mk g)) R.arrows}
     (isAmalg : Presieve.FamilyOfElements.IsAmalgamation (baseFamily R hₖs) h )
     (isSheaf : Presieve.IsSheafFor (yoneda.obj U) (Sieve.overEquiv (Over.mk f) R).arrows )
     : h ≫ g = f := by
       let fₖs
         : Presieve.FamilyOfElements (yoneda.obj U) (Sieve.overEquiv (Over.mk f) R).arrows :=
           fun _ θ _ => θ ≫ f
       let fCompat : Presieve.FamilyOfElements.Compatible fₖs := by
         intros _ _ _ g1 g2 _ _ inR1 inR2 eq
         simp
         rw [<- Category.assoc]
         aesop_cat
       let hgₖs
         : Presieve.FamilyOfElements (yoneda.obj U) (Sieve.overEquiv (Over.mk f) R).arrows :=
           fun _ θ _ => θ ≫ h ≫ g
       have eq : fₖs  = hgₖs := by
         funext X θ inR
         simp at inR
         simp
         let hₖ := hₖs _ ((Sieve.overEquiv_iff R θ).mp inR)
         let pf := hₖ.w
         simp at pf
         simp [<- pf]
         rw [<- Category.assoc]
         apply congrArg (fun x => x ≫ g)
         symm
         apply isAmalg _ inR
       have ⟨f', _, uniq⟩ : ∃! t, Presieve.FamilyOfElements.IsAmalgamation fₖs t :=
         isSheaf fₖs fCompat
       have hgAmalg : Presieve.FamilyOfElements.IsAmalgamation fₖs (h ≫ g)  := by
         rw [eq]
         intros X θ inR
         let hAmalg := isAmalg θ inR
         simp [baseFamily] at hAmalg
         simp [Presieve.FamilyOfElements.compPresheafMap, baseFamily]
       have fAmalg : Presieve.FamilyOfElements.IsAmalgamation fₖs f  := by
         intros X θ _
         simp
       let feq := uniq _ fAmalg
       let hgeq := uniq _ hgAmalg
       simp [feq, hgeq]



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


   def overPreserveAmalgSame {U V W : C}  {g : W ⟶ U} {h : V ⟶ W}
    (R : Sieve (Over.mk (h ≫ g)))
    {hₖs : Presieve.FamilyOfElements (yoneda.obj (Over.mk g)) R.arrows}
     (isAmalg : Presieve.FamilyOfElements.IsAmalgamation (baseFamily R hₖs) h )
     : Presieve.FamilyOfElements.IsAmalgamation hₖs (Over.homMk h) := by
       simp [Presieve.FamilyOfElements.IsAmalgamation, baseFamily] at isAmalg
       simp [Presieve.FamilyOfElements.IsAmalgamation, baseFamily]
       intros Y θ inR
       simp_all [Over.homMk, CostructuredArrow.homMk]
       let ⟨θ, rt, eq⟩ := θ
       let inRbase := (baseArrowsIff R _).mp inR
       let lem := isAmalg θ inRbase
       apply Over.OverMorphism.ext
       simp
       apply Eq.trans lem
       congr!
       cases Y
       simp [Over.mk, CostructuredArrow.mk]
       simp at eq
       apply eq


   def overPreserveAmalg {U V W : C} {f : V ⟶ U}  {g : W ⟶ U} {h : V ⟶ W}
    (R : Sieve (Over.mk f))
    {hₖs : Presieve.FamilyOfElements (yoneda.obj (Over.mk g)) R.arrows}
     (isAmalg : Presieve.FamilyOfElements.IsAmalgamation (baseFamily R hₖs) h )
     (eq : f = h ≫ g)
     : Presieve.FamilyOfElements.IsAmalgamation hₖs (Over.homMk h) := by
       cases eq
       apply overPreserveAmalgSame R isAmalg

   def basePreserveAmalg {U V W : C} {f : V ⟶ U}  {g : W ⟶ U} {h : V ⟶ W}
    (R : Sieve (Over.mk f))
    {hₖs : Presieve.FamilyOfElements (yoneda.obj (Over.mk g)) R.arrows}
     (eq : h ≫ g = f)
     (isAmalg : Presieve.FamilyOfElements.IsAmalgamation hₖs (Over.homMk h))
     : Presieve.FamilyOfElements.IsAmalgamation (baseFamily R hₖs) h  := by
       cases eq
       intros X θ inR
       simp at θ
       simp [baseFamily]
       let lem := @isAmalg (Over.mk (θ ≫ h ≫ g)) (Over.homMk θ) ((baseArrowsIff R _).mpr inR)
       simp at lem
       apply congrArg (fun x => x.left) lem

def subcanonicalSlice {J : GrothendieckTopology C}
  (issub : Sheaf.Subcanonical J )
  : Sheaf.Subcanonical (GrothendieckTopology.over J U) := by
  apply Sheaf.Subcanonical.of_yoneda_isSheaf
  let allBaseReprSheaf := Sheaf.Subcanonical.isSheaf_of_representable issub
  intros X Y R Rcover hₖs compat
  let baseFam := baseFamily R hₖs
  let baseCompat := baseFamilyCompat R compat
  let Jbase := Sieve.overEquiv _ R
  let JbaseCover := (GrothendieckTopology.mem_over_iff J R).mp Rcover
  -- let sieveIn : (Sieve.overEquiv Y) R ∈ J.sieves Y.left := by
  --   let lem := GrothendieckTopology.mem_over_iff J R
  --   apply lem.mp Rcover
  let ⟨h, hAmalg, hUniq⟩ :=
    allBaseReprSheaf
      (yoneda.obj X.left)
      Jbase
      JbaseCover
      baseFam
      baseCompat
  simp at h hAmalg hUniq
  let V := Y.left
  let W := X.left
  let f := Y.hom
  let g := X.hom
  let eqY : Y = Over.mk f := by aesop
  let eqX : X = Over.mk g := by aesop
  cases eqX
  cases eqY
  simp at f g V W hₖs compat baseFam baseCompat
  have hgfeq : h ≫ g = f :=
    overAmalgFactor R hAmalg (allBaseReprSheaf _ _ Rcover)
  fconstructor <;> simp
  . apply Over.homMk h hgfeq
  . fconstructor
    -- It's an amalgamation for the slice
    . apply overPreserveAmalg _ hAmalg hgfeq.symm
    -- The amalgamation is unique
    . intros t isAmalg
      let ⟨t , _ , eq⟩ := t
      simp at eq
      simp [Over.homMk, CostructuredArrow.homMk]
      apply CommaMorphism.ext
      simp
      apply hUniq
      fapply basePreserveAmalg _ eq isAmalg
      simp
      aesop

end GrothendieckTopology


-- Turn a presieve in the slice into one in the base category
def forgetOverPresieve {Γ : C} {θ : Over Γ} (R : Presieve θ)
  : Presieve θ.left :=  @fun _ =>
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
-- def coverage_isSheaf_yondea_obj
--   {Γ : C} {R : Presieve Γ} (mem : R ∈ canonicalCoverage.covering Γ) (Δ : C)
--   : Presieve.IsSheafFor (yoneda.obj Δ) R := by
--     let gi_eq := GaloisInsertion.l_u_eq (Coverage.gi C) (Sheaf.canonicalTopology C)
--     let ⟨toLem , _⟩ := (Presieve.isSheaf_coverage canonicalCoverage (yoneda.obj Δ))
--     apply toLem
--     dsimp only [canonicalCoverage]
--     rw [gi_eq]
--     apply Sheaf.isSheaf_yoneda_obj
--     assumption

theorem canonicalCoverageGenerate {Γ : C} (R : Presieve Γ)
  (mem : R ∈ canonicalCoverage.covering Γ)
  : Sieve.generate R ∈ (Sheaf.canonicalTopology C).sieves Γ :=
    (Coverage.ofGrothendieck_iff (Sheaf.canonicalTopology C)).mp mem


-- theorem generateToSlice  {Γ : C} (θ : Over Γ) (R : Presieve θ.left) {Δi : Over Γ} {f : Δi ⟶ θ}
--   : Sieve.generate (toSlicePresieve θ R) f ↔ toSlicePresieve θ (Sieve.generate R).arrows f :=
--   by
--     simp [toSlicePresieve, setOf]
--     fconstructor <;> intros H
--     . choose Y h g mem eq using H
--       cases eq
--       reduce
--       aesop_cat
--     . simp at H
--       choose Y h g mem eq using H
--       admit









def coverSlicePresieve {Γ : C} (cov : PatCover Γ) : Presieve (Over.mk (𝟙 Γ)) :=
  toSlicePresieve (Over.mk (𝟙 Γ)) (toPresieve cov)

theorem generateEquiv {Γ : C} {cov : PatCover Γ} :
  Sieve.generate (coverSlicePresieve cov)  = (Sieve.overEquiv (Over.mk (𝟙 Γ))).symm (Sieve.generate (toPresieve cov )) := by
    simp [coverSlicePresieve, toSlicePresieve, toPresieve]
    ext
    constructor <;> simp <;> try aesop_cat
    . intros X f g isCover eq
      cases eq
      simp [toSlicePresieve, setOf] at isCover
      let lem := Sieve.overEquiv_symm_iff (Y := Over.mk (𝟙 Γ)) (Sieve.generate (toPresieve cov)) (f ≫ g)
      apply lem.mpr
      apply Sieve.downward_closed
      apply Sieve.le_generate
      apply isCover
    . intros inCov
      simp [toSlicePresieve, setOf]
      rename_i f
      let lem := Sieve.overEquiv_symm_iff (Y := Over.mk (𝟙 Γ)) (Sieve.generate (toPresieve cov)) f
      let lem' := lem.mp inCov
      let ⟨Y' , h , g, gInCov, eq⟩ := lem'
      let feq := f.w
      simp at feq
      exists (Over.mk g)
      exists (Over.homMk h )
      exists (Over.homMk g)
      constructor <;> aesop_cat


class IsSubcanonicalPatCoverage (coverage : CwF.PatCoverage (C := C)) where
  inCanonical {Γ : C} {cov : PatCover Γ} (isCover : cov ∈ coverage Γ )
    : (canonicalCoverage (C := C)).covering Γ (toPresieve cov)
  disjoint {Γ : C} {cov : PatCover Γ} (isCover : cov ∈ coverage Γ)
    {pat1 : Over Γ} (pos1 : pat1 ∈ cov)
    {pat2 : Over Γ} (pos2 : pat2 ∈ cov)
        : ∀ {X} {g1 : X ⟶ pat1.left } {g2 : X ⟶ pat2.left},
        g1 ≫ pat1.hom = g2 ≫ pat2.hom → pat1 = pat2 ∧ HEq pos1 pos2
  nonOverlapping {Γ : C} {cov : PatCover Γ} (isCover : cov ∈ coverage Γ)
    {pat : Over Γ} (pos : pat ∈ cov)
    : Mono (pat.hom)


def subcanonicalPatSliceCover
  [subcanonical : IsSubcanonicalPatCoverage coverage]
  {Γ : C} { cov : PatCover Γ } (isCover : cov ∈ coverage Γ)
  : Sieve.generate (coverSlicePresieve cov)
      ∈ ((Sheaf.canonicalTopology C).over Γ).sieves (Over.mk (𝟙 Γ))  := by
    rw [GrothendieckTopology.mem_over_iff]
    simp [generateEquiv]
    have inCanonical : (Sieve.generate (toPresieve cov)) ∈ (Sheaf.canonicalTopology C).sieves Γ :=
      by
        apply canonicalCoverageGenerate
        apply subcanonical.inCanonical isCover
    apply cast _ inCanonical
    congr!
    have unEquiv
      : (Sieve.overEquiv (Over.mk (𝟙 Γ))) ((Sieve.overEquiv (Over.mk (𝟙 Γ))).symm (Sieve.generate (toPresieve cov)))
          = (Sieve.generate (toPresieve cov)) :=
        (Sieve.overEquiv (Over.mk (𝟙 Γ))).right_inv (Sieve.generate (toPresieve cov))
    apply Eq.trans unEquiv.symm
    congr!

def subcanonicalPatSliceSheaf
  [subcanonical : IsSubcanonicalPatCoverage coverage]
  {Γ : C} {Δᵢ} { cov : PatCover Γ } (isCover : cov ∈ coverage Γ)
  : Presieve.IsSheafFor (yoneda.obj Δᵢ) (coverSlicePresieve cov)  := by
    apply Presieve.IsSheaf.isSheafFor (J := (Sheaf.canonicalTopology C).over Γ)
    . apply Sheaf.Subcanonical.isSheaf_of_representable
      apply GrothendieckTopology.subcanonicalSlice
      simp [Sheaf.Subcanonical]
    . apply subcanonicalPatSliceCover isCover


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


def subcanonicalCompat
  [subcanonical : IsSubcanonicalPatCoverage coverage]
  {Γ : C} {T : Ty Γ} {cov} (isCover : cov ∈ (coverage Γ))
  (branches : MatchOn cov T)
  : Presieve.FamilyOfElements.Compatible (branchesToFam branches) := by
      intros X Y Z g1 g2 f1 f2 R1 R2 eq
      simp
      simp [coverSlicePresieve, toSlicePresieve, setOf, toPresieve, Membership.mem, Set.Mem] at R1 R2
      -- let ⟨X , rtx , xarr⟩ := X
      -- let ⟨Y , rty , yarr⟩ := Y
      cases X
      cases Y
      let ⟨f1 , _ , eq1⟩ := f1
      let ⟨f2 , _ , eq2⟩ := f2
      let eq' := congrArg (fun (x : Z ⟶ Over.mk (𝟙 Γ)) => x.left) eq
      simp at eq'
      let ⟨feq , posEq⟩ := subcanonical.disjoint isCover R1 R2 eq'
      simp [Over.mk, CostructuredArrow.mk] at feq
      cases feq
      cases posEq
      let mono := (subcanonical.nonOverlapping isCover R1).right_cancellation g1.left g2.left eq'
      apply Over.OverMorphism.ext
      simp [mono]
      congr!
      simp at eq1 eq2
      aesop

theorem matchSliceArrowAmalg
  [subcanonical : IsSubcanonicalPatCoverage coverage]
  {Γ : C} {T : Ty Γ} {cov} (isCover : cov ∈ (coverage Γ))
  (branches : MatchOn cov T)
 :  {x : Over.mk (𝟙 Γ) ⟶ tyToSlice T //
      Presieve.FamilyOfElements.IsAmalgamation (branchesToFam branches) x } := by
    simp [MatchOn] at branches
    let amalg :=
      (subcanonicalPatSliceSheaf isCover)
        (branchesToFam branches)
        (subcanonicalCompat isCover branches)
    let ⟨x, pf , _⟩ :=  Classical.indefiniteDescription _ amalg
    aesop



-- class IsSubcanonical (coverage : Coverage (cat := cat)) : Type _ where


-- Relies on Axiom of choice. Alternately we can add an extra constraint that
-- the sheaf is constructive.
noncomputable instance {coverage : CwF.PatCoverage (C := C)}
  [subcanonical : IsSubcanonicalPatCoverage coverage]
  : MatchWithCoverage coverage where
  -- Scratch work, just admit a bunch of stuff to find out what we need
  mkMatch isCover branches :=
    termSliceEquivId.symm
      (matchSliceArrowAmalg isCover branches).val
  matchesBranch {Γ} {T} {cov} isCover pos patInCover branches := by
    dsimp only []
    rw [termSliceEquivIdSymmSub]
    symm
    rw [castSymm]
    simp [Equiv.apply_eq_iff_eq_symm_apply, castTm]
    norm_cast
    let prop :=
      (matchSliceArrowAmalg isCover branches).prop
    simp [Presieve.FamilyOfElements.IsAmalgamation, branchesToFam, termSliceEquiv'] at prop
    apply Eq.trans
    . apply prop
      aesop_cat
    . congr! <;> try aesop_cat
      simp
      let lem  (pos1 pos2 : Over Γ) (isCov : pos2 ∈ cov) (eq : pos1 = pos2)
        : branches pos1 (cast (by aesop) isCov) = cast (by aesop) (branches pos2 isCov) := by
        cases eq
        rfl
      apply lem
      aesop
    . simp

    -- let t := (termSliceEquivId.symm.toFun
    -- simp
    -- rw [Equiv.symm_apply_eq]
    -- apply Function.LeftInverse.injective termSliceEquivId.left_inv
    -- apply Eq.trans _ (by simp ; rfl)
    -- rw [termSliceEquivId.left_inv]
