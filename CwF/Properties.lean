import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Types
import Mathlib.Combinatorics.Quiver.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Comma.Over
import Mathlib.CategoryTheory.Comma.StructuredArrow
import Mathlib.CategoryTheory.Comma.Basic
import Mathlib.CategoryTheory.Functor.ReflectsIso
import Mathlib.Data.Opposite
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.Logic.Unique


import Mathlib.Data.ULift

import CwF.Fam
import CwF.Basics

open CategoryTheory

namespace CwF

open Fam
open CwFProp
open CwFExt

universe u v u2
variable {C : Type u} [cat : Category.{v}  C] [cwf: CwF C]

-- Some cast lemmas
@[simp]
def castSnoc {Γ Δ : C} {T : Ty Γ} {eq : Γ = Δ}
  : Δ ▹ (cast (by rw [eq]) T) = Γ ▹ T := by aesop
--
--
@[simp]
theorem castP {Γ Δ  : C} {T : Ty Γ} {eq : Γ = Δ } :
  cast (β := Δ ▹ (cast (by aesop) T) ⟶ Δ ) (by aesop) (p (T := T))  = p :=
    by aesop

@[simp]
theorem castV {Γ Δ  : C} {T : Ty Γ} {eq : Γ = Δ } :
  cast (by aesop) (v (T := T))  = v (T := cast (β := Ty Δ) (congrArg Ty eq) T) :=
    by aesop



@[simp]
theorem vExtComp {Γ Δ Ξ : C} {T : Ty Γ }
{f : Δ ⟶ Γ} {t : Tm (T⦃f⦄)} {θ : Ξ ⟶ Δ}
  : v⦃θ ≫ ⟪f,t⟫⦄  = cast (by aesop) t⦃θ⦄  := by
  simp [tmSubComp']


-- If you compose with an extension, this is the same as extending by the composition,
-- except that you also end up substituting in the term you're extending by.
-- Unfortunate ugliness due to the fact that Tm⦃g ≫ f⦄ is not definitionally equal to tm⦃f⦄⦃g⦄
@[simp]
theorem ext_nat {Γ Δ Ξ : C} {T : Ty Γ}
  (f : Δ ⟶ Γ)
  (g : Ξ ⟶ Δ)
  (t : Tm (T⦃f⦄))
  : (g ≫ ⟪f , t⟫) = ⟪g ≫ f , (castTm t⦃g⦄ (by simp [tySubComp])) ⟫ := by
    fapply ext_unique <;> simp_all


-- If you take a weaning and extend it with the newly introduced variable, you get the identity,
-- because it just replaces each v with v
@[simp]
theorem ext_id {Γ : C} {T : Ty Γ} : ⟪p , v⟫ = 𝟙 (Γ ▹ T) := by
  symm
  fapply ext_unique <;> simp_all

-- Helper function for dependent cong
-- Should really be in the stdlib
-- TODO PR?
--
--


theorem v_eq {Γ Δ : C} {T : Ty Γ} {f g : Δ ⟶ Γ▹T }
  (eq : f = g)
  : (v (T := T))⦃f⦄ =ₜ (v (T := T))⦃g⦄  := by aesop


theorem v_id {Γ : C} {T : Ty Γ} {f : Γ▹T ⟶ Γ▹T }
  (eq : f = 𝟙 (Γ▹T))
  : (v (T := T))⦃f⦄ =ₜ v  := by aesop


theorem castCong {A : Type u} {B : A → Type v} {f g : (a : A) → B a} {x y : A}
  (funEq : f = g) (argEq : x = y) :
    (f x) = cast (by aesop) (g y) := by
    aesop

@[simp]
theorem ext_inj {Γ Δ : C} {θ₁ θ₂ : Δ ⟶ Γ} {T : Ty Γ} {t₁ : Tm (T⦃θ₁⦄)} {t₂ : Tm (T⦃θ₂⦄)}
  :
  (⟪θ₁,t₁⟫ = ⟪θ₂,t₂⟫) ↔ (∃ x : (θ₁ = θ₂), t₁ =ₜ t₂) := by
    constructor <;> intro eq <;> try aesop_cat
    have peq := congrArg (λ x => x ≫ p) eq
    have veq := castCong (refl (λ x => v ⦃x⦄)) eq
    simp at peq
    aesop




---- Terms and Sections
-- There is an equivalence between terms of Tm T
-- and sections p_T

-- Turn a term into the substitution that replaces v with that term
abbrev toSub {Γ : C} {T : Ty Γ} (t : Tm T) : Γ ⟶ (Γ ▹ T) :=
  ⟪ 𝟙 _ , ↑ₜ t ⟫


def pSec {Γ : C} (T : Ty Γ) : Type _ :=
  SplitEpi (p (T := T))

-- That subsitution is a section of p
abbrev toSection {Γ : C} {T : Ty Γ} (t : Tm T) : pSec T :=
  ⟨ toSub t , by simp_all ⟩

-- Get a term out of any section of p
abbrev toTerm {Γ : C} {T : Ty Γ} (epi : pSec T) : Tm T :=
  ↑ₜ ((v ) ⦃ epi.section_ ⦄)

theorem congrDep₂  {A : Type } {B : A → Type} {R :  Type} (f : (a : A) → (b : B a) → R)
  {a₁ a₂ : A} (eqa : a₁ = a₂) {b₁ : B a₁} {b₂ : B a₂} (eqb : b₁ = cast (by aesop) b₂)
  : f a₁ b₁ = (f a₂ b₂) := by
  cases eqa with
  | refl =>
    simp at eqb
    cases eqb with
      | refl => simp


theorem extEq {Γ Δ : C} {T : Ty Γ } {f g : Δ ⟶ Γ } {t : Tm (T⦃f⦄)}
  (eq : f = g) : ⟪f , t ⟫ = ⟪ g , castTmSub t eq⟫ := by aesop


theorem toSectionTerm {Γ : C} {T : Ty Γ} (epi : pSec T) : toSection (toTerm epi) = epi := by
  simp [toTerm, toSection, toSub]
  cases (epi) with
  | mk f eq =>
    congr
    simp_all
    rw [extEq (symm eq)]
    simp
    rw [<- ext_nat]
    simp

theorem toTermSection {Γ : C} {T : Ty Γ} (t : Tm T) : toTerm (toSection t) = t := by
  simp [toTerm, toSection, toSub]


-- Terms and sections are equivalent
theorem termSecEquiv {Γ : C} {T : Ty Γ} : Function.Bijective (toSection (T := T))  := by
  constructor
  . apply Function.LeftInverse.injective (g := toTerm)
    apply toTermSection
  . apply Function.RightInverse.surjective (g := toTerm)
    apply toSectionTerm

-- This equivalence is an isomorphism in Set
def termSecIso {Γ : C} {T : Ty Γ}
  : uliftFunctor.{v,u}.obj (Tm T) ≅ uliftFunctor.obj.{u,v} (pSec T)  where
  hom t := ULift.up (toSection t.down)
  inv θ := ULift.up (toTerm θ.down)
  hom_inv_id := by
    funext t
    apply ULift.down_injective
    simp [toTermSection]
  inv_hom_id := by
    funext t
    apply ULift.down_injective
    simp [toSectionTerm]


-- All arrows out of the empty context are sections of p
def emptySecIso : pSec T ≅ (cwf.empty ⟶ cwf.empty▹T) where
      hom sec := sec.section_
      inv f := by
        fconstructor
        . apply f
        . aesop_cat


--Closed types are isomorphic to arrows into the context only containing that type
def closedSnocIso {T : Ty ⬝}
  : uliftFunctor.{v,u}.obj (Tm T) ≅ uliftFunctor.{u,v}.obj (cwf.empty ⟶ (⬝▹T)) :=
  termSecIso ≪≫ uliftFunctor.mapIso emptySecIso


--And we can transport isomorphisms across this equivalence,
--because uliftFunctor is fully faithful
theorem termSecPreserveEquiv  {Γ : C} {S T : Ty Γ}
  (epiEquiv : pSec S ≅ pSec T)
  : Tm S ≅ Tm T := by
  let liftIso := termSecIso (T := S)
    ≪≫ uliftFunctor.{u,v}.mapIso epiEquiv
    ≪≫ (termSecIso (T := T)).symm
  apply Functor.preimageIso uliftFunctor.{v,u} liftIso

-- Corollary is that toTerm is injective: each unique section carves out a unique term
-- which is useful when defining new terms by composing section
-- especially for democratic CwFs
theorem toTermInj {Γ : C} {T : Ty Γ} : Function.Injective (toTerm (T := T)) := by
  apply Function.LeftInverse.injective
  apply toSectionTerm

notation:10000 t "⁻" => toSub t

-- Weakening
-- Lifts any substitution to work on an extended context
abbrev wk {Γ Δ : C} (f : Δ ⟶ Γ) {T : Ty Γ} : (Δ ▹ T⦃f⦄) ⟶ (Γ ▹ T) :=
  ⟪p (T := T⦃f⦄) ≫ f , ↑ₜ v ⟫

-- Weakening morphisms are the CwF version of a substitution Γ(x:T)Δ ⟶ Γ Δ
-- i.e. as a substitution, we can introduce an unused variable anywhere in the context
class Weakening (Δ Γ : C) : Type _ where
  weaken : Δ ⟶ Γ

instance wkBase {Γ : C} {T : Ty Γ} : Weakening (Γ ▹ T) Γ where
  weaken := p

instance wkStep {Δ Γ : C} [inst : Weakening Δ Γ] {T : Ty Γ}  : Weakening (Δ ▹ T⦃inst.weaken⦄) (Γ ▹ T) where
  weaken := wk (inst.weaken) (T := T)

notation:10000 T "⁺" => tySub T Weakening.weaken
notation:10000 t "⁺" => tmSub t Weakening.weaken


-- All equalities between terms can be deduced from equalities between morphisms
theorem eqAsSections {Γ : C} {T : Ty Γ} {t1 t2 : Tm T} (eq :  t1⁻ =  t2⁻)
  : t1 = t2 := by
  apply Function.LeftInverse.injective (toTermSection)
  simp_all


@[simp]
theorem vCast {Γ  : C} {T : Ty Γ} {f : _} (eq : f = 𝟙 (Γ ▹ T)) : (v (T := T))⦃f⦄  =ₜ v := by
  aesop

@[simp]
theorem wkTm {Γ Δ : C} (θ : Δ ⟶ Γ) {T : Ty Γ} {t : Tm T}
: (t⦃θ⦄)⁻ ≫ (wk θ) = θ ≫ (t⁻) := by
  simp [toSub, <- Category.assoc]


----------------------------------------------------------
-- Some useful tools for going between morphisms and terms


-- These lemmas encode a generalization of the "terms as sections of display maps"
-- idea, where germs in an indexed type correspond to arrows in the slice category
-- between the specific index values and a display map.
-- When you plug in id for the arrow, you get terms as sections

abbrev tyToSlice {Γ : C} (T : Ty Γ) : Over Γ :=
  Over.mk (p (T := T))

def secToSliceArrow {Γ : C} {T : Ty Γ} (sec : pSec T)
  : (Over.mk (𝟙 Γ) ⟶ tyToSlice T) :=
    Over.homMk (SplitEpi.section_ sec)

def sliceArrowToSection {Γ : C} {T : Ty Γ} (sliceArr : Over.mk (𝟙 Γ) ⟶ tyToSlice T)
  : pSec T := SplitEpi.mk (sliceArr.left)
    (by have pf := Over.w sliceArr
        simp_all [tyToSlice]
        )


def extHead {Γ Δ : C} {T : Ty Γ} (f : Δ ⟶ Γ ▹ T) : Tm (T⦃f ≫ p⦄) :=
  ↑ₜ v⦃f⦄

theorem headTmEq {Γ Δ : C} {T : Ty Γ} (f : Δ ⟶ Γ ▹ T) : f = ⟪f ≫ p, extHead f⟫ := by
  have p : _ := ext_nat p f v
  rw [ext_id] at p
  aesop

-- Γ is the "telescope of indices"
-- f is the concrete index values for T that t has
def termFromSlice {Γ Δ : C} {T : Ty Δ}
  (f : Γ ⟶ Δ)
  (sliceArr : (Over.mk f) ⟶ tyToSlice T)
  : Tm (T⦃f⦄) :=
    castTm (extHead sliceArr.left) (by
  have pf := Over.w sliceArr
  simp_all)

def termToSlice {Γ Δ : C} {T : Ty Δ}
  (f : Γ ⟶ Δ) (t : Tm (T⦃f⦄))
  : ( (Over.mk f) ⟶ tyToSlice T) := by
  fapply Over.homMk
  . simp_all
    exact ⟪f , t⟫
    --TODO simplify this
  . simp_all -- Looks to be a lean4 bug, see https://github.com/leanprover/lean4/issues/3257
    reduce
    simp

theorem termToFromSlice {Γ Δ : C} {T : Ty Δ}
  (f : Γ ⟶ Δ)
  (sliceArr : (Over.mk f) ⟶ tyToSlice T)
  : termToSlice f (termFromSlice f sliceArr) = sliceArr := by
  apply Over.OverMorphism.ext
  simp [termToSlice, termFromSlice]
  apply (λ x => Eq.trans x (Eq.symm (headTmEq _)))
  rw [ext_inj]
  fconstructor
  . symm
    apply Over.w sliceArr
  . simp_all

theorem termFromToSlice {Γ Δ : C} {T : Ty Δ}
  (f : Γ ⟶ Δ) (t : Tm (T⦃f⦄))
  : termFromSlice f (termToSlice f t) = t := by
    simp [termFromSlice, termToSlice, extHead]

-- theorem termSliceIso {Γ Δ : C} {T : Ty Δ} (f : Γ ⟶ Δ)
--   : Iso (Tm T⦃f⦄) ( (Over.mk f) ⟶ tyToSlice T)  where
--   hom := termToSlice
--   inv := termFromSlice


--Helpers for proof search
@[aesop unsafe 90% apply]
theorem congrTy {Γ : C} {S T : Ty Γ}
  (eq : S = T)
  : Tm S = Tm T := by aesop_cat


@[aesop unsafe 90% apply]
theorem congrTySub {Δ Γ : C} {T : Ty Γ} {f g : Δ ⟶ Γ }
  (eq : f = g)
  : T⦃f⦄ = T⦃g⦄ := by aesop_cat

end CwF
