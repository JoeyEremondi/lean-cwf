import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Types
import Mathlib.Combinatorics.Quiver.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Comma.Over
import Mathlib.CategoryTheory.Comma.StructuredArrow
import Mathlib.CategoryTheory.Comma.Basic
import Mathlib.CategoryTheory.Functor.ReflectsIso
import Mathlib.CategoryTheory.Conj
import Mathlib.Data.Opposite
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.Logic.Unique


import Mathlib.Data.ULift

import CwF.Fam
import CwF.Basics

-- import CwF.Util.ULift

open CategoryTheory

namespace CwF

open Fam
open CwFProp
open CwFExt

universe u v' u2
variable {C : Type u} [cat : Category.{v'}  C] [cwf: CwF C]


--We work with (type) equivalences, but any time we have equivalences at
--the same universe level, we want to be able to use isomorphisms
-- instance {A B : Type u} : Coe (A ≅ B) (Equiv A  B) where
--   coe := Iso.toEquiv
-- instance {A B : Type u} : Coe (Equiv A  B) (A ≅ B) where
--   coe := Equiv.toIso


-- Some cast lemmas
@[simp]
def castSnoc {Γ Δ : C} {T : Ty Γ} {eq : Γ = Δ}
  : Δ ▹ (cast (by rw [eq]) T) = Γ ▹ T := by aesop
--
--
@[simp]
theorem castP {Γ Δ  : C} {T : Ty Γ} {eq : Γ = Δ } :
  cast (β := Δ ▹ (cast (by aesop) T) ⟶ Δ ) (by aesop) (p_ T)  = p :=
    by aesop

@[simp]
theorem castV {Γ Δ  : C} {T : Ty Γ} {eq : Γ = Δ } :
  cast (by aesop) (v_ T)  = v_ ( cast (β := Ty Δ) (congrArg Ty eq) T) :=
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

-- Simp re-associates composition, so we need a version that accounts for this
-- so we can rewrite nicely
@[simp]
theorem ext_nat_comp {Γ Δ Ξ Ξ' : C} {T : Ty Γ}
  (f : Δ ⟶ Γ)
  (g : Ξ ⟶ Δ)
  (h : Γ▹T ⟶ Ξ')
  (t : Tm (T⦃f⦄))
  : (g ≫ (⟪f , t⟫ ≫ h)) = ⟪g ≫ f , (castTm t⦃g⦄ (by simp [tySubComp])) ⟫ ≫ h
  := by simp [<- Category.assoc]


-- If you take a weaning and extend it with the newly introduced variable, you get the identity,
-- because it just replaces each v with v
@[simp]
theorem ext_id {Γ : C} {T : Ty Γ} : ⟪p , v⟫ = 𝟙 (Γ ▹ T) := by
  symm
  fapply ext_unique <;> simp_all

-- We can combine these to decompose any morphism to a Snoc into an extension arrow
theorem ext_decomp {Γ Δ : C} {T : Ty Γ} {θ : Δ ⟶ Γ▹T}
  : θ = cwf.cwfExt.ext (θ ≫ p) (↑ₜ v⦃θ⦄ )  := by
  trans
  . apply (Eq.symm (Category.comp_id _))
  . rw [<- ext_id]
    rw [ ext_nat ]

  

-- Helper function for dependent cong
-- Should really be in the stdlib
-- TODO PR?
--


@[aesop unsafe 90%]
theorem ty_eq {Γ Δ : C} {f g : Δ ⟶ Γ } {T : Ty Γ}
  (eq : f = g)
  : T⦃f⦄ = T ⦃g⦄  := by aesop


@[aesop unsafe 90%]
theorem ty_id {Γ : C} {g : Γ ⟶ Γ } {T : Ty Γ}
  (eq : g = 𝟙 Γ)
  : T = T ⦃g⦄  := by aesop


@[aesop unsafe 90%]
theorem tm_eq {Γ Δ : C} {T : Ty Γ} {f g : Δ ⟶ Γ } {t : Tm T}
  (eq : f = g)
  : t⦃f⦄ =ₜ t ⦃g⦄  := by aesop


@[aesop unsafe 90%]
theorem tm_id {Γ : C} {T : Ty Γ} {g : Γ ⟶ Γ } {t : Tm T}
  (eq : g = 𝟙 Γ)
  : t =ₜ t ⦃g⦄  := by aesop

-- theorem v_eq {Γ Δ : C} {T : Ty Γ} {f g : Δ ⟶ Γ▹T }
--   (eq : f = g)
--   : (v (T := T))⦃f⦄ =ₜ (v (T := T))⦃g⦄  := by aesop


-- theorem v_id {Γ : C} {T : Ty Γ} {f : Γ▹T ⟶ Γ▹T }
--   (eq : f = 𝟙 (Γ▹T))
--   : (v (T := T))⦃f⦄ =ₜ v  := by aesop


theorem castCong {A : Type u} {B : A → Type v'} {f g : (a : A) → B a} {x y : A}
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

-- @[simp]
theorem ext_inj_general {Γ Δ : C} {θ : Δ ⟶ Γ} {T : Ty Γ} {t : Tm (T⦃θ⦄)} {f : Δ ⟶ Γ▹ T}
  :
  (⟪θ,t⟫ = f) ↔ (∃ x : (θ = f ≫ (p_ T)), t =ₜ (v_ T)⦃f⦄) := by
  let decomp := ext_decomp (θ := f)
  rw [decomp]
  rw [ext_inj]
  fconstructor <;> simp <;> aesop_cat


-- Any morphism to Γ▹T is just a dependent pair
-- of a morphism to Γ and a term of type T
def snocIso {Δ Γ : C} {T : Ty Γ}
  : (Δ ⟶ Γ▹T)  ≃ (γ : Δ ⟶ Γ) × (Tm T⦃γ⦄) where
  toFun θ := by
    fconstructor
    . apply θ ≫ p
    . let x := v_ T
      let y := x⦃θ⦄
      simp only [tySubComp] at y
      assumption
  invFun := fun ⟨γ, t⟩ => by
    fapply ext
    . apply γ
    . apply t
  left_inv θ := by
    simp
    rw [ext_inj_general]
    aesop_cat
  right_inv γt := by
    cases γt with
    | mk γ t =>
      simp


---- Terms and Sections
-- There is an equivalence between terms of Tm T
-- and sections p_T

-- Turn a term into the substitution that replaces v with that term
abbrev toSub {Γ : C} {T : Ty Γ} (t : Tm T) : Γ ⟶ (Γ ▹ T) :=
  ⟪ 𝟙 _ , ↑ₜ t ⟫


def pSec {Γ : C} (T : Ty Γ) : Type _ :=
  SplitEpi (p_ T)

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


-- This equivalence is an equivalence between types.
-- Would be a Set-isomorphism except for the universe mismatch
def termSecEquiv {Γ : C} {T : Ty Γ}
  :  Tm T ≃ pSec T  where
  toFun := toSection
  invFun := toTerm
  left_inv t := by
    simp [toTermSection]
  right_inv t := by
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
  : Tm T ≃ (cwf.empty ⟶ (⬝▹T) ):=
  Equiv.trans termSecEquiv emptySecIso.toEquiv


--And we can transport isomorphisms across this equivalence,
--because uliftFunctor is fully faithful
theorem termSecPreserveIso  {Γ Δ : C} {S : Ty Δ} {T : Ty Γ}
  (epiEquiv : pSec S ≅ pSec T)
  : Tm S ≅ Tm T := by
  apply Equiv.toIso
  apply Equiv.trans (termSecEquiv)
  apply Equiv.trans epiEquiv.toEquiv
  apply termSecEquiv.symm

-- Corollary is that toTerm is injective: each unique section carves out a unique term
-- which is useful when defining new terms by composing section
-- especially for democratic CwFs
theorem toTermInj {Γ : C} {T : Ty Γ} : Function.Injective (toTerm (T := T)) := by
  apply Function.LeftInverse.injective
  apply toSectionTerm

notation:10000 t "⁻" => toSub t

-- def pIso {Γ Δ : C} {S : Ty Γ} {T : Ty Δ}
--   (ciso : Γ ≅ Δ)
--   (tiso : Γ▹S ≅ Δ▹T)
--   : p ≫ ciso.hom = tiso.hom ≫ p := by
--   simp [<- Iso.inv_comp_eq]
--   let lem := ext_decomp (θ := tiso.inv)
--   rw [lem]
--   simp only [<- Category.assoc]
--   rw [ext_p]
--   rw [ext_nat]

-- Types with isomorphic contexts produce isomorphic term-sets
-- TODO does this actually hold?
-- def tyIsoToTerm {Γ Δ  : C} {S : Ty Γ} {T : Ty Δ}
--   (ciso : Γ ≅ Δ)
--   (tiso : Γ▹S ≅ Δ▹T)
--   : Tm S ≅ Tm T := by
--   apply Equiv.toIso
--   apply Equiv.trans termSecEquiv
--   apply Equiv.trans _ termSecEquiv.symm
--   simp [pSec]
--   let hiso := Iso.homCongr ciso tiso
--   let piso := Iso.homCongr tiso ciso
--   fconstructor <;> try intros sec <;> try fconstructor
--   . apply (ciso.inv ≫ _)
--     apply (sec.section_ ≫ _)
--     apply tiso.hom
--   . simp
--     let lem := ext_decomp (θ := (ciso.inv ≫ sec.section_) )
--     simp only [<- Category.assoc]
--     simp only [lem]
--     simp
--     rw [ext_p]
--     simp
--     rw [Iso.inv_comp_eq_id]
--   . apply (ciso.hom ≫ _)
--     apply (sec.section_ ≫ _)
--     apply tiso.inv

  -- fconstructor <;> try intros f
  -- . fconstructor
  --   . apply (ciso.inv ≫ f.section_ ≫ tiso.hom)
  --   . simp



-- Weakening
-- Lifts any substitution to work on an extended context
abbrev wk {Γ Δ : C} (f : Δ ⟶ Γ) {T : Ty Γ} : (Δ ▹ T⦃f⦄) ⟶ (Γ ▹ T) :=
  ⟪p_ T⦃f⦄ ≫ f , ↑ₜ v ⟫

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


-- @[simp]
-- theorem vCast {Γ  : C} {T : Ty Γ} {f : _} (eq : f = 𝟙 (Γ ▹ T)) : (v_ (T⦃f⦄)) =ₜ v_ T := by
--   aesop



-- @[simp]
theorem wkTm {Γ Δ : C} (θ : Δ ⟶ Γ) {T : Ty Γ} {t : Tm T}
: (t⦃θ⦄)⁻ ≫ (wk θ) = θ ≫ (t⁻) := by
  simp [<- Category.assoc]

-- -- Version of snocIso that plays better with universes
-- def snocSecIso {Δ Γ : C} {T : Ty Γ}
--   : (Δ ⟶ Γ▹T) ≅ (γ : Δ ⟶ Γ) × (pSec T⦃γ⦄) where
--   hom θ := by
--     fconstructor
--     . apply θ≫ p
--     . let x := v_ T
--       let y := x⦃θ⦄
--       simp only [tySubComp] at y
--       apply toSection
--       assumption
--   inv := fun ⟨γ, t⟩ => by
--     fapply ext
--     . apply γ
--     . apply toTerm
--       assumption
--   hom_inv_id := by
--     funext θ
--     simp
--     rw [ext_inj_general]
--     aesop_cat
--   inv_hom_id := by
--     funext γt
--     cases γt with
--     | mk γ t =>
--       simp
--       apply heq_of_heq_of_eq _ (toSectionTerm t)
--       simp [toTerm, castTm]
--       apply hCong (f := toSection) (g := toSection) (y := cast _ v⦃t.section_⦄)
--       rfl
--       apply heq_of_eq
--       reduce
--       apply hCongArg (f := toSection) (x := cast _ _) (y := toTerm t)



----------------------------------------------------------
-- Some useful tools for going between morphisms and terms


-- These lemmas encode a generalization of the "terms as sections of display maps"
-- idea, where germs in an indexed type correspond to arrows in the slice category
-- between the specific index values and a display map.
-- When you plug in id for the arrow, you get terms as sections

abbrev tyToSlice {Γ : C} (T : Ty Γ) : Over Γ :=
  Over.mk (p_ T)

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
  have pf : _ := ext_nat p f v
  rw [ext_id] at pf
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

def termSliceEquiv {Γ Δ : C} {T : Ty Δ}
  {f : Γ ⟶ Δ}
  : Tm T⦃f⦄ ≃ ((Over.mk f) ⟶ tyToSlice T) where
  toFun := termToSlice f
  invFun := termFromSlice f
  left_inv := termFromToSlice f
  right_inv := termToFromSlice f

--TODO add to mathlib?
def overExt {Γ : C} {f g : Over Γ}
  (domEq : f.left = g.left) (eq : f.hom = cast (by simp [domEq]) g.hom)
  : f = g := by
    cases f
    cases g
    cases domEq
    cases eq
    aesop_cat

def termSliceSub {Γ Δ Ξ : C} (f : Δ ⟶ Γ) (g : Ξ ⟶ Δ)
  : Over.mk (g ≫ f) ⟶ Over.mk f := by
    apply Over.homMk _ _ <;> simp
    . apply g
    . rfl

def termSliceEquivSymmSub  {Γ Δ Ξ : C} (f : Δ ⟶ Γ) (g : Ξ ⟶ Δ) (T : Ty Γ) (θ : ((Over.mk f) ⟶ tyToSlice T))
  : ((termSliceEquiv (f := f)).symm θ)⦃g⦄ =ₜ termSliceEquiv.symm ((termSliceSub f g) ≫ θ) := by
  simp [termSliceEquiv]
  dsimp [termFromSlice]
  dsimp only [extHead]
  repeat rw [castCast] <;> aesop_cat
  rw [castSub]
  simp
  aesop_cat



def termSliceEquiv' {Δ : C} {T : Ty Δ}
  {f : Over Δ}
  : Tm T⦃f.hom⦄ ≃ (f ⟶ tyToSlice T) := by
  let ff := f.hom
  simp at ff
  let ret := @termSliceEquiv _ _ _ f.left Δ T ff
  simp at ret
  apply Equiv.trans ret
  apply Equiv.cast
  apply congrArg (fun x => x ⟶ _)
  cases f
  rfl


def termSliceEquivId {Γ : C} {T : Ty Γ}
  : Tm T ≃ ((Over.mk (𝟙 Γ)) ⟶ tyToSlice T) := by
    let eq : Tm T⦃𝟙 Γ⦄ ≃ ((Over.mk (𝟙 Γ)) ⟶ tyToSlice T) := termSliceEquiv (f := 𝟙 Γ)
    simp at eq
    assumption


def termSliceEquivIdSymmSub  {Γ Ξ : C}  (g : Ξ ⟶ Γ) (T : Ty Γ)
  (θ : ((Over.mk (𝟙 Γ)) ⟶ tyToSlice T))
  : (termSliceEquivId.symm θ)⦃g⦄ =ₜ
      (termSliceEquiv.symm (termSliceSub (𝟙 Γ) g ≫ θ)) := by
    let foo := (termSliceEquivSymmSub (𝟙 Γ) g T θ)
    apply cast _ foo
    congr! <;> try aesop_cat
    apply heq_of_cast_eq
    symm
    simp [termSliceEquivId]
    aesop_cat


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


-- Isomorphism properties
-- TODO organize
def closedWeakenIso {Γ Δ : C} {T : Ty ⬝}
  (iso : Γ ≅ Δ)
  : Tm (T⦃⟨⟩Γ⦄) ≃ Tm (T⦃⟨⟩Δ⦄)  where
  toFun t := by
    let t' := t⦃iso.inv⦄
    simp at t'
    exact t'
  invFun t := by
    let t' := t⦃iso.hom⦄
    simp at t'
    exact t'
  left_inv := by
    intros t
    symm
    simp
    apply tm_id
    aesop_cat
  right_inv := by
    intros t
    symm
    simp
    apply tm_id
    aesop_cat



end CwF
