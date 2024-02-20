import CwF.Fam
import CwF.CwF
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Comma.Over
import Mathlib.CategoryTheory.Comma.Basic
import Mathlib.Data.Opposite
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.Logic.Unique

open CategoryTheory

universe u v u2
section
  variable {C : Type u} [Category.{v}  C] [TmTy.{u,v} C] [cwf: CwF C]



  -- If you compose with an extension, this is the same as extending by the composition,
  -- except that you also end up substituting in the term you're extending by.
  -- Unfortunate ugliness due to the fact that Tm⦃g ≫ f⦄ is not definitionally equal to tm⦃f⦄⦃g⦄
  @[simp]
  theorem ext_nat {Γ Δ Ξ : C} {T : Ty Γ}
    (f : Δ ⟶ Γ)
    (g : Ξ ⟶ Δ)
    (t : Tm (T⦃f⦄))
    : (g ≫ ⟪f , t⟫) = ⟪g ≫ f , (↑ₜ t⦃g⦄) ⟫ := by
      fapply CwF.ext_unique <;> simp_all
      have eq2 := castSymm (tmSubComp (f := ⟪f , t⟫) (g := g) (t := CwF.v))
      rw [eq2]
      simp_all


  -- If you take a weaning and extend it with the newly introduced variable, you get the identity,
  -- because it just replaces each v with v
  @[simp]
  theorem ext_id {Γ : C} {T : Ty Γ} : ⟪CwF.p , CwF.v⟫ = 𝟙 (Γ ▹ T) := by
    symm
    fapply CwF.ext_unique <;> simp_all

  -- Helper function for dependent cong
  -- Should really be in the stdlib
  -- TODO PR?
  theorem hCong {A : Type u} {B : A → Type v} {f g : (a : A) → B a} {x y : A}
    (funEq : f = g) (argEq : x = y) :
      HEq (f x) (g y) := by aesop

  theorem castCong {A : Type u} {B : A → Type v} {f g : (a : A) → B a} {x y : A}
    (funEq : f = g) (argEq : x = y) :
      (f x) = cast (by aesop) (g y) := by
      aesop


  theorem ext_inj {Γ Δ : C} {θ₁ θ₂ : Δ ⟶ Γ} {T : Ty Γ} {t₁ : Tm (T⦃θ₁⦄)} {t₂ : Tm (T⦃θ₂⦄)}
    :
    (⟪θ₁,t₁⟫ = ⟪θ₂,t₂⟫) ↔ (∃ x : (θ₁ = θ₂), t₁ =ₜ t₂) := by
      constructor <;> intro eq <;> try aesop_cat
      have peq := congrArg (λ x => x ≫ CwF.p) eq
      have veq := castCong (refl (λ x => CwF.v ⦃x⦄)) eq
      simp at peq
      aesop




---- Terms and Sections
-- There is an equivalence between terms of Tm T
-- and sections p_T

  -- Turn a term into the substitution that replaces v with that term
  abbrev toSub {Γ : C} {T : Ty Γ} (t : Tm T) : Γ ⟶ (Γ ▹ T) :=
    ⟪ 𝟙 _ , ↑ₜ t ⟫

  -- That subsitution is a section of p
  abbrev toSection {Γ : C} {T : Ty Γ} (t : Tm T) : SplitEpi (CwF.p (T := T)) :=
    ⟨ toSub t , by simp_all ⟩

  -- Get a term out of any section of p
  abbrev toTerm {Γ : C} {T : Ty Γ} (epi : SplitEpi (CwF.p (T := T))) : Tm T :=
    ↑ₜ ((CwF.v ) ⦃ epi.section_ ⦄)

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


  theorem toSectionTerm {Γ : C} {T : Ty Γ} (epi : SplitEpi (CwF.p (T := T))) : toSection (toTerm epi) = epi := by
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
    ⟪CwF.p (T := T⦃f⦄) ≫ f , ↑ₜ CwF.v ⟫

  -- Weakening morphisms are the CwF version of a substitution Γ(x:T)Δ ⟶ Γ Δ
  -- i.e. as a substitution, we can introduce an unused variable anywhere in the context
  class Weakening (Δ Γ : C) : Type _ where
    weaken : Δ ⟶ Γ

  instance wkBase {Γ : C} {T : Ty Γ} : Weakening (Γ ▹ T) Γ where
    weaken := CwF.p

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
  theorem vCast {Γ  : C} {T : Ty Γ} {f : _} (eq : f = 𝟙 (Γ ▹ T)) : (tmSub (CwF.v (T := T)) f)  =ₜ CwF.v := by
    aesop

  @[simp]
  theorem wkTm {Γ Δ : C} (θ : Δ ⟶ Γ) {T : Ty Γ} {t : Tm T}
  : (t⦃θ⦄)⁻ ≫ (wk θ) = θ ≫ (t⁻) := by
    simp [toSub]
    rw [ext_inj]
    apply Exists.intro <;> simp_all
    simp [<- Category.assoc]

end

--Given the functoral definition of substitution on terms and types for a category of contexts,
--context extension is unique up to isomorphism
lemma cwfUnique {C : Type u} [Category.{v}  C] [TmTy.{u,v} C] [Limits.HasTerminal C]
  (inst1 : CwF C) (inst2 : CwF C) {Γ : C} {T : Ty Γ} :  (inst1.snoc Γ T)  ≅  (inst2.snoc Γ T) where
  -- Bascially a dependent version of the uniqueness of products
  hom := inst2.ext (inst1.p (T := T)) inst1.v
  inv := inst1.ext (inst2.p (T := T)) inst2.v
  hom_inv_id := by
    rw [<- ext_id (cwf := inst1) (T := T)]
    fapply inst1.ext_unique
      <;> try simp [ext_nat (cwf := inst1), inst1.ext_p ]
    trans
    . apply castSymm
      apply tmSubComp
    . simp_rw [inst1.ext_v]
      simp only [castSub, inst2.ext_v, cast_cast]
  inv_hom_id := by
    rw [<- ext_id (cwf := inst2) (T := T)]
    fapply inst2.ext_unique <;> try simp [ext_nat (cwf := inst1), inst1.ext_p]
    trans
    . apply castSymm
      apply tmSubComp
    simp_rw [inst2.ext_v]
    simp only [castSub, inst1.ext_v, cast_cast]



----------------------------------------------------------
-- Some useful tools for going between morphisms and terms

section

  variable {C : Type u} [Category.{v}  C] [TmTy.{u,v} C]  [cwf: CwF C]


  -- These lemmas encode a generalization of the "terms as sections of display maps"
  -- idea, where germs in an indexed type correspond to arrows in the slice category
  -- between the specific index values and a display map.
  -- When you plug in id for the arrow, you get terms as sections

  abbrev tyToSlice {Γ : C} (T : Ty Γ) : Over Γ :=
    Over.mk (CwF.p (T := T))

  def secToSliceArrow {Γ : C} {T : Ty Γ} (sec : SplitEpi (CwF.p (T := T)))
    : (Over.mk (𝟙 Γ) ⟶ tyToSlice T) :=
      Over.homMk (SplitEpi.section_ sec)

  def sliceArrowToSection {Γ : C} {T : Ty Γ} (sliceArr : Over.mk (𝟙 Γ) ⟶ tyToSlice T)
    : SplitEpi (CwF.p (T := T)) := SplitEpi.mk (sliceArr.left)
      (by have pf := Over.w sliceArr
          simp_all [tyToSlice]
          )


  def extHead {Γ Δ : C} {T : Ty Γ} (f : Δ ⟶ Γ ▹ T) : Tm (T⦃f ≫ CwF.p⦄) :=
    ↑ₜ CwF.v⦃f⦄

  theorem headTmEq {Γ Δ : C} {T : Ty Γ} (f : Δ ⟶ Γ ▹ T) : f = ⟪f ≫ CwF.p, extHead f⟫ := by
    have p : _ := ext_nat CwF.p f CwF.v
    rw [ext_id] at p
    aesop

  def termFromSlice {Γ Δ : C} {T : Ty Δ}
    (f : Γ ⟶ Δ)
    (sliceArr : (CategoryTheory.Over.mk f) ⟶ (CategoryTheory.Over.mk (CwF.p (T := T))))
    : Tm (T⦃f⦄) :=
      castTm (extHead sliceArr.left) (by
    have pf := Over.w sliceArr
    simp_all)

  def termToSlice {Γ Δ : C} {T : Ty Δ}
    (f : Γ ⟶ Δ) (t : Tm (T⦃f⦄))
    : ( (CategoryTheory.Over.mk f) ⟶ (CategoryTheory.Over.mk (CwF.p (T := T)))) := by
    fapply Over.homMk
    . simp_all
      exact ⟪f , t⟫
      --TODO simplify this
    . simp_all -- Looks to be a lean4 bug, see https://github.com/leanprover/lean4/issues/3257
      reduce
      simp

  theorem termToFromSlice {Γ Δ : C} {T : Ty Δ}
    (f : Γ ⟶ Δ)
    (sliceArr : (CategoryTheory.Over.mk f) ⟶ (CategoryTheory.Over.mk (CwF.p (T := T))))
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
