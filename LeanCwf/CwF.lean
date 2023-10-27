import LeanCwf.Fam
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.Data.Opposite
import Mathlib.CategoryTheory.Limits.Shapes.Terminal

open CategoryTheory

universe u v u2


-- Terms and Types in a CwF, without the comprehension structure
-- A CwF over C has a Fam-valued presheaf
-- We interpret objects of C as contexts
class TmTy (C : Type u) [Category.{v} C] : Type ((max v u+1)+1) where
  F : Functor Cᵒᵖ Fam.{u}

section
  variable {C : Type u} [Category.{v}  C] [TmTy.{u,v} C]

  -- The index set of the functor F gives types over a given context
  def Ty (Γ : C) : Type u :=  ixSet (TmTy.F.obj (Opposite.op Γ))

  -- The family for a given context and type gives the set of
  -- terms of that type
  def Tm {Γ : C} (T : Ty Γ) : Type u := famFor (TmTy.F.obj (Opposite.op Γ)) T

  -- Definition of substitution for types
  -- Any C-arrow can be lifted to a substitution function on types
  -- by the functoral structure of F.
  def tySub {Δ Γ: C} (T : Ty Δ) (θ : Γ ⟶ Δ) : Ty Γ :=
    mapIx (TmTy.F.map θ.op) T

  -- Notation for substitution on types
  notation T "⦃" θ "⦄"  => tySub T θ

  -- Definition fo substitution on terms
  -- Like for types, but the resulting term also has the substitution applied
  -- in its type
  def tmSub  {Γ Δ : C} {T : Ty Δ} ( t : Tm T )  (θ : Γ ⟶ Δ) : Tm (T⦃θ⦄) :=
    mapFam (TmTy.F.map θ.op) t

  -- Notation for substitution on terms
  notation t "⦃" θ "⦄ₜ"  => tmSub t θ

  --Helpful functions to cast based on subst and type equalities
  abbrev castTm {Γ : C} {S T : Ty Γ} (t : Tm T) (eq : S = T) : Tm S :=
    cast (by aesop) t

  abbrev castTmSub {Γ Δ : C} {f g : Δ ⟶ Γ} {T : Ty Γ} (t: Tm (T⦃f⦄)) (eq : f = g)
    : Tm (T⦃g⦄) :=
    cast (by aesop) t


  notation "↑ₜ" t => castTm t (by aesop)
  notation s "=ₜ" t => s = (↑ₜ t)

  theorem castSymm {Γ : C} {S T : Ty Γ} {s : Tm S} {t : Tm T} {eq : S = T} (eq2 : s = castTm t eq) :
    t =ₜ s := by
    aesop

  @[simp]
  theorem castSub {Γ Δ : C} {S T : Ty Γ} {t : Tm T} {eq : S = T} {f : Δ ⟶ Γ}  :
    (castTm t eq) ⦃ f ⦄ₜ = castTm (t⦃f⦄ₜ) (by aesop) := by aesop

  @[simp]
  theorem castCast  {Γ : C} {S T U: Ty Γ} {s : Tm S} {t : Tm U} {eq : S = T} {eq2 : T = U} :
    (castTm (castTm t eq2) eq) = castTm t (Eq.trans eq eq2) := by aesop

  @[simp]
  theorem castEq  {Γ : C} {S T : Ty Γ} {s : Tm S} {s t : Tm T} {eq : S = T}  :
    castTm s eq = castTm t eq ↔ s = t := by aesop

  -- Subsitution by the identity has no effect
  @[simp]
  theorem tySubId {Γ : C} {T : Ty Γ} : T⦃𝟙 Γ⦄ = T  := by
    simp [tySub]

  -- Substitution a composite is the same as composing substitutions
  @[simp]
  theorem tySubComp {Γ Δ Ξ : C} {T : Ty Γ} {g : Δ ⟶ Γ} {f : Ξ ⟶ Δ} :  (T⦃g⦄)⦃f⦄ = T⦃f ≫ g⦄   := by
    simp [tySub]

  -- Same laws but for substitution on terms instead of types
  @[simp]
  theorem tmSubId {Γ : C} {T : Ty Γ} (t : Tm T) : (t⦃𝟙 Γ⦄ₜ) =ₜ t := by
    simp [tySub, tmSub]
    have eq := mapCast t (symm (TmTy.F.map_id (Opposite.op Γ)))
    aesop_cat

  @[simp]
  theorem tmSubComp {Γ Δ Ξ : C} {T : Ty Γ} {f : Δ ⟶ Γ} {g : Ξ ⟶ Δ} {t : Tm T}
  : ((t⦃f⦄ₜ)⦃g⦄ₜ) =ₜ (t⦃g ≫ f⦄ₜ )  := by
    simp [tySub, tmSub]
    have eq := mapCast t ((TmTy.F.map_comp f.op g.op))
    aesop_cat


  -- Helpful lemma: equal types have equal sets of terms
  -- theorem tmEq {Γ : C} {S T : Ty Γ} (eq : S = T ) : Tm S = Tm T := by aesop

end

-- A CwF has a type-term structure,
-- plus context-extension, substitution extension, and a terminal object
class CwF (C : Type u) [Category.{v} C] [TmTy C] [Limits.HasTerminal C] : Type _ where
  -- Context extension
  snoc : (Γ : C) → Ty Γ → C
  --The projection substitution
  --Applying this weakens a type/term
  --by introducing an unused variable
  p : {Γ : C} → {T : Ty Γ} → snoc Γ T ⟶ Γ
  --The variable introduced by extending a context
  v : {Γ : C} → {T : Ty Γ} → Tm (T⦃p⦄ : Ty (snoc Γ T))
  -- Every morphism can be extended to extended contexts
  -- This basically says "do whatever f does, and replace the newly introduced variable with t"
  ext : {Γ Δ : C} → {T : Ty Γ} → (f : Δ ⟶ Γ) → (t : Tm (T⦃f⦄)) → Δ ⟶ snoc Γ T
  -- Such an extension is the unique morphism satisfying certain laws
  -- Extending and composing with p cancels: if you introduce an unused variable then replace it with t,
  -- you get the original substitution
  ext_p : {Γ Δ : C} → {T : Ty Γ}
    → {f : Δ ⟶ Γ} → {t : Tm (tySub T f)}
    → (ext f t) ≫ p = f

  -- Can be derived from existing equalities, but if we postulate it
  -- it's easier to express the type of later things
  ext_pHelper : {Γ Δ : C} → {T : Ty Γ}
    → {f : Δ ⟶ Γ} → {t : Tm (tySub T f)} → {T : Ty _}
    → (T⦃p⦄⦃ext f t⦄)  = T⦃f⦄

  --An extended substitution, applied to the newly generated variable, produces
  --the term by which the subsitution was extended
  ext_v : {Γ Δ : C} → {T : Ty Γ} → (f : Δ ⟶ Γ) → (t : Tm (tySub T f))
    → v⦃ext f t⦄ₜ = castTm t (ext_pHelper)
  -- The extension is unique

  ext_unique : {Γ Δ : C} → {T : Ty Γ} → (f : Δ ⟶ Γ)
    → (t : Tm (tySub T f)) → (g : _) → g ≫ p = f
    → (tyEq : _)
    → (v⦃g⦄ₜ = castTm t tyEq)
    → g = ext f t


notation Γ "▸" T => CwF.snoc Γ T
notation "⟪" θ "," t "⟫" => CwF.ext θ t
attribute [simp] CwF.ext_p CwF.ext_v


section
  variable {C : Type u} [Category.{v}  C] [TmTy.{u,v} C] [Limits.HasTerminal C] [CwF C]


  -- If you compose with an extension, this is the same as extending by the composition,
  -- except that you also end up substituting in the term you're extending by.
  -- Unfortunate ugliness due to the fact that Tm⦃g ≫ f⦄ is not definitionally equal to tm⦃f⦄⦃g⦄
  @[simp]
  theorem ext_nat {Γ Δ Ξ : C} {T : Ty Γ}
    (f : Δ ⟶ Γ)
    (g : Ξ ⟶ Δ)
    (t : Tm (T⦃f⦄))
    : (g ≫ ⟪f , t⟫) = ⟪g ≫ f , (↑ₜ t⦃g⦄ₜ) ⟫ := by
      fapply CwF.ext_unique <;> simp_all
      have eq2 := castSymm (tmSubComp (f := ⟪f , t⟫) (g := g) (t := CwF.v))
      rw [eq2]
      simp_all


  -- If you take a weaning and extend it with the newly introduced variable, you get the identity,
  -- because it just replaces each v with v
  @[simp]
  theorem ext_id {Γ : C} {T : Ty Γ} : ⟪CwF.p , CwF.v⟫ = 𝟙 (Γ ▸ T) := by
    symm
    fapply CwF.ext_unique <;> simp_all



---- Terms and Sections
-- There is an equivalence between terms of Tm T
-- and sections p_T

  -- Turn a term into the substitution that replaces v with that term
  abbrev toSub {Γ : C} {T : Ty Γ} (t : Tm T) : Γ ⟶ (Γ ▸ T) :=
    ⟪ 𝟙 _ , ↑ₜ t ⟫

  -- That subsitution is a section of p
  def toSection {Γ : C} {T : Ty Γ} (t : Tm T) : SplitEpi (CwF.p (T := T)) :=
    ⟨ toSub t , by simp_all ⟩

  -- Get a term out of any section of p
  def toTerm {Γ : C} {T : Ty Γ} (epi : SplitEpi (CwF.p (T := T))) : Tm T :=
    ↑ₜ ((CwF.v ) ⦃ epi.section_ ⦄ₜ)

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

  -- Weakening
  -- Lifts any substitution to work on an extended context
  abbrev wk {Γ Δ : C} {f : Δ ⟶ Γ} {T : Ty Γ} : (Δ ▸ T⦃f⦄) ⟶ (Γ ▸ T) :=
    ⟪CwF.p (T := T⦃f⦄) ≫ f , ↑ₜ CwF.v ⟫
