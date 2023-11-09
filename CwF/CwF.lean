import CwF.Fam
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.Data.Opposite
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.Logic.Unique

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
  notation:60 T "⦃" θ "⦄"  => tySub T θ

  -- Definition fo substitution on terms
  -- Like for types, but the resulting term also has the substitution applied
  -- in its type
  def tmSub  {Γ Δ : C} {T : Ty Δ} ( t : Tm T )  (θ : Γ ⟶ Δ) : Tm (T⦃θ⦄) :=
    mapFam (TmTy.F.map θ.op) t

  -- Notation for substitution on terms
  notation:60 t "⦃" θ "⦄"  => tmSub t θ

  --Helpful functions to cast based on subst and type equalities
  abbrev castTm {Γ : C} {S T : Ty Γ} (t : Tm T) (eq : S = T) : Tm S :=
    cast (by aesop) t

  abbrev castTmSub {Γ Δ : C} {f g : Δ ⟶ Γ} {T : Ty Γ} (t: Tm (T⦃f⦄)) (eq : f = g)
    : Tm (T⦃g⦄) :=
    cast (by aesop) t


  notation:500 "↑ₜ" t => castTm t (by aesop)
  notation:50 s "=ₜ" t => s = (↑ₜ t)

  theorem castSymm {Γ : C} {S T : Ty Γ} {s : Tm S} {t : Tm T} {eq : S = T} (eq2 : s = castTm t eq) :
    t =ₜ s := by
    aesop

  @[simp]
  theorem castSub {Γ Δ : C} {S T : Ty Γ} {t : Tm T} {eq : S = T} {f : Δ ⟶ Γ}  :
    castTm t eq ⦃ f ⦄ = castTm (t⦃f⦄) (by aesop) := by aesop

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
  theorem tmSubId {Γ : C} {T : Ty Γ} (t : Tm T) : (t⦃𝟙 Γ⦄) =ₜ t := by
    simp [tySub, tmSub]
    have eq := mapCast t (symm (TmTy.F.map_id (Opposite.op Γ)))
    aesop_cat

  @[simp]
  theorem tmSubComp {Γ Δ Ξ : C} {T : Ty Γ} {f : Δ ⟶ Γ} {g : Ξ ⟶ Δ} {t : Tm T}
  : ((t⦃f⦄)⦃g⦄) =ₜ (t⦃g ≫ f⦄ )  := by
    simp [tySub, tmSub]
    have eq := mapCast t ((TmTy.F.map_comp f.op g.op))
    aesop_cat


  @[simp]
  theorem tmSubCast {Γ Δ : C} {T : Ty Γ} {f g : Δ ⟶ Γ} {t : Tm T} (eq : f = g) : t⦃f⦄ = ↑ₜ t⦃g⦄ := by aesop


  -- Helpful lemma: equal types have equal sets of terms
  -- theorem tmEq {Γ : C} {S T : Ty Γ} (eq : S = T ) : Tm S = Tm T := by aesop

end

-- A CwF has a type-term structure,
-- plus context-extension, substitution extension, and a terminal object
class CwF (C : Type u) [Category.{v} C] [TmTy C] : Type _ where
  -- Empty context
  empty : C
  -- Empty context is terminal
  emptyUnique : (Γ : C) → Unique (Γ ⟶ empty)
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
    → v⦃ext f t⦄ = castTm t (ext_pHelper)
  -- The extension is unique

  ext_unique : {Γ Δ : C} → {T : Ty Γ} → (f : Δ ⟶ Γ)
    → (t : Tm (tySub T f)) → (g : _) → g ≫ p = f
    → (tyEq : _)
    → (v⦃g⦄ = castTm t tyEq)
    → g = ext f t


-- Any CwF is a terminal category
instance (C : Type u) [Category.{v} C] [TmTy C] [CwF C] : Limits.HasTerminal C :=
  Limits.IsTerminal.hasTerminal (Limits.IsTerminal.ofUnique (h := CwF.emptyUnique))

notation:5  "‼"  => CwF.empty
notation:100 Γ "▹" T => CwF.snoc Γ T
notation:100 "⟪" θ "," t "⟫" => CwF.ext θ t
attribute [simp] CwF.ext_p CwF.ext_v

