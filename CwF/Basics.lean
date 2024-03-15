import CwF.Fam
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
-- import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.Data.Opposite
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.Logic.Unique

import CwF.Util

open CategoryTheory
open Fam



namespace CwF

universe u v u2


-- Terms and Types in a CwF, without the comprehension structure
-- A CwF over Ctx has a Fam-valued presheaf
-- We interpret objects of Ctx as contexts.
class TmTy (Ctx : Type u) [Category.{v} Ctx] : Type (max u v (u2+1)) where
  tmTyFam : CategoryTheory.Functor Ctxᵒᵖ Fam.{u2}

open TmTy

section
  variable {C : Type u} [cat : Category.{v}  C] [tmTy : TmTy.{u,v} C]

  -- The index set of the functor F gives types over a given context
  def Ty (Γ : C) : Type u :=  ixSet (tmTyFam.obj (Opposite.op Γ))

  -- Ty is a contra-functor to Type u
  def TyFunctor : CategoryTheory.Functor Cᵒᵖ (Type u) :=
    Functor.comp tmTyFam  projIx

  -- The family for a given context and type gives the set of
  -- terms of that type
  def Tm {Γ : C} (T : Ty Γ) : Type u := famFor (tmTyFam.obj (Opposite.op Γ)) T

  -- Definition of substitution for types
  -- Any C-arrow can be lifted to a substitution function on types
  -- by the functoral structure of F.
  def tySub {Δ Γ: C} (T : Ty Δ) (θ : Γ ⟶ Δ) : Ty Γ :=
    mapIx (tmTyFam.map θ.op) T

  -- Notation for substitution on types
  notation:max T "⦃" θ "⦄"  => tySub T θ

  -- Definition fo substitution on terms
  -- Like for types, but the resulting term also has the substitution applied
  -- in its type
  def tmSub  {Γ Δ : C} {T : Ty Δ} ( t : Tm T )  (θ : Γ ⟶ Δ) : Tm (T⦃θ⦄) :=
    mapFam (tmTyFam.map θ.op) t

  -- Notation for substitution on terms
  notation:max t "⦃" θ "⦄"  => tmSub t θ

  --Helpful functions to cast based on subst and type equalities
  abbrev castTm {Γ : C} {S T : Ty Γ} (t : Tm T) (eq : S = T) : Tm S :=
    cast (by aesop) t

  abbrev castTmSub {Γ Δ : C} {f g : Δ ⟶ Γ} {T : Ty Γ} (t: Tm (T⦃f⦄)) (eq : f = g)
    : Tm (T⦃g⦄) :=
    cast (by aesop) t

  abbrev eqModCast {Γ : C} {S T : Ty Γ} (s : Tm S) (t : Tm T) (eq : S = T)
    : Prop :=
    s = castTm t (by aesop)



  notation:500 "↑ₜ" t => castTm t (by aesop)
  notation:50 s "=ₜ" t => s = (↑ₜ t)

  @[aesop unsafe 50% apply]
  theorem castSymm {Γ : C} {S T : Ty Γ} {s : Tm S} {t : Tm T} {eq : S = T} :
    (s =ₜ t) ↔ (t =ₜ s) := by
    constructor <;> aesop

  @[simp]
  theorem castSub {Γ Δ : C} {S T : Ty Γ} {t : Tm T} {eq : S = T} {f : Δ ⟶ Γ}  :
    (castTm t eq )⦃ f ⦄ = castTm (t⦃f⦄) (by aesop) := by aesop


  @[simp]
  theorem castCast  {Γ : C} {S T U: Ty Γ} {s : Tm S} {t : Tm U} {eq : S = T} {eq2 : T = U} :
    (castTm (castTm t eq2) eq) = castTm t (Eq.trans eq eq2) := by aesop

  @[simp]
  theorem castEq  {Γ : C} {T : Ty Γ}  {s t : Tm T}   :
    castTm s (rfl) = castTm t rfl ↔ s = t := by aesop

  theorem castTrans {Γ : C} {S T U : Ty Γ} {s : Tm S} {t : Tm T} {u : Tm U}
    {eq1 : S = T} {eq2 : T = U}
    (eqst : s =ₜ t)  (eqtu : t =ₜ u) : s =ₜ u := by aesop
    


  @[simp]
  theorem castCastGen {X Y Z : Type u} {x : X} {y : Y}
    {eq1 : X = Z} {eq2 : Y = Z}
    : cast eq1 x = cast eq2 y ↔ x = cast (by aesop) y := by aesop

  @[simp]
  theorem castTyOutOfSub { Γ1 Γ2 : C} {θ : Δ ⟶ Γ1} {T : Ty Γ2}
    {eq : Γ1 = Γ2 }
    : T⦃cast (α := Δ ⟶ Γ1) (β := Δ ⟶ Γ2) (by rw [eq]) θ⦄
      = tySub (cast (by aesop) T) θ  := by aesop

  @[simp]
  theorem castOutOfSub {Δ Γ1 Γ2 : C} {θ : Δ ⟶ Γ1} {T : Ty Γ2} {t : Tm T}
    {eq : Γ1 = Γ2 }
    : t⦃cast (α := Δ ⟶ Γ1) (β := Δ ⟶ Γ2) (by rw [eq]) θ⦄
      =ₜ castTm
        (S := tySub T (cast (by rw [eq]) θ)) (T := tySub (cast (by rw [eq]) T) θ)
        ((cast   (by aesop) t )⦃θ⦄)
        (by aesop):= by aesop


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
    have eq := mapCast t (symm (tmTyFam.map_id (Opposite.op Γ)))
    aesop_cat

  @[simp]
  theorem tmSubComp {Γ Δ Ξ : C} {T : Ty Γ} {f : Δ ⟶ Γ} {g : Ξ ⟶ Δ} {t : Tm T}
  : ((t⦃f⦄)⦃g⦄) =ₜ (t⦃g ≫ f⦄ )  := by
    simp [tySub, tmSub]
    have eq := mapCast t ((tmTyFam.map_comp f.op g.op))
    aesop_cat

  @[aesop unsafe apply]
  theorem tmSubComp' {Γ Δ Ξ : C} {T : Ty Γ} {f : Δ ⟶ Γ} {g : Ξ ⟶ Δ} {t : Tm T}
  :  (t⦃g ≫ f⦄ ) =ₜ ((t⦃f⦄)⦃g⦄)  := by simp

  theorem tySubExt {Γ Δ Ξ : C} {f : Δ ⟶ Γ } {g : Ξ ⟶ Γ } {T : Ty Γ } (ctxEq : Δ = Ξ)
    (eq : HEq f g)
    : HEq T⦃f⦄ T⦃g⦄ := by aesop


  @[simp]
  theorem tmSubCast {Γ Δ : C} {T : Ty Γ} {f g : Δ ⟶ Γ} {t : Tm T} (eq : f = g) : t⦃f⦄ = ↑ₜ t⦃g⦄ := by aesop

  theorem tmHeq {Γ Δ : C} {S : Ty Γ} {T : Ty Δ} (eq : Γ = Δ) (heq : HEq S  T)
    : Tm (Γ := Γ) S = Tm  T := by aesop

  -- Isomorphic contexts have isomorphic sets of types
  def ctxIsoToType {Γ Δ : C} (iso : Γ ≅ Δ) : Ty Γ ≅ Ty Δ :=  by
    simp [Ty]
    apply Functor.mapIso TyFunctor
    apply Iso.op
    exact (iso.symm)

  @[simp]
  theorem ctxIsoTypeSubHom {Γ Δ : C} (iso : Γ ≅ Δ) {T : Ty Γ}
    : (ctxIsoToType iso).hom  T = T⦃iso.inv⦄ :=  by aesop

  @[simp]
  theorem ctxIsoTypeSubInv {Γ Δ : C} (iso : Γ ≅ Δ) {T : Ty Δ}
    : (ctxIsoToType iso).inv  T = T⦃iso.hom⦄ :=  by aesop

-- Context isomorphisms can be transported over term sets

  theorem ctxIsoToTm {Γ Δ : C} (iso : Γ ≅ Δ) {T : Ty Γ} :
    Tm T ≅ Tm ((ctxIsoToType iso).hom T)  where
    hom t :=  by
      simp
      apply tmSub t
    inv t := by
      let tsub := t⦃iso.hom⦄
      simp at tsub
      assumption
    hom_inv_id := by
      funext t
      simp
      let teq := tmSubId t
      rw [castSymm] at teq
      apply Eq.trans _ (Eq.symm teq) <;> try aesop_cat
      symm
      rw [castSymm, castCast] <;> try aesop_cat
      apply tmSubCast
      simp
    inv_hom_id := by
      funext t
      simp
      let teq := tmSubId t
      rw [castSymm] at teq
      apply Eq.trans _ (Eq.symm teq) <;> try aesop_cat
      symm
      rw [castSymm, castCast] <;> try aesop_cat
      apply tmSubCast
      simp
      

end


class CwFExt (C : Type u) [Category.{v} C]  [tmTy : TmTy C] : Type _  where
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


open CwFExt
notation:max Γ:1000 "▹" T:max => snoc Γ T
notation:max "⟪" θ "," t "⟫" => ext θ t


class CwFProp (C : Type u) [catInst : Category.{v} C] [tmTy : TmTy C] [cwf : CwFExt C] : Prop where
  -- The extension is the unique morphism satisfying certain laws
  -- Extending and composing with p cancels: if you introduce an unused variable then replace it with t,
  -- you get the original substitution
  ext_p : {Γ Δ : C} → {T : Ty Γ}
    → {f : Δ ⟶ Γ} → {t : Tm (T⦃f⦄)}
    → ⟪f , t⟫ ≫ p = f := by aesop_cat

  -- Can be derived from existing equalities, but if we postulate it
  -- it's easier to express the type of later things
  ext_pHelper : {Γ Δ : C} → {S : Ty Γ}
    → {f : Δ ⟶ Γ} → {t : Tm (S⦃f⦄)} → {T : Ty _}
    → (T⦃p⦄⦃ext f t⦄)  = T⦃f⦄ :=
    fun {Γ Δ} {S} {f} {t} {T} =>
      of_eq_true ((congrArg (fun x => x = T⦃f⦄) (tySubComp.trans (congrArg (tySub T) ext_p))).trans (eq_self T⦃f⦄))

  --An extended substitution, applied to the newly generated variable, produces
  --the term by which the subsitution was extended
  ext_v : {Γ Δ : C} → {T : Ty Γ} → (f : Δ ⟶ Γ) → (t : Tm (T⦃f⦄))
    → v⦃⟪f,t⟫⦄ = castTm t (ext_pHelper) := by aesop_cat
  -- The extension is unique

  ext_unique : {Γ Δ : C} → {T : Ty Γ} → (f : Δ ⟶ Γ)
    → (t : Tm T⦃f⦄) → (g : _)
    → (peq : g ≫ p = f)
    → (v⦃g⦄ = castTm t (by aesop))
    → g = ⟪f,t⟫ := by aesop_cat

attribute [simp] CwFProp.ext_p CwFProp.ext_v

open CwFProp

-- A CwF has a type-term structure,
-- plus context-extension, substitution extension, and a terminal object
class CwF (C : Type u) [cat : Category.{v} C]  : Type _ where
  -- Empty context
  empty : C
  -- Unique morphism to the empty substitution
  toEmpty {Γ : C} : Γ ⟶ empty
  -- Empty context is terminal
  emptyTerminal : Limits.IsTerminal empty
  [tmTy : TmTy C]
  [cwfExt : CwFExt C]
  [cwfProp : CwFProp C]


-- notation:5  "‼"  => CwF.empty
-- notation:5  "‼"  => CwF.toEmpty

attribute [instance] CwF.tmTy CwF.cwfExt CwF.cwfProp


-- Any CwF is a terminal category
instance (C : Type u) [Category.{v} C] [CwF C] : Limits.HasTerminal C :=
  Limits.IsTerminal.hasTerminal CwF.emptyTerminal


attribute [simp] ext_p ext_v


end CwF
