import LeanCwf.Fam
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.Data.Opposite

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

  -- Subsitution by the identity has no effect
  @[simp]
  theorem tySubId {Γ : C} (T : Ty Γ) : T⦃𝟙 Γ⦄ = T  := by
    simp [tySub]

  -- Substitution a composite is the same as composing substitutions
  @[simp]
  theorem tySubComp {Γ Δ Ξ : C} {T : Ty Γ} {f : Δ ⟶ Γ} {g : Ξ ⟶ Δ} : T⦃g ≫ f⦄ = (T⦃f⦄)⦃g⦄   := by
    simp [tySub]


  -- Same laws but for substitution on terms instead of types
  @[simp]
  theorem tmSubId {Γ : C} {T : Ty Γ} (t : Tm T) : HEq (t⦃𝟙 Γ⦄ₜ) t  := by
    simp [tySub, tmSub]
    rw [TmTy.F.map_id]
    simp_all only [mapIxId, mapFamId, heq_eq_eq]

  @[simp]
  theorem tmSubComp {Γ Δ Ξ : C} {T : Ty Γ} {f : Δ ⟶ Γ} {g : Ξ ⟶ Δ} {t : Tm T} : HEq (t⦃g ≫ f⦄ₜ ) ((t⦃f⦄ₜ)⦃g⦄ₜ)   := by
    simp [tySub, tmSub]
    rw [TmTy.F.map_comp]
    apply mapFamComp

  -- -- Helpful lemma: equal types have equal sets of terms
  -- theorem tmEq {Γ : C} {S T : Ty Γ} (eq : S = T ) : Tm S = Tm T := by aesop


-- A CwF has a type-term structure,
-- plus context-extension, substitution externsn, and an initial object
class CwF (C : Type u) [Category.{v} C] [TmTy C] : Type _ where
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
    → (f : Δ ⟶ Γ) → (t : Tm (tySub T f))
    → (ext f t) ≫ p = f

  --An extended substitution, applied to the newly generated variable, produces
  --the term by which the subsitution was extended
  ext_v : {Γ Δ : C} → {T : Ty Γ} → (f : Δ ⟶ Γ) → (t : Tm (tySub T f)) → HEq (v⦃ext f t⦄ₜ) t
  -- The extension is unique
  -- ext_unique : {Γ Δ : C} → {T : Ty Γ} → (f : Δ ⟶ Γ) → (t : Tm (tySub T f)) → (g : _) → g ≫ p = f → HEq (v⦃g⦄ₜ) t → g = ext f t

  -- If you compose with an extension, this is the same as extending by the composition,
  -- except that you also end up substituting in the term you're extending by.
  -- Unfortunate ugliness due to the fact that Tm⦃g ≫ f⦄ is not definitionally equal to tm⦃f⦄⦃g⦄
  ext_nat : {Γ Δ Ξ : C} → {T : Ty Γ}
    → (f : Δ ⟶ Γ)
    → (g : Ξ ⟶ Δ)
    → (t : Tm (T⦃f⦄))
    → (g ≫ ext f t) = (ext (g ≫ f) (cast (symm (congrArg Tm tySubComp)) (t⦃g⦄ₜ)))
  -- If you take a weaning and extend it with the newly introduced variable, you get the identity,
  -- because it just replaces each v with v
  ext_id : {Γ : C} → {T : Ty Γ} → ext p v = 𝟙 (snoc Γ T)

notation Γ "⬝" T => CwF.snoc Γ T
notation "⟪" θ "," t "⟫" => CwF.ext θ t


theorem ext_unique {Γ Δ : C} [inst : CwF C] {T : Ty Γ}
  (f : Δ ⟶ Γ) (t : Tm (T⦃f⦄)) (g : Δ ⟶ Γ ⬝ T)
  (pfComp : f = (g ≫ CwF.p)) (pfv : t (cast (tmEq pfComp) CwF.v⦃g⦄ₜ) )
  : g = ⟪f,t⟫ := by
--   cases (pfComp) with
--   | refl =>
--     aesop
  -- rw [pfComp]
  -- rw [pfComp] at *
  -- simp [pfv] at *
--     have pfTyComp : T⦃g ≫ CwF.p⦄ = T⦃CwF.p⦄⦃g⦄ := tySubComp
--     rw [pfTyComp] at t
--     have pfv2 : t = CwF.v⦃g⦄ₜ := by simp [pfv]
-- end
