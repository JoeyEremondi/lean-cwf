
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.NatTrans
import Mathlib.CategoryTheory.Comma.Over
import Mathlib.CategoryTheory.Comma.Basic
import Mathlib.Data.Opposite
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.Logic.Unique
import Mathlib.CategoryTheory.Category.Basic



import CwF.Fam
import CwF.CwF
import CwF.Properties
import CwF.Util


open CategoryTheory
open CwFExt
open TmTy

universe u v u2
section


structure CwFCat : Type _ where
  Ctx : Type u
  [exCat : Category.{v} Ctx]
  [exCwF : CwF Ctx]


instance : Coe CwFCat (Type _) where
  coe C := C.Ctx

attribute [instance] CwFCat.exCat
attribute [instance] CwFCat.exCwF

structure TmTyMorphism (C D : CwFCat) : Type _ where
  CtxF : CategoryTheory.Functor.{v,v,u,u} C.Ctx D.Ctx
  natTrans :
    NatTrans
      tmTyF --C's functor
      (CategoryTheory.Functor.comp  (Functor.op CtxF) tmTyF ) -- D's functor






def MapCtx {C D : CwFCat} (F : TmTyMorphism C D) (Γ : C.Ctx) : D.Ctx :=
  F.CtxF.obj Γ

def MapSub {C D : CwFCat} (F : TmTyMorphism C D) {Γ Δ : C.Ctx}
  (θ : Δ ⟶ Γ)
  : (MapCtx F Δ) ⟶ (MapCtx F Γ) :=
  F.CtxF.map θ

@[simp]
theorem MapSubComp {C D : CwFCat} (F : TmTyMorphism C D) {Γ Δ Ξ : C.Ctx}
  (f : Ξ ⟶ Δ) (g : Δ ⟶ Γ )
  : (MapSub F f) ≫ (MapSub F g) = MapSub F (f ≫ g) :=
    Eq.symm (F.CtxF.map_comp f g)

theorem MapSubId {C D : CwFCat} (F : TmTyMorphism C D) {Γ : C.Ctx}
  : MapSub F (𝟙 Γ) = 𝟙 (MapCtx F Γ) :=
    F.CtxF.map_id Γ

def MapTy {C D : CwFCat} (F : TmTyMorphism C D)
  {Γ : C.Ctx}
  (T : Ty Γ)
  : Ty (MapCtx F Γ) := mapIx (F.natTrans.app (Opposite.op Γ )) T


def MapTm {C D : CwFCat} (F : TmTyMorphism C D)
 {Γ : C.Ctx}
  {T : Ty Γ}
  (t : Tm T)
  : Tm (MapTy F T) := mapFam (F.natTrans.app (Opposite.op Γ )) t

-- section
--   variable {C : CwFCat} { D : CwFCat} (F : TmTyMorphism C D)
--   -- attribute [-instance] CwF.cwfExt
--   -- attribute [-instance] CwF.tmTy
--   -- attribute [-instance] CwFCat.exCwF

--   local instance (priority := default + 2) MapTmTy
--     : TmTy (C.Ctx) where
--     tmTyF := CategoryTheory.Functor.comp (Functor.op F.CtxF) D.exCwF.tmTy.tmTyF

--   def ExpCwFExt (C : Type u) (cat : Category C) (tt : @TmTy C cat) : Type _ :=
--     @CwFExt C cat tt


--   def mkExpCwFExt (C : Type u) (cat : Category C) (tt : @TmTy C cat)
--     (empty : C)
--     (snoc : (Γ : C) → Ty Γ → C)
--     (p : {Γ : C} → {T : Ty Γ} → snoc Γ T ⟶ Γ)
--     (v : {Γ : C} → {T : Ty Γ} → Tm (T⦃p⦄ : Ty (snoc Γ T)))
--     (ext : {Γ Δ : C} → {T : Ty Γ} → (f : Δ ⟶ Γ) → (t : Tm (T⦃f⦄)) → Δ ⟶ snoc Γ T)
--   : (ExpCwFExt C cat tt) := ⟨empty, snoc, p, v, ext ⟩

--   def MapExt : ExpCwFExt (C.Ctx) _ (MapTmTy F) := by
--     fapply mkExpCwFExt C _ (MapTmTy F)
--     . exact C.exCwF.cwfExt.empty
--     . intros Γ T
--       reduce at T
--       fapply D.exCwF.cwfExt.snoc
--   end


@[simp]
def MapTyCommut {C D : CwFCat} (F : TmTyMorphism C D)
  {Δ Γ : C.Ctx}
  {T : Ty Γ}
  {θ : Δ ⟶ Γ}
  : MapTy F (T⦃θ⦄) = (MapTy F T)⦃MapSub F θ⦄ :=
    congrFun (congrArg mapIx (F.natTrans.naturality (Opposite.op θ))) T

@[simp]
def MapTmCommut {C D : CwFCat} (F : TmTyMorphism C D)
  {Δ Γ : C.Ctx}
  {T : Ty Γ}
  {t : Tm T}
  {θ : Δ ⟶ Γ}
  : (MapTm F (t⦃θ⦄)) = castTm  ((MapTm F t)⦃MapSub F θ⦄) (by rw [MapTyCommut]) := by
    -- let tyEq := MapTyCommut F (T := T) (θ := θ)
    -- let ceq
    --   := castSub (t := MapTm F t) (eq := by aesop) (f := MapSub F θ)
    let nat := F.natTrans.naturality (Opposite.op θ)
    let mapnat :=  (HEq.symm (hCong (refl mapFam) nat))
    let mapnat_T := hCongFunImplicit T (by simp) mapnat
    let mapnat_Tt := hCongFun t (by simp) mapnat_T
    let mapnat_eq := Eq.symm (eq_cast_of_heq mapnat_Tt)
    eapply Eq.trans mapnat_eq
    simp [MapTm, mapFam, castSub]
    apply Subtype.ext
    aesop_cat
    -- simp
    -- trans
    -- . skip
    -- . exact (
    -- apply Eq.trans _
    -- cases tyEq
    -- fapply congrArg mapFam

-- set_option pp.explicit true

/-- We use HSub instead of cast sub because we didn't build up a bunch of infrastructure for dealing with-/
/-casts in types and substitutions -/
/-but we have Context equality (which we avoid in the CwF module), which induces casts on types-/
class PreservesCwF {C D : CwFCat} (F : TmTyMorphism C D)  : Type _ where
  snocPreserve :
    {Γ : C.Ctx}
    → {T : Ty Γ}
    → MapCtx F (Γ ▹ T) ≅ (MapCtx F Γ) ▹ (MapTy F T) := by aesop_cat
  pPreserve :
    {Γ : C.Ctx}
    → {T : Ty Γ}
    → MapSub F (p (T := T))
      = snocPreserve.hom ≫ p
  vPreserve :
    {Γ : C.Ctx}
    → {T : Ty Γ}
    → (MapTm F (CwFExt.v (T := T)))
     =ₜ (v (T := MapTy F T))⦃snocPreserve.hom⦄  := by aesop_cat

open PreservesCwF

attribute [simp] PreservesCwF.snocPreserve
attribute [simp] PreservesCwF.pPreserve
attribute [simp] PreservesCwF.vPreserve

@[aesop unsafe apply]
def pPreserve' {C D : CwFCat} {F : TmTyMorphism C D} [PreservesCwF F]
    {Γ : C.Ctx}
    {T : Ty Γ}
    : p (T := MapTy F T) =  snocPreserve.inv ≫ MapSub F (p (T := T))
      := by aesop

def vPreserve'  {C D : CwFCat} {F : TmTyMorphism C D} [PreservesCwF F]
    {Γ : C.Ctx}
    {T : Ty Γ}
    : (v (T := MapTy F T)) =
       castTm (MapTm F (CwFExt.v (T := T)))⦃snocPreserve.inv⦄ (by aesop) := by simp

set_option maxHeartbeats 1000000

def extPreserveCast (C D : CwFCat) {F : TmTyMorphism C D} [pres : PreservesCwF F]
  {Γ Δ : C.Ctx} {T : Ty Γ} {f : Δ ⟶ Γ} {t : Tm (T⦃f⦄)}
  : MapSub F (ext f t) ≫ snocPreserve.hom
    = (ext (MapSub F f) (cast (by aesop) (MapTm F t)))  := by
    let vP := cast_moveL (pres.vPreserve (T := T))
    fapply CwFProp.ext_unique
    . simp [<- pPreserve]
    . rw [vPreserve']
