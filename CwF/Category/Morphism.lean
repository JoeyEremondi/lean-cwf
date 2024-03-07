
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

theorem MapSubComp {C D : CwFCat} (F : TmTyMorphism C D) {Γ Δ Ξ : C.Ctx}
  (f : Ξ ⟶ Δ) (g : Δ ⟶ Γ )
  : MapSub F (f ≫ g) = (MapSub F f) ≫ (MapSub F g) :=
    F.CtxF.map_comp f g

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
class PreservesCwF {C D : CwFCat} (F : TmTyMorphism C D)  : Prop where
  snocPreserve :
    {Γ : C.Ctx}
    → {T : Ty Γ}
    → MapCtx F (Γ ▹ T) = (MapCtx F Γ) ▹ (MapTy F T) := by aesop_cat
  pPreserveH :
    {Γ : C.Ctx}
    → {T : Ty Γ}
    → HEq (MapSub F (CwFExt.p (T := T) ))
        (D.exCwF.cwfExt.p (T := MapTy F T)) := by aesop_cat
  -- pPreserveTm :
  --   {Γ : C.Ctx}
  --   → {T : Ty Γ}
  --   → Tm (tySub (MapTy F T) (p (T := MapTy F T))) = Tm (MapTy F T⦃p (T := T)⦄)
  vPreserveH :
    {Γ : C.Ctx}
    → {T : Ty Γ}
    → HEq (MapTm F (CwFExt.v (T := T))) (v (T := MapTy F T)) := by aesop_cat

open PreservesCwF

attribute [simp] PreservesCwF.snocPreserve
attribute [simp] PreservesCwF.pPreserveH
attribute [simp] PreservesCwF.vPreserveH


theorem vPreserveTm  (C D : CwFCat) (F : TmTyMorphism C D) [PreservesCwF F]
    {Γ : C.Ctx}
    {T : Ty Γ}
    : Tm (tySub (MapTy F T) (p (T := MapTy F T))) = Tm (MapTy F T⦃p (T := T)⦄) := by
    fapply tmHeq <;> try aesop_cat
    rw [MapTyCommut]
    fapply tySubExt
    . aesop_cat
    . symm
      apply pPreserveH


theorem pPreserveCast {C D : CwFCat} {F : TmTyMorphism C D} [PreservesCwF F]
    {Γ : C.Ctx}
    {T : Ty Γ}
    :  (MapSub F (CwFExt.p (T := T) ))
       = cast (by aesop) (D.exCwF.cwfExt.p (T := MapTy F T)) := by
       apply eq_of_heq
       apply HEq.trans pPreserveH
       apply heq_of_cast_eq <;> aesop_cat



def extPreserve (C D : CwFCat) {F : TmTyMorphism C D} [PreservesCwF F]
  {Γ Δ : C.Ctx} {T : Ty Γ} {f : Δ ⟶ Γ} {t : Tm (T⦃f⦄)}
  : HEq (MapSub F (ext f t)) (ext (MapSub F f) (↑ₜ (MapTm F t))) := by
    let eqP := C.exCwF.cwfProp.ext_p (T := T) (f := f) (t := t)
    let eqPD := congrArg (MapSub F) eqP
    let eqV := C.exCwF.cwfProp.ext_v (T := T) (f := f) (t := t)
    let eqVD := congrArg (MapTm F) eqV
    simp only [MapSubComp] at eqPD
    simp only [pPreserveCast] at eqPD
    let eqInD := D.exCwF.cwfProp.ext_unique (MapSub F f) _ _ eqPD (by aesop) (eqD)
    apply heq_of_heq_of_eq
    . skip
    . apply eqInD
      . simp
      . aesop_cat
      . simp
    . simp
