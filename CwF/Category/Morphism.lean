
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.NatTrans
import Mathlib.CategoryTheory.Comma.Over
import Mathlib.CategoryTheory.Comma.Basic
import Mathlib.Data.Opposite
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.Logic.Unique
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Types



import CwF.Fam
import CwF.Basics
import CwF.Properties
import CwF.Util

open CategoryTheory
open NatTrans Category Functor

namespace CwF

universe u v u2
section



structure CwFCat : Type _ where
  Ctx : Type u
  [exCat : Category.{v} Ctx]
  [exCwF : CwF Ctx]


instance : Coe CwFCat (Type _) where
  coe C := C.Ctx

attribute [instance] CwFCat.exCat CwFCat.exCwF

structure TmTyMorphism (C D : CwFCat) : Type _ where
  CtxF : CategoryTheory.Functor.{v,v,u,u} C.Ctx D.Ctx
  transSubst :
    NatTrans
      (tmTyFam (Ctx := C)) --C's functor
      (Functor.comp (CtxF.op) (tmTyFam (Ctx := D)) ) -- D's functor






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
  : Ty (MapCtx F Γ) := mapIx (F.transSubst.app (Opposite.op Γ )) T


def MapTm {C D : CwFCat} (F : TmTyMorphism C D)
 {Γ : C.Ctx}
  {T : Ty Γ}
  (t : Tm T)
  : Tm (MapTy F T) := mapFam (F.transSubst.app (Opposite.op Γ )) t

@[simp]
def MapTyCommut {C D : CwFCat} (F : TmTyMorphism C D)
  {Δ Γ : C.Ctx}
  {T : Ty Γ}
  {θ : Δ ⟶ Γ}
  : MapTy F (T⦃θ⦄) = (MapTy F T)⦃MapSub F θ⦄ :=
    congrFun (congrArg mapIx (F.transSubst.naturality (Opposite.op θ))) T

@[simp]
def MapTmCommut {C D : CwFCat} {F : TmTyMorphism C D}
  {Δ Γ : C.Ctx}
  {T : Ty Γ}
  {t : Tm T}
  {θ : Δ ⟶ Γ}
  : (MapTm F (t⦃θ⦄)) = castTm  ((MapTm F t)⦃MapSub F θ⦄) (by rw [MapTyCommut]) := by
    -- let tyEq := MapTyCommut F (T := T) (θ := θ)
    -- let ceq
    --   := castSub (t := MapTm F t) (eq := by aesop) (f := MapSub F θ)
    let nat := F.transSubst.naturality (Opposite.op θ)
    let mapnat :=  (HEq.symm (hCong (refl mapFam) nat))
    let mapnat_T := hCongFunImplicit T (by simp) mapnat
    let mapnat_Tt := hCongFun t (by simp) mapnat_T
    let mapnat_eq := Eq.symm (eq_cast_of_heq mapnat_Tt)
    eapply Eq.trans mapnat_eq
    simp [MapTm, mapFam, castSub]
    apply Subtype.ext
    aesop_cat

@[simp]
def CastMapTmCommut {C D : CwFCat} {F : TmTyMorphism C D}
  {Γ : C.Ctx}
  {S T : Ty Γ}
  {eq  : S = T}
  {t : Tm T}
  : MapTm F (castTm (S := S) t (by rw [eq])) =ₜ MapTm F t  := by aesop


class IsoPreserveCwF {C D : CwFCat} (F : TmTyMorphism C D)  : Type _ where
  snocIso :
    {Γ : C.Ctx}
    → {T : Ty Γ}
    → MapCtx F (Γ ▹ T) ≅ (MapCtx F Γ) ▹ (MapTy F T) := by aesop_cat
  pPreserve :
    {Γ : C.Ctx}
    → {T : Ty Γ}
    → MapSub F (p (T := T))
      = snocIso.hom ≫ p
      := by aesop_cat
  vPreserve :
    {Γ : C.Ctx}
    → {T : Ty Γ}
    → (MapTm F (v (T := T)))
     =ₜ (v (T := MapTy F T))⦃snocIso.hom⦄  := by aesop_cat

open IsoPreserveCwF

-- attribute [simp] IsoPreserveCwF.snocIso
-- attribute [simp] IsoPreserveCwF.pPreserve
attribute [simp] IsoPreserveCwF.vPreserve



@[aesop unsafe apply]
def pPreserve' {C D : CwFCat} {F : TmTyMorphism C D} [IsoPreserveCwF F]
    {Γ : C.Ctx}
    {T : Ty Γ}
    : p (T := MapTy F T) =  snocIso.inv ≫ MapSub F (p (T := T))
      := by simp_all only [pPreserve, Iso.inv_hom_id_assoc]

def vPreserve'  {C D : CwFCat} {F : TmTyMorphism C D} [IsoPreserveCwF F]
    {Γ : C.Ctx}
    {T : Ty Γ}
    : (v (T := MapTy F T)) =
       castTm (MapTm F (v (T := T)))⦃snocIso.inv⦄ (by simp [pPreserve']) :=
         by simp only [vPreserve, castSub, tmSubComp, Iso.inv_hom_id, vCast, cast_cast, cast_eq]



def extPreserve' (C D : CwFCat) {F : TmTyMorphism C D} [pres : IsoPreserveCwF F]
  {Γ Δ : C.Ctx} {T : Ty Γ} {f : Δ ⟶ Γ} {t : Tm (T⦃f⦄)}
  : MapSub F ⟪f, t⟫ ≫ snocIso.hom
    = ⟪MapSub F f, ↑ₜ (MapTm F t) ⟫  := by
    fapply CwFProp.ext_unique <;> simp
    . simp [<- pPreserve]
    . let vid : v⦃⟪f,t⟫⦄ = castTm t (_ : T⦃p⦄⦃⟪f,t⟫⦄ = T⦃f⦄)
         := CwFProp.ext_v (f := f) (t := t)
      let vCongr := Eq.symm (congrArg (MapTm F) vid)
      rw [MapTmCommut, <- castSymm] at vCongr <;> try simp [vPreserve]
      simp only [vPreserve, castSub, tmSubComp, cast_cast, tySubComp, CwFProp.ext_p, CastMapTmCommut,
  castCastGen] at vCongr
      assumption

@[simp]
def extPreserve (C D : CwFCat) {F : TmTyMorphism C D} [pres : IsoPreserveCwF F]
  {Γ Δ : C.Ctx} {T : Ty Γ} {f : Δ ⟶ Γ} {t : Tm (T⦃f⦄)}
  : MapSub F ⟪f,t⟫
    =  ⟪MapSub F f, ↑ₜ (MapTm F t) ⟫ ≫ snocIso.inv  := by
    symm
    rw [CategoryTheory.Iso.comp_inv_eq]
    symm
    apply extPreserve'


class StrictPreserveCwF {C D : CwFCat} (F : TmTyMorphism C D)  : Prop where
  snocPreserve:
    {Γ : C.Ctx}
    → {T : Ty Γ}
    → MapCtx F (Γ ▹ T) = (MapCtx F Γ) ▹ (MapTy F T) := by aesop_cat
  pPreserveStrict :
    {Γ : C.Ctx}
    → {T : Ty Γ}
    → MapSub F (p (T := T))
      = eqToHom snocPreserve ≫ p := by aesop_cat
  vPreserveStrict :
    {Γ : C.Ctx}
    → {T : Ty Γ}
    → (MapTm F (v (T := T)))
     =ₜ (v (T := MapTy F T))⦃eqToHom snocPreserve⦄  := by aesop_cat

open StrictPreserveCwF

instance strictIsoPreserve  {C D : CwFCat} (F : TmTyMorphism C D) [StrictPreserveCwF F]  : IsoPreserveCwF F  where
  snocIso := eqToIso snocPreserve
  pPreserve := pPreserveStrict
  vPreserve := vPreserveStrict

theorem preserveId {C : CwFCat} : StrictPreserveCwF ⟨Functor.id C, NatTrans.id _⟩ where

section

def tmTyComp {C D E : CwFCat} (F : TmTyMorphism C D) (G : TmTyMorphism D E) : TmTyMorphism C E := by
  fconstructor
  . apply Functor.comp F.CtxF G.CtxF
  . fconstructor
    . intros Γ
      apply CategoryStruct.comp
      . apply F.transSubst.app
      . apply G.transSubst.app
    . aesop_cat
end

theorem MapCtxComp {C D E : CwFCat} (F : TmTyMorphism C D) (G : TmTyMorphism D E) {Γ : C.Ctx} : MapCtx (tmTyComp F G) Γ = MapCtx G (MapCtx F Γ)
  := by aesop


theorem MapSubTmTyComp {C D E : CwFCat} (F : TmTyMorphism C D) (G : TmTyMorphism D E) {Γ Δ : C.Ctx} {θ : Δ ⟶ Γ}
  : MapSub (tmTyComp F G) θ = MapSub G (MapSub F θ)
  := by aesop

theorem MapTm_TmTyComp {C D E : CwFCat} (F : TmTyMorphism C D) (G : TmTyMorphism D E) {Γ : C.Ctx} {T : Ty Γ} {t : Tm T}
  : MapTm (tmTyComp F G) t = MapTm G (MapTm F t)
  := by aesop

-- set_option pp.proofs true

theorem preserveComp {C D E : CwFCat} {F : TmTyMorphism C D} {G : TmTyMorphism D E} [Fpres : StrictPreserveCwF F] [Gpres : StrictPreserveCwF G]
  : StrictPreserveCwF (tmTyComp F G) where
  snocPreserve := by
    intros
    simp only [MapCtxComp]
    simp [Fpres.snocPreserve, Gpres.snocPreserve]
    rfl

  pPreserveStrict := by
    intros Γ T
    simp only [MapSubTmTyComp]
    simp [Fpres.pPreserveStrict]
    rw [<- MapSubComp]
    simp [Gpres.pPreserveStrict]
    simp [MapSub, eqToHom_map]

  vPreserveStrict := by
    intros Γ T
    rw [MapTm_TmTyComp]
    rw [Fpres.vPreserveStrict]
    let eq : MapTy F T⦃p⦄ = (MapTy F T)⦃p⦄⦃eqToHom (snocPreserve (T := T))⦄ := by
      simp [pPreserveStrict]
    rw [CastMapTmCommut (eq := eq)]
    rw [MapTmCommut]
    rw [Gpres.vPreserveStrict]
    simp
    apply tm_eq
    simp [MapSub, eqToHom_map]




instance : Category CwFCat where
  Hom C D := {F : TmTyMorphism C D // StrictPreserveCwF F}
  id C := ⟨ ⟨Functor.id C, NatTrans.id _⟩, preserveId⟩
  comp F G := ⟨ tmTyComp F.val G.val , preserveComp (Fpres := F.prop) (Gpres := G.prop)⟩
