
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
import CwF.Category.TmTyMorphism


open CategoryTheory
open CwFExt
open TmTy

universe u v u2
section


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

-- attribute [simp] PreservesCwF.snocPreserve
-- attribute [simp] PreservesCwF.pPreserve
-- attribute [simp] PreservesCwF.vPreserve


    -- . rw [vPreserve']

@[aesop unsafe apply]
def pPreserve' {C D : CwFCat} {F : TmTyMorphism C D} [PreservesCwF F]
    {Γ : C.Ctx}
    {T : Ty Γ}
    : p (T := MapTy F T) =  snocPreserve.inv ≫ MapSub F (p (T := T))
      := by simp_all only [pPreserve, Iso.inv_hom_id_assoc]

def vPreserve'  {C D : CwFCat} {F : TmTyMorphism C D} [PreservesCwF F]
    {Γ : C.Ctx}
    {T : Ty Γ}
    : (v (T := MapTy F T)) =
       castTm (MapTm F (CwFExt.v (T := T)))⦃snocPreserve.inv⦄ (by simp [pPreserve']) :=
         by simp only [vPreserve, castSub, tmSubComp, Iso.inv_hom_id, vCast, cast_cast, cast_eq]



def extPreserveCast (C D : CwFCat) {F : TmTyMorphism C D} [pres : PreservesCwF F]
  {Γ Δ : C.Ctx} {T : Ty Γ} {f : Δ ⟶ Γ} {t : Tm (T⦃f⦄)}
  : MapSub F (ext f t) ≫ snocPreserve.hom
    = (ext (MapSub F f) (cast (by aesop) (MapTm F t)))  := by
    fapply CwFProp.ext_unique <;> simp
    . simp [<- pPreserve]
    . let vid : v⦃⟪f,t⟫⦄ = castTm t (_ : T⦃p⦄⦃⟪f,t⟫⦄ = T⦃f⦄)
         := CwFProp.ext_v (f := f) (t := t)
      let vCongr := Eq.symm (congrArg (MapTm F) vid)
      rw [MapTmCommut, <- castSymm] at vCongr <;> try simp [vPreserve]
      simp [vPreserve] at vCongr
      assumption
