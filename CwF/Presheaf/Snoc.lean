import CwF.Fam
import CwF.Util
import CwF.Sigma
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.NatTrans
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Presheaf
import Mathlib.CategoryTheory.Elements
import Mathlib.Data.Opposite
import Mathlib.CategoryTheory.Types

import CwF.Presheaf.TmTy

import CwF.CwF

open CategoryTheory


universe u v u₂
variable {C : Type u} [CCat : Category.{v}  C]

abbrev pshSnocObj (Γ : Cᵒᵖ ⥤ Type u₂) (T : Ty Γ) (k : Cᵒᵖ) :  Type u₂ :=
  (γ : Γ.obj k) × (T.obj ⟨k,γ⟩)


abbrev pshSnocMap {Γ : Cᵒᵖ ⥤ Type u₂} {T : Ty Γ} {k1 k2 : Cᵒᵖ}
  (θ : k1 ⟶ k2) (γτ : pshSnocObj Γ T k1) : pshSnocObj Γ T k2 :=
      ⟨ Γ.map θ γτ.fst
      , pshTyMap T θ γτ.fst γτ.snd
      ⟩


abbrev pshSnocMapId {Γ : Cᵒᵖ ⥤ Type u₂} {T : Ty Γ} {k : Cᵒᵖ} {γτ : pshSnocObj Γ T k}
    : pshSnocMap (𝟙 k) γτ  = γτ := by
      cases γτ with
      | mk γ τ =>
        fapply Sigma.ext <;> try simp
        apply hCongFun (f := pshTyMap T (𝟙 k) γ) (g := fun x => x) τ
        . aesop_cat
        . fapply HEq.trans (pshTyMapId T)
          aesop



abbrev pshSnocMapComp {Γ : Cᵒᵖ ⥤ Type u₂} {T : Ty Γ} {k1 k2 k3 : Cᵒᵖ} {γτ : pshSnocObj Γ T k1}
  {f : k1 ⟶ k2} {g : k2 ⟶ k3}
    : pshSnocMap (f ≫ g) γτ = pshSnocMap g (pshSnocMap f γτ) := by
      cases γτ with
      | mk γ τ =>
        fapply Sigma.ext <;> try simp
        apply hCongFun τ
        . aesop_cat
        . fapply HEq.trans (pshTyMapComp T f g)
          aesop



abbrev pshSnoc (Γ : Cᵒᵖ ⥤ Type u₂) (T : Ty Γ) : Cᵒᵖ ⥤ Type u₂  where
    obj := pshSnocObj Γ T
    map := pshSnocMap
    map_id k := by
      funext γτ
      apply pshSnocMapId

    map_comp f g :=  by
      funext γτ
      apply pshSnocMapComp


def pshP {Γ : Cᵒᵖ ⥤ Type u₂} {T : Ty Γ}
  : (pshSnoc Γ T) ⟶ Γ :=
    ⟨ fun k γτ =>  γτ.fst
    , @fun k1 k2 f => by
      aesop_cat
    ⟩


def pshV {Γ : Cᵒᵖ ⥤ Type u₂} {T : pshTy Γ}
  : pshTm (Γ := pshSnoc Γ T) (pshTySub T (pshP (T := T))) := by
    simp [pshSnoc, pshTySub]
    fconstructor
    . intros k γ
      simp [tySub, pshTySub, mapIx]
      simp at γ
      exact γ.snd
    . aesop_cat
