
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


open CategoryTheory

universe u v u2
section


structure CwFCat : Type ((max u v) + 1) where
  Ctx : Type u
  cat : Category.{v} Ctx
  tmTy : TmTy.{u,v} Ctx
  cwf : CwF Ctx

instance {C : CwFCat} : Category C.Ctx := C.cat
instance {C : CwFCat} : TmTy C.Ctx := C.tmTy
instance {C : CwFCat} : CwF C.Ctx := C.cwf

structure TmTyMorphism (C D : CwFCat) : Type ((max u v)+2) where
  CtxF : CategoryTheory.Functor.{v,v,u,u} C.Ctx D.Ctx
  MapSub : NatTrans C.tmTy.F (CategoryTheory.Functor.comp (Functor.op CtxF) D.tmTy.F )

-- FTy {C D : CwFCat} (F : TmTyMorphism C D) ->


structure CwFMorphism (C D : CwFCat) : Type ((max u v)+2) where

  preserveSnoc : {Γ : C.Ctx} → {T : Ty Γ} →

-- instance cwfCat :  Category CwFCat where
--   Hom C D := C.tmTyInst.F ⟶ D.tmTy.F
--   id C := 𝟙 C.Ctx
