
import CwF.Fam
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.NatTrans
import Mathlib.Data.Opposite
import Mathlib.CategoryTheory.Limits.Shapes.Terminal


import CwF.Basics
import CwF.Util.ULift
import CwF.Properties
import CwF.TypeFormers.PiSigma


open CategoryTheory

-- Pi type structure in a category with families


namespace CwF
open Fam
open CwFProp
open CwFExt


class Democratic {C : Type u} [Category.{v}  C] (cwf: CwF C) : Type _ where
  asTy : C → Ty (tmTy := cwf.tmTy) (cwf.empty)
  demIso : Γ ≅ cwf.cwfExt.snoc cwf.empty (asTy Γ)

open Democratic

section
    variable {C : Type u} [Category.{v}  C] [cwf: CwF C] [dem : Democratic cwf]

    def demTm {Γ : C}
      : (Tm (asTy Γ)) ↑≅ ⬝ ⟶ Γ :=  by
      apply Iso.trans
      . apply closedSnocIso
      . apply Functor.mapIso uliftFunctor
        let yNatIso := Functor.mapIso (yoneda (C := C)) (X := ⬝▹(asTy Γ)) (Y := Γ) demIso.symm
        apply yNatIso.app (Opposite.op ⬝)

    --TODO move this out of democracy?


        -- simp
--      hom_in v_id := by
--         funext θ
--         simp [<- Category.assoc]
--         rw [emptySelfUnique]
--         simp only [Category.id_comp]
--       inv_hom_id := by
--         funext γθ
--         cases γθ with
--         | mk γ  θ =>
--           simp
--           constructor

--     def demSnoc {Γ : C} {T : Ty Γ}
--       : Tm (asTy (Γ ▹ T)) ≅ Tm (asTy Γ) × Tm T := by
--       apply viaUlift
--       . apply demTm
--       . apply termSecIso
--       . fconstructor
--         . intros θ
--           apply SplitEpi.mk (‼ ≫ θ) (by
--             simp
--             simp)
--       -- apply Iso.trans
--       -- . apply demTm
--       -- apply termSecPreserveIso
--       -- trans
--       -- . apply emptySecIso
--       -- . fconstructor
--       --   . intros f
--       --     fconstructor
--       --     . apply CategoryStruct.comp (‼ ≫ f)


-- end


-- end CwF
