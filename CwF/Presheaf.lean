

import CwF.Fam
import CwF.Util
import CwF.Sigma
import CwF.CwFProperties
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.NatTrans
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Presheaf
import Mathlib.CategoryTheory.Elements
import Mathlib.Data.Opposite
import Mathlib.CategoryTheory.Types

import CwF.PresheafTmTy
import CwF.PresheafSnoc
import CwF.PresheafExt

import CwF.CwF


open CategoryTheory



universe u v u₂
variable {C : Type u} [CCat : Category.{v}  C]






-- set_option pp.explicit true

def pshCwF : CwF (Cᵒᵖ ⥤ Type u₂) where
  empty := Limits.terminal _

  emptyUnique := Limits.uniqueToTerminal

  snoc := pshSnoc

  p := pshP

  v := famForInv.inv pshV

  ext θ t := pshExt θ (famForInv.hom t)

  ext_p := pshExtP
  ext_pHelper := pshExt_pHelper
  ext_v :=@fun Γ Δ T θ t => by
    simp
    simp [famForInv]
    apply CategoryTheory.injective_of_mono (famForInv.hom)
    simp [famForInv, toFam]
    apply pshTmExt
    intros k γ
    simp at γ
    simp [pshV , tmSub, pshTmSub, pshExt, TmTy.F, pshTmTyFunctor]



    -- famForInv (@pshTy C CCat Δ) (@pshTm C CCat Δ) (@pshTySub C CCat Γ Δ T θ)) t)
    -- simp
    -- let cancel := fun x => congrFun ffi.hom_inv_id x
    -- simp only [CategoryStruct.comp, Function.comp, CategoryStruct.id, id] at cancel
    -- apply Eq.trans (cancel _)


  ext_unique := by simp
