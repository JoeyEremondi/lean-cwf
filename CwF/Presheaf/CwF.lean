

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
import CwF.Presheaf.Snoc
import CwF.Presheaf.Ext

import CwF.Basics


open CategoryTheory



universe u v u₂
variable {C : Type u} [CCat : Category.{v}  C]







def pshCwF : CwF (Cᵒᵖ ⥤ Type u₂) where
  -- Lean's terminal stuff is all non-computable, so we
  -- construct it manually
  empty  := {
    obj := fun _ => PUnit
    map := fun _ y => y
  }

  emptyUnique := fun Γ => by
    fconstructor
    . fconstructor
      fconstructor <;> aesop_cat
    . intros
      apply NatTrans.ext
      funext
      simp


  snoc := pshSnoc

  p := pshP

  v := fromFam pshV

  ext θ t := pshExt θ (toFam t)

  ext_p := pshExtP
  ext_pHelper := pshExt_pHelper
  ext_v :=@fun Γ Δ T θ t => by
    simp
    apply Function.LeftInverse.injective toFamLeftInv
    apply pshTmExt
    intros k γ
    simp at γ
    aesop_cat

  ext_unique f t g peq tyEq veq := by
    aesop_cat
