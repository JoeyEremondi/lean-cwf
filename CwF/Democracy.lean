
import CwF.Fam
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.NatTrans
import Mathlib.Data.Opposite
import Mathlib.CategoryTheory.Limits.Shapes.Terminal


import CwF.Basics
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

    def demSnoc {Γ : C} {T : Ty Γ}
      : Tm (asTy (Γ ▹ T)) ≅ Tm T := by
      trans
      . apply termSecEquiv

end


end CwF