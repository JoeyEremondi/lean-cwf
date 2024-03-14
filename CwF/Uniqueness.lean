
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Comma.Over
import Mathlib.CategoryTheory.Comma.Basic
import Mathlib.Data.Opposite
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.Logic.Unique


import CwF.Fam
import CwF.Basics
import CwF.Properties

open CategoryTheory
namespace CwF

lemma cwfUniqueHomInv {C : Type u} [cat : Category.{v}  C] [Limits.HasTerminal C] [TmTy C]
  (inst1 inst2 : CwFExt C)
  [prop1 : @CwFProp C _ _ inst1] [prop2 : @CwFProp C _ _ inst2]
  {Γ : C} {T : Ty Γ}
  : (inst2.ext (inst1.p (T := T)) inst1.v) ≫ (inst1.ext (inst2.p (T := T)) inst2.v)
      = 𝟙 (inst1.snoc Γ T) := by
    let cwf1 : CwF C := {cwfExt := inst1}
    rw [<- ext_id (cwf := cwf1) (T := T)]
    fapply prop1.ext_unique (cwf := inst1)
      <;> try simp [ext_nat (cwf := cwf1), prop1.ext_p (cwf := inst1) ]

--Given the functoral definition of substitution on terms and types for a category of contexts,
--context extension is unique up to isomorphism
lemma cwfUnique {C : Type u} [cat : Category.{v}  C] [Limits.HasTerminal C] [tmTy : TmTy C]
  (inst1 inst2 : CwFExt C)
  [prop1 : @CwFProp C _ _ inst1] [prop2 : @CwFProp C _ _ inst2]
  {Γ : C} {T : Ty Γ}
    :  (inst1.snoc Γ T)  ≅  (inst2.snoc Γ T) where
  -- Bascially a dependent version of the uniqueness of products
  hom := (inst2.ext (inst1.p (T := T)) inst1.v)
  inv :=  (inst1.ext (inst2.p (T := T)) inst2.v)
  hom_inv_id := cwfUniqueHomInv inst1 inst2
  inv_hom_id := cwfUniqueHomInv inst2 inst1
