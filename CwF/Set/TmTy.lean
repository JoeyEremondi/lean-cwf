
import CwF.Fam
import CwF.Util
import CwF.Sigma
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Types
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.NatTrans
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Presheaf
import Mathlib.CategoryTheory.Elements
import Mathlib.Data.Opposite
import Mathlib.CategoryTheory.Types



import CwF.Basics

/-!  The CwF functor for Presheaves. For a presheaf Γ, defines a structure of types over that presheaf
(e.g. we interpret the presheaf as a context) and the structure of terms over a given type, as well
as substitution of terms into types and terms.
-/

open CategoryTheory
open CwF
open Fam

def setToFam : CategoryTheory.Functor Typeᵒᵖ Fam where
  obj Γ := mkFam (Γ.unop → Type) (fun T => ULift ((γ : Γ.unop) → T γ))
  map := @fun {Δ} {Γ} θ =>
  let θop := θ.unop
  by
    fapply unmapFam <;> try aesop_cat
    . intros T δf'
      let δf := (toFam δf').down
      fapply fromFam
      aesop_cat
