

import Mathlib.CategoryTheory.Comma.Arrow
import Mathlib.CategoryTheory.Types
import Mathlib.CategoryTheory.Comma.Over
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.Data.Opposite
import Mathlib.CategoryTheory.Equivalence


import CwF.TypeFam
import CwF.Fam

open CategoryTheory
open Opposite


universe  u


-- set_option maxHeartbeats 400000


def famToFam : TypeFam ⥤ Fam where
    obj AB :=  mkFam AB.fst AB.snd
    map f :=  {
      left := fun ab =>
         ⟨f.fst ab.fst , f.snd ab.snd⟩
      right := f.fst
      }

def arrTypeFamToTypeFam : Fam ⥤ TypeFam where
    obj AB :=  ⟨ixSet AB, famFor AB⟩

    map θ := ⟨mapIx θ , mapFam θ⟩


instance famToArrEssSurj : CategoryTheory.EssSurj famToFam where
  mem_essImage Y := by
    fconstructor
    . exact arrTypeFamToTypeFam.obj Y
    . simp [arrTypeFamToTypeFam, famToFam]
      constructor
      aesop_cat


instance famToArrFull : CategoryTheory.Full famToFam where
  preimage := @fun X Y θ =>
  by
    simp [famToFam, mkFam] at θ
    fconstructor
    . exact θ.right
    . intros a b
      let ab := θ.left ⟨a,b⟩
      let abEq := congrFun θ.w ⟨a,b⟩
      simp at ab abEq
      simp [<- abEq]
      exact ab.snd
  witness := by
    intros X Y f
    simp [famToFam, mkFam] at f
    simp [famToFam, mkFam]
    fapply CommaMorphism.ext <;> try simp
    . funext ab
      fapply Sigma.ext <;> try simp
      . let fw := congrFun f.w ab
        simp at fw
        simp [fw]


instance famToArrFaithful : CategoryTheory.Faithful famToFam where
  map_injective := @fun
  | X, Y, ⟨fa1,fb1⟩, ⟨fa2,fb2⟩, feq => by
    simp [famToFam] at feq
    rw [CommaMorphism.ext_iff] at feq
    let eqL := And.left feq
    let eqR := And.right feq
    simp at eqL eqR
    cases eqR
    fapply Sigma.ext <;> simp
    . funext a b
      let fab := congrFun eqL ⟨a,b⟩
      simp at fab
      assumption

-- I think this is evil e.g. classical?
noncomputable instance famToFamEquiv : IsEquivalence famToFam := Equivalence.ofFullyFaithfullyEssSurj _


-- TypeFam is equivalent to the Arrow Category of Type
theorem famEquivFam : CategoryTheory.Equivalence TypeFam.{u} Fam.{u} := Functor.asEquivalence.{u} famToFam
