import CwF.Fam
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.NatTrans
import Mathlib.CategoryTheory.Equivalence
import Mathlib.Data.Opposite
import Mathlib.CategoryTheory.Limits.Shapes.Terminal


import CwF.Basics
import CwF.Properties
import CwF.TypeFormers.Pi
import CwF.TypeFormers.Sigma
import CwF.Democracy


open CategoryTheory

-- Pi type structure in a category with families


namespace CwF
open Fam
open CwFProp
open CwFExt


universe u v' u2
variable {Ctx : Type u} [cat : Category.{v'}  Ctx] [cwf: CwF Ctx]


inductive Tele : Ctx → Type u where
  | teleNil : {Γ : Ctx} → Tele Γ
  | teleCons : {Γ : Ctx} → (T : Ty  Γ) → Tele (Γ ▹ T) → Tele Γ

open Tele

inductive Env : {Γ : Ctx} → Tele Γ → Type u where
  | envNil : Env teleNil
  | envCons : {Γ : Ctx} → {T : Ty Γ} → {TT : Tele (Γ▹T)} →
    (t : Tm T) → Env TT → Env (teleCons T TT)

set_option pp.universes true
-- #check cwf.tmTy.tmTyFam

namespace Tele
  def map {Γ Δ : Ctx} (θ : Δ ⟶ Γ ) : Tele Γ → Tele Δ
  | teleNil => teleNil
  | teleCons T TT => teleCons T⦃θ⦄ (map (wk θ) TT)

  theorem map_id {Γ : Ctx} {TT : Tele Γ} : Tele.map (𝟙 Γ) TT = TT := by
    induction TT with
    | teleNil => aesop_cat
    | teleCons T TT IH =>
      simp [Tele.map]
      apply heq_of_heq_of_eq _ IH


end Tele

namespace Env
  def map {Γ Δ : Ctx} {TT : Tele Γ} (θ : Δ ⟶ Γ ) : Env TT → Env (TT.map θ)
  | envNil => envNil
  | envCons t tt => envCons t⦃θ⦄ (map (wk θ) tt)
end Env

-- def teleTmTy : TmTy Ctx where
--   tmTyFam := {
--     obj := fun Γ => mkFam (Tele (Opposite.unop Γ)) (Env)
-- }

def teleFam : CategoryTheory.Functor.{v',u,u,u+1} (Ctxᵒᵖ) Fam.{u} where
  obj Γ := mkFam (Tele (Opposite.unop Γ)) Env
  map {X} {Y} θ := by
    cases X
    cases Y
    fapply unmapFam <;> simp
    . apply Tele.map θ.unop
    . intros TT tt
      simp
      apply fromFam
      apply Env.map θ.unop (toFam tt)
  map_id := by
    intros Γop
    cases Γop
    simp
    symm
    apply Eq.trans
    . apply (unmapMap _).symm
    . apply unmapExt <;> simp
      . funext TT
        simp at TT
        simp
        induction TT <;> try aesop_cat
        simp [Tele.map]
        apply heq_of_eq_of_heq <;> try assumption
        rfl



--   map θ := by
--     apply unmapFam
