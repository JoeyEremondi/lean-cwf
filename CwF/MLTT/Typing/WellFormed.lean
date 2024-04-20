import CwF.ABT.Defs
import CwF.ABT.Subst
import CwF.ABT.Renaming
import CwF.ABT.SubstProperties
import CwF.MLTT.Sig
import CwF.MLTT.Reductions
import CwF.MLTT.Typing.Defs
import CwF.MLTT.Typing.Subst


namespace MLTT
open ABT

class WfCtx (Γ : PreCtx n) : Prop where
  lookupTyped : ∀ {x : Fin2 n}, Γ ⊢ 𝒰∋ Γ[x]


attribute [aesop safe] WfCtx.lookupTyped

instance : WfCtx ⬝ where
  lookupTyped {x} := by cases x


instance wfCons {Γ : PreCtx n} [wf : WfCtx Γ] {T : Term n} (ty : Γ ⊢ 𝒰∋ T := by aesop) : WfCtx (Γ ▸ T)  where
  lookupTyped {x} := by
    cases x with simp [Renaming.shift, getElem, PreCtx.lookup] <;> try aesop_cat
    | fz =>
      let D := shiftPreserveType ty ty
      simp [JRen] at D
      assumption
    | fs x =>
      let D := shiftPreserveType (wf.lookupTyped (x := x)) ty
      simp [JRen] at D
      assumption






-- The category of contexts
structure Ctx : Type where
  {len : ℕ}
  pre : PreCtx len
  [ wf : WfCtx pre ]

structure CtxMorphism (Δ Γ : Ctx) : Type where
  sub : Subst sig Δ.len Γ.len
  [ wf : SubstWf Δ.pre Γ.pre sub]

def ctxId : CtxMorphism Γ Γ where
  sub := Subst.id

instance Termoid {n : ℕ} : Setoid  (Term n) where
  r := DefEq
  iseqv := by
    fconstructor <;> intros <;> try aesop_cat
    . apply DefEq.Refl
    . apply DefEq.Symm
      assumption
    . apply DefEq.Trans <;> assumption

-- Values are equivalence classes of the transitive-symmetric closure of reduction
def Value (n : ℕ) : Type := Quotient (Termoid (n := n))

namespace Value
  def subst (θ : Subst sig m n) : Value n → Value m :=
    Quotient.lift (fun (t : Term n) => Quotient.mk Termoid (Subst.subst θ t) )
    (by
       intros a b rel
       simp
       apply Quotient.sound
       apply DefEq.substPreserve rel
    )

end Value
