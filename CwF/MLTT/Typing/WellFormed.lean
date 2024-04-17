import CwF.ABT.Defs
import CwF.ABT.Subst
import CwF.ABT.Renaming
import CwF.ABT.SubstProperties
import CwF.MLTT.Sig
import CwF.MLTT.Reductions
import CwF.MLTT.Typing.Defs
import CwF.MLTT.Typing.Renaming


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




class SubstWf (Δ : PreCtx m) (Γ : PreCtx n) (θ : Subst sig m n) : Prop where
  varTyped : ∀ {x : Fin2 n}, (Δ ⊢ Γ[x]⦇θ⦈ ∋∷ (θ x) )

attribute [aesop safe] SubstWf.varTyped

instance wfExt (Δ : PreCtx m) (Γ : PreCtx n) (θ : Subst sig m n)
  [wf : SubstWf Δ Γ θ]
  {t : Term m}
  {T : Term n}
  (D : Δ ⊢ T⦇θ⦈ ∋∷ t)
  : SubstWf Δ (Γ▸T) (Subst.ext θ t) where
  varTyped {x} := by
    cases x <;> simp [getElem, PreCtx.lookup, Renaming.shift, Subst.sub_tail] <;> try aesop_cat
    simp [Subst.ext]
    apply wf.varTyped

instance wfWk (Δ : PreCtx m) (Γ : PreCtx n) (θ : Subst sig m n)
  [wf : SubstWf Δ Γ θ]
  {T : Term n}
  : SubstWf (Δ▸T⦇θ⦈) (Γ▸T) (Subst.wk θ) where
  varTyped {x} := by
    cases x with simp [Subst.wk, getElem, PreCtx.lookup, Renaming.shift, Subst.sub_tail]
    | fz =>
      constructor
      . constructor
      . simp [getElem, PreCtx.lookup, Renaming.shift, Subst.wk_def]
    | fs x =>
      simp [Subst.wk_def]
      simp [Subst.proj]
      -- rw [<- Subst.sub_comp]
      -- simp only [<- Subst.substOfRenaming]
      let ty := wf.varTyped (x := x)
      let helper := renamePreserveType ty (ρ := Fin2.fs) (wf := weakenWf (T := T⦇θ⦈))
      simp [JRen] at helper
      assumption
