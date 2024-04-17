import CwF.ABT.Defs
import CwF.ABT.Subst
import CwF.ABT.Renaming
import CwF.ABT.SubstProperties
import CwF.MLTT.Sig
import CwF.MLTT.Reductions
import CwF.MLTT.Typing.Defs


namespace MLTT
open ABT


abbrev JRen (ρ : Renaming m n)
  : Judgment n → Judgment m
  -- | Judgment.wfctx => Judgment.wfctx (n := m)
  | Judgment.IsType T => Judgment.IsType T⦇ρ⦈ᵣ
  | Judgment.SynthType t T => Judgment.SynthType t⦇ρ⦈ᵣ T⦇ρ⦈ᵣ
  | Judgment.CheckType t T => Judgment.CheckType t⦇ρ⦈ᵣ T⦇ρ⦈ᵣ
  | Judgment.CheckHead h t Ts => Judgment.CheckHead h t⦇ρ⦈ᵣ Ts⦇ρ⦈ᵣ
  | Judgment.SynthLevel T ℓ => Judgment.SynthLevel T⦇ρ⦈ᵣ ℓ



section
  attribute [local simp] DefEq.substPreserve
  attribute [-simp] Subst.wkRenaming
  attribute [-simp] Subst.substOfRenaming


  class RenameWf {m n : ℕ} (Δ : PreCtx m) (Γ : PreCtx n) (ρ : Renaming m n) where
    changeCtx  (x : Fin2 n) : Δ[ρ x] = (Γ[x])⦇ρ⦈ᵣ

  attribute [aesop safe] RenameWf.changeCtx

  instance weakenWf {Γ : PreCtx n} {T : Term n} : RenameWf (Γ ▸ T) Γ (Fin2.fs) where
    changeCtx x := by
      cases x <;> simp [getElem, PreCtx.lookup, Renaming.shift]

  instance wkWf
    {Δ : PreCtx m} {Γ : PreCtx n} {T : Term n} {ρ : Renaming m n}
    [wf : RenameWf Δ Γ ρ ]
    : RenameWf (Δ ▸ (T⦇ρ⦈ᵣ)) (Γ ▸ T) (Renaming.wk ρ)  where
    changeCtx x := by
      cases x <;> simp [Renaming.wk, getElem, PreCtx.lookup]
      apply congrArg Renaming.shift
      apply wf.changeCtx

  instance wkShift : RenameWf (Γ▸T) Γ Fin2.fs where
    changeCtx x := by
      cases x <;> simp [PreCtx.lookup, getElem, Renaming.shift]

  set_option maxHeartbeats 1000000

  @[aesop safe]
  theorem renamePreserveType  {n : ℕ} {Γ : PreCtx n}   {J : Judgment n}  (D : Γ ⊢ J)  :
    {m : ℕ} → {Δ : PreCtx m}  → {ρ : Renaming m n } → [wf : (RenameWf Δ Γ ρ) ] → (Δ ⊢ JRen ρ J) := by
      induction D <;>
        ( intros m Δ ρ wf
          simp_all [JRen]
          (first
              |  ( constructor
                   <;> (try simp)
                   <;> aesop_cat
                   <;> done )
              -- Tactic for solving all the conversion goals
              |  (constructor <;> (try aesop_cat)
                  simp [Subst.wkRenaming, Subst.wk_def, Subst.substOfRenaming]
                  let renEq := DefEq.substPreserve (by assumption) (Subst.ofRenaming ρ)
                  simp at renEq
                  assumption
                  done)
              -- Cases where we can just apply the IH to the subgoals
              | (constructor
                  <;> (try simp)
                  <;> (try aesop_cat)
                  <;> (try unfold Renaming.rename ; simp_all [Subst.singleSubRename])
                  <;> (try trivial)
                  <;> (try aesop_cat)
                  <;> done)
              -- Cases where we need to prove a substitition equality before we can apply IH, the synthEq lemma helps us here
              | apply synthEq
                  <;> (try constructor <;> aesop_cat)
                  <;> (try unfold Renaming.rename ; simp_all [Subst.singleSubRename] ; (first | trivial | aesop_cat) )
                  <;> done
              | skip))

  @[aesop safe]
  theorem shiftPreserveType  {n : ℕ} {Γ : PreCtx n}  {J : Judgment n}  (D : Γ ⊢ J)
    {T : Term n} (Tty: Γ ⊢ 𝒰∋ T)
    : ((Γ▸T) ⊢ JRen (Fin2.fs) J) := by
      simp [Renaming.shift, JRen]
      apply renamePreserveType D
