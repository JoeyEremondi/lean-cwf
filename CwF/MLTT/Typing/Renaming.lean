import CwF.ABT.Defs
import CwF.ABT.Subst
import CwF.ABT.Renaming
import CwF.ABT.SubstProperties
import CwF.MLTT.Sig
import CwF.MLTT.Reductions
import CwF.MLTT.Typing.Defs


namespace MLTT
open ABT

variable [Coverage]

section
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

  -- set_option maxHeartbeats 20000
  set_option pp.notation true

  @[aesop safe]
  theorem renamePreserveType  {n : ℕ} {Γ : PreCtx n}  {md : Mode} {i : Inputs n md} {o : Outputs n md}
    (D : Derivation Γ md i o)  :
    {m : ℕ} → {Δ : PreCtx m}  → {ρ : Renaming m n }
    → [wf : (RenameWf Δ Γ ρ) ]
    → (Derivation Δ md i⦇ρ⦈ᵣ o⦇ρ⦈ᵣ ) := by
      induction D with
      intros m Δ ρ wf
      <;> unfold_rename
      <;> unfold_rename_all
      <;> (first
              |  ( constructor
                   <;> (try unfold_rename)
                   <;> (try aesop_cat)
                   <;> (try simp [Subst.wkRenaming, Subst.wk_def, Subst.substOfRenaming])
                   <;> done )
              -- Tactic for solving all the conversion goals
              |  (constructor <;> (try aesop_cat)
                  simp [Subst.wkRenaming, Subst.wk_def, Subst.substOfRenaming]
                  let renEq := DefEq.substPreserve (by assumption) (Subst.ofRenaming ρ)
                  simp at renEq
                  assumption
                  done)
              -- -- Cases where we can just apply the IH to the subgoals
              | (constructor
                  <;> (try simp)
                  <;> (try aesop_cat)
                  <;> (try unfold_rename; simp_all [Subst.singleSubRename])
                  <;> (try trivial)
                  <;> (try aesop_cat)
                  <;> done)
              -- -- Cases where we need to prove a substitition equality before we can apply IH, the synthEq lemma helps us here
              | apply synthEq
                  <;> (try constructor <;> aesop_cat)
                  <;> (try unfold_rename ; simp_all [Subst.singleSubRename] ; (first | trivial | aesop_cat) )
                  <;> done
              | skip)
      | @VarSynth _ _ x =>
        let eq := wf.changeCtx x
        simp [<- eq]
        constructor
      | EnvCheckCons =>
        unfold_rename
        simp [Subst.renTeleCons]
        skip
        apply Derivation.EnvCheckCons
        constructor <;> try assumption
        simp
      -- | _ => admit

      -- <;>
      --   ( intros m Δ ρ wf
      --     -- unfold_rename


  -- @[aesop safe]
  -- theorem shiftPreserveType
  --   {n : ℕ} {Γ : PreCtx n} {md : Mode} {i : Inputs n md} {o : Outputs n md}
  --   (D : Γ ⊢ i ↪[md] o)
  --   {T : Term n} (Tty : Γ ⊢ 𝒰∋ T)
  --   : ((Γ▸T) ⊢ (Renaming.shift i) ↪[ md ] (Renaming.shift o)) := by
  --     simp [Renaming.shift]
  --     apply renamePreserveType D
