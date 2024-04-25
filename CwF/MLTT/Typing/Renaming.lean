import CwF.ABT.ABT
import CwF.ABT.Subst
import CwF.ABT.Renaming
import CwF.ABT.SubstProperties
import CwF.MLTT.Sig
import CwF.MLTT.Reductions
import CwF.MLTT.Typing.Derivations


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
      <;> (try unfold_rename
      <;> unfold_rename_all
      <;> (first
              |  ( constructor
                   <;> (try unfold_rename)
                   <;> (try aesop_cat)
                   <;> (try simp_all [Subst.wkRenaming, Subst.wk_def, Subst.substOfRenaming])
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
              <;> done)
      | @VarSynth _ _ x =>
        let eq := wf.changeCtx x
        unfold_rename_at eq
        unfold_rename
        simp [<- eq]
        constructor
      -- We have to handle match specially because it does werid stuff with top-level expressions
      -- Should be simpler if we get Justus's rules working
      | @MatchTy _ Γ numScrut numBranch ts Ts Tmotive xs lhss rhss iscover ty tyBranch IHts _ =>
        unfold_rename
        unfold_rename_at IHts
        simp [Subst.substOfRenaming]
        rw [Subst.syntacticSubComp]
        rw [<- Subst.substOfRenaming]
        constructor <;> try aesop_cat
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
