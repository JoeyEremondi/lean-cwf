
import CwF.ABT.ABT
import CwF.ABT.Subst
import CwF.ABT.Renaming
import CwF.ABT.SubstProperties
import CwF.MLTT.Sig
import CwF.MLTT.Reductions
import CwF.MLTT.Typing.Derivations
import CwF.MLTT.Typing.Renaming
import CwF.MLTT.Typing.SubstHelper


namespace MLTT
open ABT

variable  [Ind] [Arities] [IndTypes] [Coverage]



set_option maxHeartbeats 1000000


-- set_option trace.Meta.synthInstance true

theorem subPreserveType  {Γ : PreCtx n} {md : Mode} {i : Inputs n md} {o : Outputs n md}
  (D : Derivation Γ md i o)  :
  ∀ {m : ℕ} {Δ : PreCtx m}  {θ : Subst m n } [θwf : SubstWf Δ Γ θ],
  (Derivation Δ (subMode md) (subIn md i o)⦇θ⦈ (subOut md i o)⦇θ⦈ ) := by
  induction D with
    ( intros m Δ θ θwf
      <;> dsimp only [subMode, subIn, subOut]
      <;> (try dsimp only [subMode, subIn, subOut] at *)
      <;> unfold_subst
      <;> (try unfold_subst_all)
      <;> (try (first
          |  ( constructor <;> (try aesop_cat) <;> (try simp [Subst.wk_def, Subst.singleSubSub]) <;> (try aesop_cat) <;> done )
          -- Tactic for solving all the conversion goals
          |(rename_i IH
            let subEq := DefEq.substPreserve (by assumption) θ
            unfold_subst_at subEq
            let ⟨S, ty, eq⟩ := allSynthSub (Γ := Δ) θ subEq (IH)
            constructor <;> try assumption
            done)
          -- Cases where we can just apply the IH to the subgoals
          -- We need to apply constructor twice because even if we had a synthesis judgment as input,
          -- we're producing a checking one as output, so there's an extra Conversion rule to apply
          | (constructor
              <;> constructor
              <;> (try simp)
              <;> (try aesop_cat)
              <;> (try unfold_subst ; simp_all [Subst.wk_def, Subst.singleSubSub] )
              <;> (try trivial)
              <;> (try aesop_cat)
              <;> done
              )
          -- Cases where we need to prove a substitition equality before we can apply IH, the checkEq lemma helps us here
          | (apply checkEq
              <;> (try simp)
              <;> (try constructor <;> aesop_cat)
              <;> (try simp [Subst.wk_def, Subst.singleSubSub])
              <;> (first | trivial | exact True.intro | aesop_cat)
              <;> done)
          ) <;> done ))
  | @VarSynth _ _ x =>
    let helper := θwf.varTyped (x := x)
    unfold_subst_at helper
    assumption
  | @MatchTy n Γ numScrut numBranch ts Ts Tmotive xs lhss rhss iscover ty tyBranch IHts _ =>
    apply checkEq _ (Eq.refl _)
    rw [Subst.syntacticSubComp]

    let ret := IHts (Δ := Δ) (θ := θ)
    let eq : (θ ⨟ Subst.ofRenaming (Renaming.fromClosed (m := n))) = Subst.ofRenaming (Renaming.fromClosed (m := m)) :=
      Subst.fromClosedSubst (θ := θ ⨟ Subst.ofRenaming (Renaming.fromClosed (m := n)))
    simp [eq] at ret
    constructor <;> try assumption
    simp [Subst.substOfRenaming]
    apply ret
    -- (try unfold_subst ; simp_all [Subst.wk_def, Subst.singleSubSub] )
    -- let seq := DefEq.InContext (s := S⦇θ⦈) (t := S') (C := Σx∷ x0,, (Renaming.shift T⦇θ⦈)) (DefEq.Symm eq)
    -- apply Entails.TyConv _ seq
    -- constructor
    --   <;> constructor <;> (try simp)
    --   <;> (try aesop_cat)
    --   <;> (try unfold Subst.subst ; simp_all [Subst.wk_def, Subst.singleSubSub] )
    --   <;> (try trivial)
    --   <;> (try aesop_cat)
