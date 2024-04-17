
import CwF.ABT.Defs
import CwF.ABT.Subst
import CwF.ABT.Renaming
import CwF.ABT.SubstProperties
import CwF.MLTT.Sig
import CwF.MLTT.Reductions
import CwF.MLTT.Typing.Defs
import CwF.MLTT.Typing.Renaming
import CwF.MLTT.Typing.WellFormed


namespace MLTT
open ABT

set_option pp.notation true
-- attribute [simp] Subst.wk_def


set_option maxHeartbeats 3000000

-- Helpful lemma for managning conversion and the checking/synthesis switch
lemma allSynthSub {Γ : PreCtx m} {t : Term n} {S : Term m} {T : Term n} (θ : Subst sig m n)
  (eq : (T⦇θ⦈ ≡ S) )
  (checked : (Γ ⊢ T⦇θ⦈ ∋∷ t⦇θ⦈) := by assumption)
  : ∃ S', (Γ ⊢ t⦇θ⦈ ∷∈ S') ∧ (S' ≡ S) := by
  cases checked
  (repeat constructor) <;> try assumption
  apply DefEq.Trans <;> assumption

theorem subPreserveType  {Γ : PreCtx n}   (𝒥 : Judgment n)  (𝒟 : Γ ⊢ 𝒥)  :
  ∀ {m : ℕ} {Δ : PreCtx m}  {θ : Subst sig m n } [θwf : SubstWf Δ Γ θ],
  (Δ ⊢ JSub θ 𝒥 ) := by
  induction 𝒟 with
    ( intros m Δ θ θwf
      simp_all [JSub]
      (first
          |  ( constructor
                <;> (try simp)
                <;> aesop_cat
                <;> done )
          -- Tactic for solving all the conversion goals
          |(rename_i IH
            let subEq := DefEq.substPreserve (by assumption) θ
            unfold Subst.subst at subEq
            simp at subEq
            let ⟨S, ty, eq⟩ := allSynthSub (Γ := Δ) θ subEq (IH)
            constructor <;> try assumption)
          -- Cases where we can just apply the IH to the subgoals
          -- We need to apply constructor twice because even if we had a synthesis judgment as input,
          -- we're producing a checking one as output, so there's an extra Conversion to apply
          | (constructor
              <;> constructor
              <;> (try simp)
              <;> (try aesop_cat)
              <;> (try unfold Subst.subst ; simp_all [Subst.wk_def, Subst.singleSubSub] )
              <;> (try trivial)
              <;> (try aesop_cat)
              <;> done)
          -- Cases where we need to prove a substitition equality before we can apply IH, the checkEq lemma helps us here
          | apply checkEq
              <;> (try simp)
              <;> (try constructor <;> aesop_cat)
              <;> (try unfold Subst.subst ; simp_all [Subst.wk_def, Subst.singleSubSub] ; (first | trivial | aesop_cat) )
              <;> done
          | skip))
  | @VarSynth _ _ x =>
    let helper := θwf.varTyped (x := x)
    apply helper
