
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

set_option pp.notation true
-- attribute [simp] Subst.wk_def


set_option maxHeartbeats 3000000


class SubstWf (Δ : PreCtx m) (Γ : PreCtx n) (θ : Subst sig m n) : Prop where
  varTyped : ∀ {x : Fin2 n}, (Δ ⊢ Γ[x]⦇θ⦈ ∋∷ (θ x) )

attribute [aesop safe] SubstWf.varTyped

instance wfId  (Γ : PreCtx n)  : SubstWf Γ Γ Subst.id where
  varTyped {x} := by
    constructor
    . constructor
    . simp

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
          -- we're producing a checking one as output, so there's an extra Conversion rule to apply
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
  | @PairIntro _ _ _ S T _ tys tyT tyt IHs IHT IHt =>
    let ⟨S', ty, eq⟩ := allSynthSub (Γ := Δ) θ DefEq.Refl (IHs)
    (try unfold Subst.subst ; simp_all [Subst.wk_def, Subst.singleSubSub] )
    let seq := DefEq.InContext (s := S⦇θ⦈) (t := S') (C := Σx∷ x0,, (Renaming.shift T⦇θ⦈)) (DefEq.Symm eq)
    apply Entails.TyConv _ seq
    constructor
      <;> constructor <;> (try simp)
      <;> (try aesop_cat)
      <;> (try unfold Subst.subst ; simp_all [Subst.wk_def, Subst.singleSubSub] )
      <;> (try trivial)
      <;> (try aesop_cat)
    
