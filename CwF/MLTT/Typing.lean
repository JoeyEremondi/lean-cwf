
import CwF.ABT.Defs
import CwF.ABT.Subst
import CwF.ABT.Renaming
import CwF.ABT.SubstProperties
import CwF.MLTT.Sig
import CwF.MLTT.Reductions


namespace MLTT
open ABT

--A context over n variables is a list of n variables, where each can depend on the last
inductive PreCtx : ℕ → Type where
  | ctxNil : PreCtx 0
  | ctxCons : PreCtx n → Term n → PreCtx (Nat.succ n)

notation "⬝" => PreCtx.ctxNil

notation:max Γ "▸" T => PreCtx.ctxCons Γ T

namespace PreCtx
def lookup :  (Γ : PreCtx n) → Fin2 n → Term n
|  (ctxCons _ T), Fin2.fz => Renaming.shift T
|  (ctxCons Γ _), (Fin2.fs x) => Renaming.shift (lookup Γ x)
end PreCtx

instance {n : ℕ} : GetElem (PreCtx n) (Fin2 n) (Term n) (fun _ _ => True) where
  getElem Γ x _ := PreCtx.lookup Γ x

-- We use a BCIC-style bidirectional system (https://arxiv.org/pdf/2102.06513.pdf)
-- so all terms synthesize, but the synthesis-checking switch determines where
-- conversion checks happen
inductive Judgment : (n : ℕ) → Type where
  -- | wfctx : {n : ℕ} →  Judgment n
  | IsType : (T : Term n) → Judgment n
  | SynthType : (t : Term n) → (T : Term n) → Judgment n
  | CheckType : (t : Term n) → (T : Term n) → Judgment n

open Judgment

abbrev JSub (θ : Subst sig m n)
  : Judgment n → Judgment m
  -- | Judgment.wfctx => Judgment.wfctx (n := m)
  | Judgment.IsType T => Judgment.IsType T⦇θ⦈
  | Judgment.SynthType t T => Judgment.SynthType t⦇θ⦈ T⦇θ⦈
  | Judgment.CheckType t T => Judgment.CheckType t⦇θ⦈ T⦇θ⦈

notation "𝒰∋" T  => Judgment.IsType T
notation t " ∷∈ " T => Judgment.SynthType t T
notation T  " ∋∷ " t => Judgment.CheckType t T

set_option hygiene false
notation Γ " ⊢ " J => Entails Γ J



inductive Entails : PreCtx n →  Judgment n → Prop where
  | wfTy :
    (Γ ⊢ T ∷∈ 𝒰 ℓ)
    → ---------------------------
    (Γ ⊢ 𝒰∋ T)

  | tyConv :
      (Γ ⊢ t ∷∈ S)
    → (S ≡ T)
    → -----------------------------
      (Γ ⊢ T ∋∷ t)

  | varSynth  :
  -----------------------------
  (Γ ⊢ ABT.var x ∷∈ Γ[x])

  | FunType :
      (Γ ⊢ (𝒰 ℓ₁) ∋∷ S)
    → ((Γ▸S) ⊢ (𝒰 ℓ₂) ∋∷ T)
    → ---------------------------
      (Γ ⊢ (Πx∷ S ,, T) ∷∈ (𝒰 (max ℓ₁ ℓ₂)))

  | FunIntro :
      ((Γ▸S) ⊢ t ∋∷ T)
    → ---------------------------
      (Γ ⊢ (λx∷ S ,, t) ∷∈ Πx∷S ,, T)


  | FunApp :
      (Γ ⊢ t ∷∈ Πx∷S ,, T)
    → (Γ ⊢ S ∋∷ s)
    → ---------------------------
      (Γ ⊢ (t $ s) ∷∈ T[s /x])

open Entails

abbrev WfCtx : (Γ : PreCtx n) → Prop
| PreCtx.ctxNil => True
| (PreCtx.ctxCons Γ T) => (Γ ⊢ 𝒰∋ T) ∧ WfCtx Γ


--Stronger than we need, but can't define the "naive" way
--until we have preservation under typing
--TODO is this a logical relation?
inductive SubstWf : {m n : ℕ} → (Δ : PreCtx m) → (Γ : PreCtx n) → (θ : Subst sig m n) → Prop where
  | IdWf : SubstWf Γ Γ Subst.id
  | CompWf : SubstWf Ξ Δ θ1 → SubstWf Δ Γ θ2 → SubstWf Ξ Γ (θ1 ⨟ θ2)

-- abbrev SubstWf (Δ : PreCtx m) (Γ : PreCtx n) (θ : Subst sig m n) :=
--   ∀ (x : Fin2 n), (Δ ⊢ Γ[x]⦇θ⦈ ∋∷ (θ x) )

--Lemmas simplifying what it means for a substitution to be well formed
-- @[simp]
-- lemma idWf {Γ : PreCtx n} : SubstWf Γ Γ Subst.id = True := by
--   simp [SubstWf, Subst.id]
--   intros x
--   constructor
--   . apply varSynth
--   . apply DefEq.Refl

-- @[simp]
-- lemma compWf {Γ : PreCtx c} {Δ : PreCtx b} {Ξ : PreCtx a}
--   {θ1 : Subst sig a b} {θ2 : Subst sig b c}
--   (wf1 : SubstWf Ξ Δ θ1) (wf2 : SubstWf Δ Γ θ2)
--   : SubstWf Ξ Γ (θ1 ⨟ θ2) := by
--   intros x
--   simp [Subst.comp]
--   rw [<- Subst.sub_comp]
--   let lem2 := wf2 x


-- theorem subPreseveType  {Γ : PreCtx n} (Γwf : WfCtx Γ )  (𝒥 : Judgment n)  (𝒟 : Γ ⊢ 𝒥)  :
--   ∀ {m : ℕ} {Δ : PreCtx m} (Δwf : WfCtx Δ) (θ : Subst sig m n ) (θwf : SubstWf Δ Γ θ),
--   (Δ ⊢ JSub θ 𝒥 ) := by
--   induction 𝒟 with intros m Δ Δwf θ <;> simp_all [JSub] <;> try (constructor <;>  aesop_cat)
--   | tyConv 𝒟 eq IH => admit
--   | FunType Sty Tty IHs IHt =>
--     constructor <;> simp
--     . apply IHs
--       assumption
--     . apply IHt
--   | _ => admit



-- def Ctx (n : ℕ) : Type :=
--   {Γ : PreCtx n // WfCtx Γ}
