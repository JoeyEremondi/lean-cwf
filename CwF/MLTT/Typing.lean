
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

-- lemma rename_lookup {m n : ℕ} {Δ : PreCtx m} {Γ : PreCtx n}

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


abbrev JRen (ρ : Renaming m n)
  : Judgment n → Judgment m
  -- | Judgment.wfctx => Judgment.wfctx (n := m)
  | Judgment.IsType T => Judgment.IsType T⦇ρ⦈ᵣ
  | Judgment.SynthType t T => Judgment.SynthType t⦇ρ⦈ᵣ T⦇ρ⦈ᵣ
  | Judgment.CheckType t T => Judgment.CheckType t⦇ρ⦈ᵣ T⦇ρ⦈ᵣ

notation "𝒰∋" T  => Judgment.IsType T
notation t " ∷∈ " T => Judgment.SynthType t T
notation T  " ∋∷ " t => Judgment.CheckType t T

set_option hygiene false
notation Γ " ⊢ " J => Entails Γ J



inductive Entails : {n : ℕ} → PreCtx n →  Judgment n → Prop where
  | WfTy :
    (Γ ⊢ T ∷∈ 𝒰 ℓ)
    → ---------------------------
    (Γ ⊢ 𝒰∋ T)

  | TyConv :
      (Γ ⊢ t ∷∈ S)
    → (S ≡ T)
    → -----------------------------
      (Γ ⊢ T ∋∷ t)

  | VarSynth  :
  -----------------------------
  (Γ ⊢ ABT.var x ∷∈ Γ[x])

  | FunType {n : ℕ} {Γ : PreCtx n} {S : Term n} {T : Term (Nat.succ n)} :
      (Γ ⊢ (𝒰 ℓ₁) ∋∷ S)
    → ((Γ▸S) ⊢ (𝒰 ℓ₂) ∋∷ T)
    → ---------------------------
      (Γ ⊢ (Πx∷ S ,, T) ∷∈ (𝒰 (max ℓ₁ ℓ₂)))

  | FunIntro :
      ((Γ▸S) ⊢ t ∋∷ T)
    → ---------------------------
      (Γ ⊢ (λx∷ S ,, t) ∷∈ Πx∷S ,, T)


  | FunElim :
      (Γ ⊢ t ∷∈ Πx∷S ,, T)
    → (Γ ⊢ S ∋∷ s)
    → ---------------------------
      (Γ ⊢ (t $ s) ∷∈ T[s /x])


open Entails

-- attribute [simp] tyConv
-- attribute [simp] wfTy
-- attribute [simp] varSynth
-- attribute [simp] FunType
-- attribute [simp] FunIntro
-- attribute [simp] FunElim

abbrev WfCtx : (Γ : PreCtx n) → Prop
| PreCtx.ctxNil => True
| (PreCtx.ctxCons Γ T) => (Γ ⊢ 𝒰∋ T) ∧ WfCtx Γ


--Stronger than we need, but can't define the "naive" way
--until we have preservation under typing
--TODO is this a logical relation?
-- inductive SubstWf : {m n : ℕ} → (Δ : PreCtx m) → (Γ : PreCtx n) → (θ : Subst sig m n) → Prop where
--   | IdWf : SubstWf Γ Γ Subst.id
--   | CompWf : SubstWf Ξ Δ θ1 → SubstWf Δ Γ θ2 → SubstWf Ξ Γ (θ1 ⨟ θ2)
--   | ExtWf : SubstWf Δ Γ θ → (Γ ⊢ T ∋∷ t) → SubstWf Δ (Γ ▸ T) ⟪θ ● t⟫
--   | ProjWf : SubstWf (Γ ▸ T) Γ proj

-- theorem SubstWfSound {m n : ℕ} (Δ : PreCtx m) (Γ : PreCtx n) (θ : Subst sig m n) (wf : SubstWf Δ Γ θ) (x : Fin2 n)
--   : (Δ ⊢ Γ[x]⦇θ⦈ ∋∷ (θ x) ) := by
--     induction wf with try simp
--     | IdWf =>
--       simp [Subst.id]
--       constructor <;> constructor
--     | CompWf wf1 wf2 IH1 IH2 =>
--       simp
--     | _ => simp

abbrev SubstWf (Δ : PreCtx m) (Γ : PreCtx n) (θ : Subst sig m n) :=
  ∀ (x : Fin2 n), (Δ ⊢ Γ[x]⦇θ⦈ ∋∷ (θ x) )


section
  attribute [local simp] DefEq.substPreserve
  attribute [-simp] Subst.wkRenaming
  attribute [-simp] Subst.substOfRenaming


  class RenameWf {m n : ℕ} (Δ : PreCtx m) (Γ : PreCtx n) (ρ : Renaming m n) where
    changeCtx  (x : Fin2 n) : Δ[ρ x] = (Γ[x])⦇ρ⦈ᵣ

  attribute [aesop safe] RenameWf.changeCtx

  instance weakenWf (Γ : PreCtx n) (T : Term n) : RenameWf (Γ ▸ T) Γ (Fin2.fs) where
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

  theorem renamePreseveType  {n : ℕ} {Γ : PreCtx n}   (J : Judgment n)  (D : Γ ⊢ J)  :
    {m : ℕ} → {Δ : PreCtx m}  → {ρ : Renaming m n } → [wf : (RenameWf Δ Γ ρ) ] → (Δ ⊢ JRen ρ J) := by
      induction D with
        intros m Δ ρ wf
        <;> let lem := wf.changeCtx
        <;> simp_all [JRen]
        -- <;> unfold Renaming.rename
        <;> (try simp)
        <;> try (constructor <;> simp <;> aesop_cat)
      | FunElim tty sty IHt IHs =>
        let lem := FunElim IHt (@IHs _ Δ ρ _)
        simp [Subst.wkRenaming, Subst.wk_def, Subst.substOfRenaming] at lem
        simp [Subst.wkRenaming, Subst.wk_def, Subst.substOfRenaming]
        apply lem
      | VarSynth =>
        unfold Renaming.rename
        simp [<- lem]
        constructor
      | TyConv D eq IH =>
               constructor <;> try apply IH
               . simp [Subst.wkRenaming, Subst.wk_def, Subst.substOfRenaming]
                 apply DefEq.substPreserve
                 assumption
      | WfTy D IH =>
        constructor <;> apply IH


end
     -- simp_all [RenameWf, getElem, PreCtx.lookup, Renaming.wk, Renaming.shift] <;> try rfl
     -- apply RenameWf.changeCtx

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


    -- | WfTy D IH =>
    --   constructor
    --   apply IH
    --   aesop

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
