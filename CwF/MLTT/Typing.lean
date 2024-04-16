
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



section
  local notation Γ " ⊢ " J => Entails Γ J
  inductive Entails : {n : ℕ} → PreCtx n →  Judgment n → Prop where
    | WfTy :
      (Γ ⊢ (𝒰 ℓ) ∋∷ T)
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
         (Γ ⊢ 𝒰∋ S)
      →  ((Γ▸S) ⊢ t ∋∷ T)
      → ---------------------------
        (Γ ⊢ (λx∷ S ,, t) ∷∈ Πx∷S ,, T)


    | FunElim :
        (Γ ⊢ t ∷∈ Πx∷S ,, T)
      → (Γ ⊢ S ∋∷ s)
      → ---------------------------
        (Γ ⊢ (t $ s) ∷∈ T[s /x])
end

open Entails

notation Γ " ⊢ " J => Entails Γ J

-- Take advantage of the fact that synthesis is directed on the syntax of terms
-- So in tactics, we can apply this to synthesize a type for any term
@[aesop unsafe]
lemma synthEq {Γ : PreCtx n} {t : Term n} {S T : Term n}
  (synthed : (Γ ⊢ t ∷∈ S) := by constructor)
  (eq : S = T := by aesop_cat)
  : Γ ⊢ t ∷∈ T := by aesop_cat


-- attribute [aesop safe] TyConv
attribute [aesop safe] WfTy
-- attribute [aesop safe] VarSynth
-- attribute [aesop safe] FunType
-- attribute [aesop safe] FunIntro
-- attribute [aesop safe] FunElim



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

  @[aesop safe]
  theorem renamePreserveType  {n : ℕ} {Γ : PreCtx n}   {J : Judgment n}  (D : Γ ⊢ J)  :
    {m : ℕ} → {Δ : PreCtx m}  → {ρ : Renaming m n } → [wf : (RenameWf Δ Γ ρ) ] → (Δ ⊢ JRen ρ J) := by
      induction D with
        intros m Δ ρ wf
        <;> let lem := wf.changeCtx
        <;> simp_all [JRen]
        <;> (try (constructor <;> (try simp) <;> aesop_cat))
        -- Special tactic for synthesizing a type then seeing if it's equal to the goal type
        <;> (try
              (apply synthEq <;> (try constructor <;> aesop_cat)
               simp [Subst.wkRenaming, Subst.wk_def, Subst.substOfRenaming]
               constructor))
      | VarSynth =>
        unfold Renaming.rename
        simp [<- lem]
        constructor
      | TyConv D eq IH =>
               constructor <;> try apply IH
               . simp [Subst.wkRenaming, Subst.wk_def, Subst.substOfRenaming]
                 apply DefEq.substPreserve
                 assumption

  @[aesop safe]
  theorem shiftPreserveType  {n : ℕ} {Γ : PreCtx n}  {J : Judgment n}  (D : Γ ⊢ J)
    {T : Term n} (Tty: Γ ⊢ 𝒰∋ T)
    : ((Γ▸T) ⊢ JRen (Fin2.fs) J) := by
      simp [Renaming.shift, JRen]
      apply renamePreserveType D


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


end


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

set_option pp.notation true

theorem subPreserveType  {Γ : PreCtx n}   (𝒥 : Judgment n)  (𝒟 : Γ ⊢ 𝒥)  :
  ∀ {m : ℕ} {Δ : PreCtx m}  (θ : Subst sig m n ) [θwf : SubstWf Δ Γ θ],
  (Δ ⊢ JSub θ 𝒥 ) := by
  induction 𝒟 with
    intros m Δ  θ θwf
    <;> simp_all [JSub]
    <;> (try (constructor <;>  aesop_cat))
    <;> (try (apply synthEq <;> (try constructor) <;> (try aesop_cat) <;> simp [Subst.wk_def] <;> trivial))
  | @VarSynth _ _ x =>
    let helper := θwf.varTyped (x := x)
    apply synthEq <;> admit
  --   apply synthEq <;> (try constructor) <;> (try aesop_cat) <;> simp [Subst.wk_def] <;> trivial

  -- | _ => admit



-- def Ctx (n : ℕ) : Type :=
--   {Γ : PreCtx n // WfCtx Γ}
