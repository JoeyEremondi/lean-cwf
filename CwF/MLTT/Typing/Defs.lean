
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
  -- Synthesize a type for a term
  | SynthType : (t : Term n) → (T : Term n) → Judgment n
  -- Check a term against a given type
  | CheckType : (t : Term n) → (T : Term n) → Judgment n
  -- Check that a term's type has the given head, then synthesize the full type
  | CheckHead : (h : Head) → (t : Term n) → (Ts : ABT sig n Args) → Judgment n
  -- Check that a term is a Type, then synthesize its universe level
  | SynthLevel : (T : Term n) → (ℓ : ℕ) → Judgment n
  -- Check that a term is a Type at any level
  | IsType : (T : Term n) → Judgment n

open Judgment

-- Since substitition only preserves checking, not synthesis,
-- applying a substitution to a synthesis judgment produces a checking one
def JSub (θ : Subst sig m n)
  : Judgment n → Judgment m
  | Judgment.IsType T => Judgment.IsType T⦇θ⦈
  | Judgment.SynthType t T => Judgment.CheckType t⦇θ⦈ T⦇θ⦈
  | Judgment.CheckType t T => Judgment.CheckType t⦇θ⦈ T⦇θ⦈
  | Judgment.CheckHead h t Ts => Judgment.CheckHead h t⦇θ⦈ Ts⦇θ⦈
  | Judgment.SynthLevel T ℓ => Judgment.SynthLevel T⦇θ⦈ ℓ



notation t " ∷∈ " T => Judgment.SynthType t T
notation T  " ∋∷ " t => Judgment.CheckType t T
notation  t "∷[" h "]∈" Ts => Judgment.CheckHead h t Ts
notation "𝒰∋" T  => Judgment.IsType T
notation T "∈𝒰" ℓ  => Judgment.SynthLevel T ℓ

set_option hygiene false



section
  local notation Γ " ⊢ " J => Entails Γ J
  inductive Entails : {n : ℕ} → PreCtx n →  Judgment n → Prop where
    | WfTy :
      (Γ ⊢ T ∈𝒰 ℓ)
      → ---------------------------
      (Γ ⊢ 𝒰∋ T)

    | WfTyLevel :
        (Γ ⊢ T ∷∈ S)
      → (S ≡ 𝒰 ℓ)
      → ---------------------------
      (Γ ⊢ T ∈𝒰 ℓ )

    | HeadConv :
        (Γ ⊢ t ∷∈ T)
      → (T ≡ ABT.op h Ts)
      → ---------------------------
      (Γ ⊢ t ∷[ h ]∈ Ts)

    | TyConv :
        (Γ ⊢ t ∷∈ S)
      → (S ≡ T)
      → -----------------------------
        (Γ ⊢ T ∋∷ t)

    | VarSynth  :
    -----------------------------
    (Γ ⊢ ABT.var x ∷∈ Γ[x])

    | FunType {n : ℕ} {Γ : PreCtx n} {S : Term n} {T : Term (Nat.succ n)} :
        (Γ ⊢ S ∈𝒰 ℓ₁)
      → ((Γ▸S) ⊢ T ∈𝒰 ℓ₂)
      → ---------------------------
        (Γ ⊢ (Πx∷ S ,, T) ∷∈ (𝒰 (max ℓ₁ ℓ₂)))

    | FunIntro :
         (Γ ⊢ 𝒰∋ S)
      →  ((Γ▸S) ⊢ t ∋∷ T)
      → ---------------------------
        (Γ ⊢ (λx∷ S ,, t) ∷∈ Πx∷S ,, T)


    | FunElim :
        (Γ ⊢ t ∷[Head.Pi]∈ (x∷ S ,, T))
      → (Γ ⊢ S ∋∷ s)
      → ---------------------------
        (Γ ⊢ (t $ s) ∷∈ T/[s /x])

    | PairType {n : ℕ} {Γ : PreCtx n} {S : Term n} {T : Term (Nat.succ n)} :
        (Γ ⊢ S ∈𝒰 ℓ₁)
      → ((Γ▸S) ⊢ T ∈𝒰 ℓ₂)
      → ---------------------------
        (Γ ⊢ (Σx∷ S ,, T) ∷∈ (𝒰 (max ℓ₁ ℓ₂)))

    | PairIntro :
        (Γ ⊢ s ∷∈ S)
      → ((Γ▸S) ⊢ 𝒰∋ T)
      → (Γ ⊢ T/[s /x] ∋∷ t)
      →-----------------------------
      (Γ ⊢ ⟨x↦ s,,t ∷x,,T⟩ ∷∈ (Σx∷S ,, T) )

    | PairElim1 :
      (Γ ⊢ t ∷[ Head.Sigma ]∈ (x∷ S ,, T))
      →-----------------------------
      (Γ ⊢ (π₁ t) ∷∈ S )


    | PairElim2 :
      (Γ ⊢ t ∷[ Head.Sigma ]∈ (x∷ S ,, T))
      →-----------------------------
      (Γ ⊢ (π₂ t) ∷∈ T/[ π₁ t /x] )

end

open Entails

notation Γ " ⊢ " J => Entails Γ J

-- Take advantage of the fact that synthesis is directed on the syntax of terms
-- So in tactics, we can apply this to synthesize a type for any term
-- @[aesop unsafe]
lemma synthEq {Γ : PreCtx n} {t : Term n} {S T : Term n}
  (synthed : (Γ ⊢ t ∷∈ S) := by constructor)
  (eq : S = T := by aesop_cat)
  : Γ ⊢ t ∷∈ T := by aesop_cat

-- @[aesop unsafe]
lemma checkEq {Γ : PreCtx n} {t : Term n} {S T : Term n}
  (synthed : (Γ ⊢ t ∷∈ S) := by constructor)
  (eq : S = T := by aesop_cat)
  : Γ ⊢ T ∋∷ t  := by
    constructor
    . apply synthed
    . cases eq
      apply DefEq.Refl

-- @[aesop unsafe]
lemma allSynth {Γ : PreCtx n} {t : Term n} {T : Term n}
  (checked : (Γ ⊢ T ∋∷ t) := by assumption)
  : ∃ S, ((Γ ⊢ t ∷∈ S)) ∧ (S ≡ T) := by
  cases checked
  aesop

-- attribute [aesop safe] TyConv
attribute [aesop safe] WfTy
-- attribute [aesop safe] VarSynth
-- attribute [aesop safe] FunType
-- attribute [aesop safe] FunIntro
-- attribute [aesop safe] FunElim
