
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

inductive Mode :=
  | Synth | Check | CheckType | SynthLevel | CheckHead (h : Head)


def inputs : Mode → Head
| Mode.Synth => Head.RawSingle
| Mode.Check => Head.RawPair
| Mode.CheckType => Head.RawSingle
| Mode.CheckHead _ => Head.RawSingle
| Mode.SynthLevel => Head.RawSingle

@[inline, reducible]
abbrev Inputs (n : ℕ) (md : Mode) : Type :=
  ABT sig n (ABTArg.Args (sig (inputs md)))

def outputs : Mode → Head
| Mode.Synth => Head.RawSingle
| Mode.Check => Head.Nothing
| Mode.CheckType => Head.Nothing
| Mode.CheckHead h => h
| Mode.SynthLevel => Head.RawLevel

abbrev Outputs (n : ℕ) (md : Mode) : Type :=
  ABT sig n (ABTArg.Args (sig (outputs md)))




section
  set_option hygiene false
  local notation Γ " ⊢ " t " ∷∈ " T => Derivation Γ Mode.Synth (ABT.singleton t) (ABT.singleton T)
  local notation Γ " ⊢ " T  " ∋∷ " t => Derivation Γ Mode.Check (ABT.pair t T) ABT.argsNil
  local notation Γ " ⊢ "  t "∷[" h "]∈" Ts => Derivation Γ (Mode.CheckHead h) (ABT.singleton t) Ts
  local notation Γ " ⊢ " "𝒰∋" T  => Derivation Γ (Mode.CheckType) (ABT.singleton T) ABT.argsNil
  local notation Γ " ⊢ " T "∈𝒰" ℓ  => Derivation Γ (Mode.SynthLevel) (ABT.singleton T) (ABT.fromNat ℓ)
  class inductive Derivation :
    {n : ℕ}
    → PreCtx n
    → (md : Mode)
    → (ins : Inputs n md)
    → (outs : Outputs n md)
    → Prop where
  | WfTy :
    (Γ ⊢ T ∈𝒰 ℓ)
    → ---------------------------
    (Γ ⊢ 𝒰∋ T)

  | WfTyLevel :
      (Γ ⊢ T ∷∈ S)
    → (S ≡ 𝒰 ℓ )
    → ---------------------------
    (Γ ⊢ T ∈𝒰 ℓ )

  | HeadConv :
      (Γ ⊢ t ∷∈ T)
    → (eq : T ≡ ABT.op h Ts)
    → ---------------------------
    (Γ ⊢ t ∷[ h ]∈ Ts)

  | TyConv :
      (Γ ⊢ t ∷∈ S)
    → (eq : S ≡ T)
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

-- Hygenic version of the notation
set_option hygiene true
notation Γ " ⊢ " t " ∷∈ " T => Derivation Γ Mode.Synth (ABT.singleton t) (ABT.singleton T)
notation Γ " ⊢ " T  " ∋∷ " t => Derivation Γ Mode.Check (ABT.pair t T) ABT.argsNil
notation Γ " ⊢ "  t "∷[" h "]∈" Ts => Derivation Γ (Mode.CheckHead h) (ABT.singleton t) Ts
notation Γ " ⊢ " "𝒰∋" T  => Derivation Γ (Mode.CheckType) (ABT.singleton T) ABT.argsNil
notation Γ " ⊢ " T "∈𝒰" ℓ  => Derivation Γ (Mode.SynthLevel) (ABT.singleton T) (ABT.numLit ℓ)

-- notation Γ " ⊢ " i " ↪[" md "] " o  => Derivation Γ md i o



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
    cases eq
    apply Derivation.TyConv <;> aesop_cat

-- @[aesop unsafe]
lemma allSynth {Γ : PreCtx n} {t : Term n} {T : Term n}
  (checked : (Γ ⊢ T ∋∷ t) := by assumption)
  : ∃ S, ((Γ ⊢ t ∷∈ S)) ∧ (S ≡ T) := by
  cases checked
  aesop

