
import CwF.ABT.Defs
import CwF.ABT.Subst
import CwF.ABT.Renaming
import CwF.ABT.SubstProperties
import CwF.MLTT.Sig
import CwF.MLTT.Reductions


namespace MLTT
open ABT

-- We leave this completely unspecified. We'll refine what it means later
class IsCover {numBranch} {numScrut}
  (Ts : TermTele sig 0 numScrut) (xs : ((i : Fin2 numBranch) → PatCtx ))
  (lhss : (i : Fin2 numBranch) → (TermVec sig (xs i).fst numScrut)) where


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

-- A closed telescope can be reversed to make a context
def snocTele {len : ℕ} : {m : ℕ} → (Γ : PreCtx m) →  (Ts : ABT sig m (ABTArg.Arg (◾tele len)))  → PreCtx (m+len) := by
  induction len with intros m Γ Ts
  | zero => apply Γ
  | succ len IH =>
      simp [Nat.add_succ, <- Nat.succ_add]
      simp [Nat.add_succ, <- Nat.succ_add] at IH
      apply IH
      . apply ctxCons Γ
        cases ABT.abtVecLookup Ts Fin2.fz
        assumption
      . apply ABT.termVec
        intros i
        cases ABT.abtVecLookup Ts (Fin2.fs i)
        assumption

def ofTele {len : ℕ} (Ts : TermTele sig 0 len) : PreCtx len := by
  let ret := snocTele ⬝ Ts
  simp at ret
  apply ret

end PreCtx
infixr:80 "<>" => PreCtx.snocTele

instance {n : ℕ} : GetElem (PreCtx n) (Fin2 n) (Term n) (fun _ _ => True) where
  getElem Γ x _ := PreCtx.lookup Γ x

-- lemma rename_lookup {m n : ℕ} {Δ : PreCtx m} {Γ : PreCtx n}

inductive Mode :=
  | Synth | Check | CheckType | SynthLevel | CheckHead (h : Head)
  | CheckTele (n : ℕ)
  | IsTele (n : ℕ)


def inputs : Mode → Head
| Mode.Synth => Head.RawSingle
| Mode.Check => Head.RawPair Head.RawSingle Head.RawSingle
| Mode.CheckType => Head.RawSingle
| Mode.CheckHead _ => Head.RawSingle
| Mode.SynthLevel => Head.RawSingle
| Mode.CheckTele n => Head.RawPair (Head.RawVec n) (Head.RawTele n)
| Mode.IsTele n => Head.RawTele n

@[inline, reducible]
abbrev Inputs (n : ℕ) (md : Mode) : Type :=
  ABT sig n (ABTArg.Args (sig (inputs md)))

def outputs : Mode → Head
| Mode.Synth => Head.RawSingle
| Mode.Check => Head.Nothing
| Mode.CheckType => Head.Nothing
| Mode.CheckHead h => h
| Mode.SynthLevel => Head.RawLevel
| Mode.CheckTele n => Head.Nothing
| Mode.IsTele n => Head.Nothing

abbrev Outputs (n : ℕ) (md : Mode) : Type :=
  ABT sig n (ABTArg.Args (sig (outputs md)))




section
  set_option hygiene false
  local notation Γ " ⊢ " t " ∷∈ " T => Derivation Γ Mode.Synth (ABT.singleton t) (ABT.singleton T)
  local notation Γ " ⊢ " T  " ∋∷ " t => Derivation Γ Mode.Check (ABT.pair t T) ABT.argsNil
  local notation Γ " ⊢ "  t "∷[" h "]∈" Ts => Derivation Γ (Mode.CheckHead h) (ABT.singleton t) Ts
  local notation Γ " ⊢ " "𝒰∋" T  => Derivation Γ (Mode.CheckType) (ABT.singleton T) ABT.argsNil
  local notation Γ " ⊢ " T "∈𝒰" ℓ  => Derivation Γ (Mode.SynthLevel) (ABT.singleton T) (ABT.fromNat ℓ)
  local notation Γ " ⊢ " Ts "∋∷[" n "] " ts
    => Derivation Γ (Mode.CheckTele n) (ABT.argsCons ts (ABT.argsCons Ts argsNothing)) ABT.argsNil
  local notation Γ " ⊢ " "𝒰∋[" n "]" T  => Derivation Γ (Mode.IsTele n) (ABT.argsCons T ABT.argsNil) ABT.argsNil
  class inductive Derivation :
    {n : ℕ}
    → PreCtx n
    → (md : Mode)
    → (ins : Inputs n md)
    → (outs : Outputs n md)
    → Prop where
  -- A type is well formed if it synthesizes a universe level
  | WfTy :
    (Γ ⊢ T ∈𝒰 ℓ)
    → ---------------------------
    (Γ ⊢ 𝒰∋ T)

  -- A type synthesizes a universe level if it synthesizes a type
  -- that is equal to a universe at some level
  | WfTyLevel :
      (Γ ⊢ T ∷∈ S)
    → (S ≡ 𝒰 ℓ )
    → ---------------------------
    (Γ ⊢ T ∈𝒰 ℓ )

  -- Check a term against the given syntactic former, synthesizing its arguments
  | HeadConv :
      (Γ ⊢ t ∷∈ T)
    → (eq : T ≡ ABT.op h Ts)
    → ---------------------------
    (Γ ⊢ t ∷[ h ]∈ Ts)

  -- If a term synthesizes a type, it checks against any definitionally equal type
  | TyConv :
      (Γ ⊢ t ∷∈ S)
    → (eq : S ≡ T)
    → -----------------------------
      (Γ ⊢ T ∋∷ t)

  -- The empty telescope is well typed
  | IsTeleNil {Γ : PreCtx n} :
  ---------------------
    (Γ ⊢ 𝒰∋[0] [[]] )

  -- Well-formed types extend well-formed telescopes
  | IsTeleCons :
    (Γ ⊢ 𝒰∋ T)
  → ((Γ▸T) ⊢ 𝒰∋[len] Ts)
  →--------------------
    (Γ ⊢ 𝒰∋[Nat.succ len] [[x∷ T,, Ts ]] )

  -- Well formed environments (substitutions)
  -- Empty env has empty telescope type
  | EnvCheckNil {Γ : PreCtx n} :
  ---------------------
    (Γ ⊢ [[]] ∋∷[ 0 ] [[]] )

  --Vector extension typed like a dependent pair
  | EnvCheckCons {Γ : PreCtx n } :
      (Γ ⊢ S ∋∷ s)
    → ((Γ▸S) ⊢ 𝒰∋[len] Ts)
    → (Γ ⊢ Ts/[s /x] ∋∷[ len ] ts )
    →-----------------------------
    (Γ ⊢  [[x∷ S,, Ts]] ∋∷[Nat.succ len] (s ∷v ts) )

  -- Variables synthesize their types from the context
  | VarSynth  :
  -----------------------------
  (Γ ⊢ ABT.var x ∷∈ Γ[x])


  -- Functions: standard
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

  -- Pairs: standard
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

  | MatchTy {Γ : PreCtx n} {Ts : TermTele sig 0 numScrut} :
      [IsCover Ts xs lhss]
    → (Γ ⊢ (Renaming.fromClosed Ts) ∋∷[ numScrut ] ts)
    → (∀ i, (PreCtx.ofTele (xs i).snd) ⊢ T⦇Subst.syntacticEquiv.toFun (lhss i)⦈ ∋∷ (rhss i) )
    →-------------------------------
    (Γ ⊢ casesplit ts ∷ Ts to Tmotive [[xs ,, lhss ↦ rhss  ]] ∷∈ Tmotive⦇Subst.syntacticEquiv.toFun ts⦈)


  --
  -- | CaseSplit
  -- ----------------------------------
  -- (Γ ⊢ casesplit ts )


end
open Derivation

-- Hygenic version of the notation
set_option hygiene true
notation Γ " ⊢ " t " ∷∈ " T => Derivation Γ Mode.Synth (ABT.singleton t) (ABT.singleton T)
notation Γ " ⊢ " T  " ∋∷ " t => Derivation Γ Mode.Check (ABT.pair t T) ABT.argsNil
notation Γ " ⊢ "  t "∷[" h "]∈" Ts => Derivation Γ (Mode.CheckHead h) (ABT.singleton t) Ts
notation Γ " ⊢ " "𝒰∋" T  => Derivation Γ (Mode.CheckType) (ABT.singleton T) ABT.argsNil
notation Γ " ⊢ " T "∈𝒰" ℓ  => Derivation Γ (Mode.SynthLevel) (ABT.singleton T) (ABT.numLit ℓ)
notation Γ " ⊢ " Ts "∋∷[" n "] " ts
  => Derivation Γ (Mode.CheckTele n) (ABT.argsCons ts (ABT.argsCons Ts ABT.argsNothing)) ABT.argsNil
notation Γ " ⊢ " "𝒰∋[" n "]" T  => Derivation Γ (Mode.IsTele n) (ABT.argsCons T ABT.argsNil) ABT.argsNil

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

