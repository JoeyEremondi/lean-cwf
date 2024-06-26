
import CwF.ABT.ABT
import CwF.ABT.Subst
import CwF.ABT.Renaming
import CwF.ABT.SubstProperties
import CwF.MLTT.Sig
import CwF.MLTT.Reductions


namespace MLTT
open ABT

variable [Ind] [Arities]

class IndTypes where
  closedParamTypes : ∀ c (ℓ : ℕ), TermTele 0 (Arities.numParams c)
  closedFieldTypes : ∀ {c} (d : Ind.Ctor c) (ℓ : ℕ) , TermTele (Arities.numParams c) (Arities.arity d)


namespace IndTypes
  variable [IndTypes]
  def paramTypes (c : Ind.TyCtor) (ℓ : ℕ) :  TermTele n (Arities.numParams c) :=
    (IndTypes.closedParamTypes c ℓ)⦇Renaming.fromClosed⦈ᵣ

  @[simp]
  theorem paramSubst {c : Ind.TyCtor} {ℓ : ℕ} {θ : Subst m n} :
    (paramTypes (n := n) c ℓ)⦇θ⦈ = paramTypes (n := m) c ℓ := by
      simp only [paramTypes, Renaming.fromClosed]
      unfold_subst

  @[simp]
  theorem paramRen {c : Ind.TyCtor} {ℓ : ℕ} {ρ : Renaming m n} :
    (paramTypes (n := n) c ℓ)⦇ρ⦈ᵣ = paramTypes (n := m) c ℓ := by
      simp only [paramTypes, Renaming.fromClosed]
      unfold_rename

  def fieldTypes {c : Ind.TyCtor} (d : Ind.Ctor c) (ℓ : ℕ)
    (params : TermVec n (Arities.numParams c))
    : TermTele n (Arities.arity d) :=
    (IndTypes.closedFieldTypes d ℓ)⦇Subst.syntacticEquiv.toFun params⦈

  @[simp]
  theorem fieldSubst : (fieldTypes d ℓ params)⦇θ⦈ = fieldTypes d ℓ params⦇θ⦈ := by
      simp only [fieldTypes, Renaming.fromClosed]
      unfold_subst
      simp [ Subst.syntacticSubComp]

  @[simp]
  theorem fieldRen : (fieldTypes d ℓ params)⦇ρ⦈ᵣ = fieldTypes d ℓ params⦇ρ⦈ᵣ := by
      simp only [fieldTypes, Renaming.fromClosed]
      unfold_rename
      simp [ Subst.syntacticSubComp]

end IndTypes

variable [IndTypes]
-- We leave this completely unspecified. We'll refine what it means later
class Coverage : Type where
  IsCover
    {numBranch} {numScrut}
    (Ts : TermTele 0 numScrut) (xs : ((i : Fin2 numBranch) → PatCtx ))
    (lhss : (i : Fin2 numBranch) → (TermVec (xs i).fst numScrut)) : Prop
  -- The identity should always be a cover
  idCover : IsCover (numBranch := 1) Ts (fun _ => ⟨_ , Ts⟩) (fun _ => Subst.syntacticEquiv.invFun Subst.id)
  -- -- The constructors should cover an inductive type
  -- ctorCover (c : Ind.TyCtor) (ℓ : ℕ) (ctx : TermTele 0 n) (params : TermVec n (Arities.numParams c))
  --   : IsCover (numBranch := Ind.numCtors c)
  --       (teleSnoc ctx (by simp ; apply c [ℓ:= ℓ] params) )
  --       (fun di => by simp)
  --       (by simp)

variable [Coverage] [IndTypes]
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
def snocTele {len : ℕ} : {m : ℕ} → (Γ : PreCtx m) →  (Ts : ABT m (ABTArg.Arg (◾tele len)))  → PreCtx (m+len) := by
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

def ofTele {len : ℕ} (Ts : TermTele 0 len) : PreCtx len := by
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
  ABT n (ABTArg.Args (sig (inputs md)))

def outputs : Mode → Head
| Mode.Synth => Head.RawSingle
| Mode.Check => Head.Nothing
| Mode.CheckType => Head.Nothing
| Mode.CheckHead h => h
| Mode.SynthLevel => Head.RawLevel
| Mode.CheckTele _ => Head.Nothing
| Mode.IsTele _ => Head.Nothing

abbrev Outputs (n : ℕ) (md : Mode) : Type :=
  ABT n (ABTArg.Args (sig (outputs md)))




section
  set_option hygiene false
  local notation Γ " ⊢ " t " ∷∈ " T => Derivation Γ Mode.Synth (ABTsingleton t) (ABTsingleton T)
  local notation Γ " ⊢ " T  " ∋∷ " t => Derivation Γ Mode.Check (ABTpair t, T) ABT.argsNil
  local notation Γ " ⊢ "  t "∷[" h "]∈" Ts => Derivation Γ (Mode.CheckHead h) (ABTsingleton t) Ts
  local notation Γ " ⊢ " "𝒰∋" T  => Derivation Γ (Mode.CheckType) (ABTsingleton T) ABT.argsNil
  local notation Γ " ⊢ " T "∈𝒰" ℓ  => Derivation Γ (Mode.SynthLevel) (ABTsingleton T) (ABTfromNat ℓ)
  local notation Γ " ⊢ " Ts "∋∷[" n "] " ts
    => Derivation Γ (Mode.CheckTele n) (ABT.argsCons ts (ABT.argsCons Ts ABT.argsNil)) ABT.argsNil
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
    (Γ ⊢ 𝒰∋[0] Ts )

  -- Well-formed types extend well-formed telescopes
  | IsTeleCons :
    (Γ ⊢ 𝒰∋ T)
  → ((Γ▸T) ⊢ 𝒰∋[len] Ts)
  →--------------------
    (Γ ⊢ 𝒰∋[Nat.succ len] [[x∷ T,, Ts ]] )

  -- Well formed environments (substitutions)
  -- Empty env has empty telescope type
  -- All telescopes of length 0 are equal
  | EnvCheckNil {Γ : PreCtx n} :
  ---------------------
    (Γ ⊢ t ∋∷[ 0 ] Ts )

  --Vector extension typed like a dependent pair
  | EnvCheckCons {n len : ℕ} {Γ : PreCtx n } {s : Term n} {ts : TermVec n len} {S : Term n} {Ts : TermTele (Nat.succ n) len} :
      (Γ ⊢ S ∋∷ s)
    -- → ((Γ▸S) ⊢ 𝒰∋[len] Ts)
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
      (Γ ⊢ (t s) ∷∈ T/[s /x])


  | TyCtorTy {Γ : PreCtx n} {c : Ind.TyCtor} {ts : TermVec n (Arities.numParams c)} :
    --
    (Γ ⊢ IndTypes.paramTypes c ℓ  ∋∷[ Arities.numParams c ] ts)
    →----------------------------------
     Γ ⊢ (c [ℓ:= ℓ] ts) ∷∈ 𝒰 ℓ


  | CtorTy {Γ : PreCtx n} {d : Ind.Ctor c}
    {pars : TermVec n (Arities.numParams c)}
    {ts : TermVec n (Arities.arity d)} :
    --
      (Γ ⊢ IndTypes.paramTypes c ℓ  ∋∷[ Arities.numParams c ] pars)
    → (Γ ⊢ (IndTypes.fieldTypes d ℓ pars) ∋∷[ Arities.arity d ] ts)
    →----------------------------------
     Γ ⊢ (d [ℓ:= ℓ] pars ts) ∷∈ (c [ℓ:= ℓ] pars)


  | MatchTy {n : ℕ} {Γ : PreCtx n} {numScrut} {numBranches : ℕ} {ts} {Ts : TermTele 0 numScrut}
                {Tmotive} {xs} {lhss : (i : Fin2 numBranches) → _} {rhss} :

      Coverage.IsCover Ts xs lhss
    → (Γ ⊢ (Ts⦇Renaming.fromClosed⦈ᵣ) ∋∷[ numScrut ] ts)
    → (∀ i, (PreCtx.ofTele (xs i).snd) ⊢ Tmotive⦇Subst.syntacticEquiv.toFun (lhss i)⦈ ∋∷ (rhss i) )
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
notation3 Γ " ⊢ " t " ∷∈ " T => Derivation Γ Mode.Synth (ABTsingleton t) (ABTsingleton T)
notation Γ " ⊢ " T  " ∋∷ " t => Derivation Γ Mode.Check (ABT.argsCons (ABT.termArg t) (ABT.argsCons (ABT.termArg T) ABT.argsNil)) ABT.argsNil
notation3 Γ " ⊢ "  t " ∷[" h "]∈ " Ts => Derivation Γ (Mode.CheckHead h) (ABTsingleton t) Ts
notation3 Γ " ⊢ 𝒰∋ " T  => Derivation Γ (Mode.CheckType) (ABT.argsCons (ABT.termArg T) ABT.argsNil) ABT.argsNil
notation3 Γ " ⊢ " T " ∈𝒰 " ℓ  => Derivation Γ (Mode.SynthLevel) (ABTsingleton T) (ABTfromNat ℓ)
notation Γ " ⊢ " Ts " ∋∷[" len "] " ts
  => Derivation Γ (Mode.CheckTele len) (ABT.argsCons ts (ABT.argsCons Ts ABT.argsNil)) ABT.argsNil
notation3 Γ " ⊢ 𝒰∋[" len "]" T  => Derivation Γ (Mode.IsTele len) (ABT.argsCons T ABT.argsNil) ABT.argsNil

-- notation Γ " ⊢ " i " ↪[" md "] " o  => Derivation Γ md i o



-- Take advantage of the fact that synthesis is directed on the syntax of terms
-- So in tactics, we can apply this to synthesize a type for any term
-- @[aesop unsafe]
lemma synthEq {Γ : PreCtx n} {t : Term n} {S T : Term n}
  (synthed : (Γ ⊢ t ∷∈ S) := by constructor) (eq : S = T := by aesop_cat)
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

