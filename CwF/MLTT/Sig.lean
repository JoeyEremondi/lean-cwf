
import CwF.ABT.ABT
import CwF.ABT.Subst
import CwF.ABT.SubstProperties
import Mathlib.Data.Vector3

namespace MLTT
open ABT

class Ind : Type 1 where
  TyCtor : Type
  Ctor : TyCtor → Type

class Arities [Ind] : Type 1 where
  numParams : Ind.TyCtor → ℕ
  arity : Ind.Ctor c → ℕ


variable [Ind] [Arities]

inductive Head where
  | Pi | Lam | App
  | Sigma | Pair | Proj₁ | Proj₂
  | True | tt
  | False | exfalso
  | Tipe (ℓ : ℕ)
  | CaseSplit {numBranch : ℕ} (vars : Vector3 ℕ numBranch) (numScrut : ℕ)
  | TyCtor (c : Ind.TyCtor)
  | Ctor (d : Ind.Ctor c)
  -- Not used for expressions, but to pass substitutions through pairs
  -- when defining e.g. preservation of substitution
  | RawSingle
  | RawPair (x y : Head)
  | RawLevel
  | Nothing
  | RawTele (len : ℕ)
  | RawVec (len : ℕ)


def sig : Head → List Sig
| Head.Pi => [◾, ν ◾ ]
| Head.Lam => [◾, ν ◾ ]
| Head.App => [◾, ◾]
| Head.Sigma => [◾, ν ◾ ]
| Head.Pair => [◾, ◾, ν ◾]
| Head.Proj₁ => [◾]
| Head.Proj₂ => [◾]
| Head.True => []
| Head.tt => []
| Head.False => []
| Head.exfalso => [◾, ◾]
| Head.Tipe _ => []
| Head.TyCtor ctor => [◾tele (Arities.numParams ctor)]
| @Head.Ctor _ tyCtor ctor => [◾tele (Arities.numParams tyCtor + Arities.arity ctor)]
-- Pattern match contains numBranch branches. There's a scrutinee and a motive type.
-- which is parameterized over the scrutinee type.
-- Then each branch has a context of its free variables, which we represent
-- as a vector where the index determines the number of free variables.
-- Then ith lhs is a telescope of patterns (terms)
-- that's closed except for the (vars i) pattern variables.
-- The rhs is a closed term except for the (vars i) pattern variables
| Head.CaseSplit vars numScrut
  => [◾vec numScrut
      , Sig.nClosed 0 (◾tele numScrut)
      , Sig.nClosed numScrut ◾
      , Sig.depVec _ (fun i => Sig.nClosed 0 (◾tele (Vector3.nth i vars)) )
      , Sig.depVec _ (fun i => Sig.nClosed (Vector3.nth i vars) (◾vec numScrut))
      , Sig.depVec _ (fun i => Sig.nClosed (Vector3.nth i vars) ◾)]

| Head.RawSingle => [◾]
| Head.RawPair x y => sig x ++  sig y
| Head.RawLevel => [Sig.numLit]
| Head.RawTele len => [ ◾tele len ]
| Head.RawVec len => [ ◾vec  len]
| Head.Nothing => []


instance : Signature.{0} where
  Op := Head
  sig := sig


abbrev PatCtx :=
  (n : ℕ) × ABT 0 (ABTArg.Arg (◾tele n))

-- set_option maxRecDepth 1000



notation:50 "x∷" T ",," S =>
    ( ABT.argsCons (ABT.termArg T) (ABT.argsCons (ABT.bind (ABT.termArg S)) ABT.argsNil) )

notation:50 "Πx∷" T ",," S =>
  ABT.op Head.Pi
    ( ABT.argsCons (ABT.termArg T) (ABT.argsCons (ABT.bind (ABT.termArg S)) ABT.argsNil) )

notation "λx∷" T ",," t =>
  ABT.op Head.Lam
    ( ABT.argsCons (ABT.termArg T) (ABT.argsCons (ABT.bind (ABT.termArg t)) ABT.argsNil) )

notation f "$" t =>
  ABT.op Head.App (ABT.argsCons (ABT.termArg f) (ABT.argsCons (ABT.termArg t) ABT.argsNil))

notation "Σx∷" T ",," S =>
  ABT.op Head.Sigma
    ( ABT.argsCons (ABT.termArg T) (ABT.argsCons (ABT.bind (ABT.termArg S)) ABT.argsNil) )

notation "⟨x↦" s ",," t "∷x,," T "⟩" =>
  ABT.op Head.Pair (ABT.argsCons (ABT.termArg s)
                   (ABT.argsCons (ABT.termArg t)
                   (ABT.argsCons (ABT.bind (ABT.termArg T)) ABT.argsNil)))


notation "π₁" s  =>
  ABT.op Head.Proj₁ (ABT.argsCons (ABT.termArg s) ABT.argsNil)


notation "π₂" s  =>
  ABT.op Head.Proj₂ (ABT.argsCons (ABT.termArg s) ABT.argsNil)

notation "⊤" => ABT.op Head.True ABT.argsNil

notation "tt" => ABT.op Head.tt ABT.argsNil


notation "⊥" => ABT.op Head.False ABT.argsNil

notation "exfalso" T t => ABT.op Head.exfalso
 ((ABT.termArg T) (ABT.argsCons (ABT.termArg t) ABT.argsNil))


notation:50 " 𝒰 " ℓ => ABT.op (Head.Tipe ℓ) ABT.argsNil

-- def Branch (n : ℕ) (numVars : ℕ) : Type :=
--   PatCtx numVars
--   × ABT n (ABTArg.Arg (Sig.nClosed numVars (Sig.tele ◾)))
--   × ABT n (ABTArg.Arg (Sig.nClosed numVars ◾))

instance  : Coe (Term n) (Term n → Term n) where
  coe f := fun t => f $ t


structure CaseSplit (n : ℕ) : Type where
  {numBranch : ℕ}
  {numScrut : ℕ}
  ts : TermVec n numScrut
  Ts : TermTele 0 numScrut
  Tmotive : Term numScrut
  xs :  ((i : Fin2 numBranch) → PatCtx )
  lhss : ((i : Fin2 numBranch) → (TermVec (xs i).fst numScrut))
  rhss : ( (i : Fin2 numBranch) → Term (xs i).fst)


@[irreducible]
def mkCases (cs : CaseSplit n) : Term n := by
    let vars := fun i => (cs.xs i).fst
    apply ABT.op (Head.CaseSplit vars cs.numScrut)
    apply ABT.argsCons cs.ts
    apply ABT.argsCons (ABT.nClosed cs.Ts)
    apply ABT.argsCons (ABT.nClosed (ABT.termArg cs.Tmotive))
    apply ABT.argsCons (ABT.termVec _)
    apply ABT.argsCons (ABT.termVec (fun branch => ABT.nClosed (ABT.termVec (ABT.termArg ∘ (Subst.syntacticEquiv.toFun (cs.lhss branch))))))
    apply ABT.argsCons (ABT.termVec (fun branch => ABT.nClosed (ABT.termArg (cs.rhss branch))))
    apply ABT.argsNil
    intros i
    constructor
    apply (fun branch => (cs.xs branch).snd)


-- We use "casesplit" to avoid conflicts with "case" or "match" in lean
notation3 "casesplit" ts " ∷ " Ts " to " Tmotive " [[" xs ",," lhss " ↦ " rhss "]]"  => mkCases ⟨ts, Ts, Tmotive, xs, lhss, rhss⟩

-- Substitutions never propogate into the branches of top level matches
@[simp]
theorem mkMatchSubst : (casesplit ts ∷ Ts to T [[xs ,, lhss ↦ rhss]])⦇θ⦈ = casesplit ts⦇θ⦈ ∷ Ts to T [[xs ,, lhss ↦ rhss]]
  := by
  unfold mkCases
  simp

@[simp]
theorem mkMatchRen : (casesplit ts ∷ Ts to T [[xs ,, lhss ↦ rhss]])⦇θ⦈ᵣ = casesplit ts⦇θ⦈ᵣ ∷ Ts to T [[xs ,, lhss ↦ rhss]]
  := by
  unfold mkCases
  simp [Subst.substOfRenaming]

end MLTT
