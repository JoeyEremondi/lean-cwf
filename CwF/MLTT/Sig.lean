
import CwF.ABT.Defs
import CwF.ABT.Subst
import Mathlib.Data.Vector3

namespace MLTT
open ABT

inductive Head where
  | Pi | Lam | App
  | Sigma | Pair | Proj₁ | Proj₂
  | True | tt
  | False | exfalso
  | Tipe (ℓ : ℕ)
  | Match {numBranch : ℕ} (vars : Vector3 ℕ numBranch)
  -- Not used for expressions, but to pass substitutions through pairs
  -- when defining e.g. preservation of substitution
  | RawSingle
  | RawPair
  | RawLevel
  | Nothing

def preCtxSig (n : ℕ) := Sig.depVec (fun (i : Fin2 n) => Sig.nClosed i.toNat ◾)

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
-- Pattern match contains numBranch branches. There's a scrutinee and a motive type.
-- which is parameterized over the scrutinee type.
-- Then each branch has a context of its free variables, which we represent
-- as a vector where the index determines the number of free variables.
-- Then ith lhs is a telescope of patterns (terms)
-- that's closed except for the (vars i) pattern variables.
-- The rhs is a closed term except for the (vars i) pattern variables
| Head.Match  vars
  => [◾
      , ν ◾
      , Sig.depVec (fun i => Sig.nClosed 0 (preCtxSig (Vector3.nth i vars)) )
      , Sig.depVec (fun i => Sig.nClosed (Vector3.nth i vars) (Sig.tele ◾))
      , Sig.depVec (fun i => Sig.nClosed (Vector3.nth i vars) ◾)]

| Head.RawSingle => [◾]
| Head.RawPair => [◾, ◾]
| Head.RawLevel => [Sig.numLit]
| Head.Nothing => []

abbrev Term (n : ℕ) :  Type :=
  ABT sig n ABTArg.Term'

abbrev PatCtx n :=
  ABT sig 0 (ABTArg.Arg (preCtxSig n))
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

def Branch (n : ℕ) (numVars : ℕ) : Type :=
  PatCtx numVars
  × ABT sig n (ABTArg.Arg (Sig.nClosed numVars (Sig.tele ◾)))
  × ABT sig n (ABTArg.Arg (Sig.nClosed numVars ◾))

abbrev mkMatch {numBranch : ℕ} {vars : Vector3 ℕ numBranch} (t : Term n) (T : Term (Nat.succ n))
  (Ctxs : (i : Fin2 numBranch) → PatCtx (Vector3.nth i vars) )
  (lhss : (i : Fin2 numBranch) → ABT sig n (ABTArg.Arg (Sig.nClosed (Vector3.nth i vars) (Sig.tele ◾))))
  (rhss : (i : Fin2 numBranch) → ABT sig n (ABTArg.Arg (Sig.nClosed (Vector3.nth i vars) ◾)))
  : Term n := by
    apply ABT.op (Head.Match vars)
    apply ABT.argsCons (ABT.termArg t)
    apply ABT.argsCons (ABT.bind (ABT.termArg T))
    apply ABT.argsCons (ABT.termVec _)
    apply ABT.argsCons (ABT.termVec lhss)
    apply ABT.argsCons (ABT.termVec rhss)
    apply ABT.argsNil
    intros i
    constructor
    apply Ctxs


notation "match" t " to " T "[[" Ξ ",," lhss "↦" rhss "]]"  => mkMatch t T Ξ lhss rhss

def foo  : _ → _ → _ → Term 0 := fun Δ lhs rhs =>
  match tt to ⊤ [[Δ ,, lhs ↦ rhs]]


end MLTT
