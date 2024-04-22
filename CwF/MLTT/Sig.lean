
import CwF.ABT.Defs
import CwF.ABT.Subst

namespace MLTT
open ABT

inductive Head where
  | Pi | Lam | App
  | Sigma | Pair | Proj₁ | Proj₂
  | True | tt
  | False | exfalso
  | Tipe (ℓ : ℕ)
  | Match (numBranch : ℕ)
  -- Not used for expressions, but to pass substitutions through pairs
  -- when defining e.g. preservation of substitution
  | RawSingle
  | RawPair
  | RawLevel
  | Nothing

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
| Head.Match numBranch => [Sig.vec numBranch (Sig.bind ◾), Sig.vec numBranch (Sig.bind ◾)]

| Head.RawSingle => [◾]
| Head.RawPair => [◾, ◾]
| Head.RawLevel => [Sig.numLit]
| Head.Nothing => []

def Term (n : ℕ) :  Type :=
  ABT sig n ABTArg.Term'
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



end MLTT
