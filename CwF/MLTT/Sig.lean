
import CwF.ABT.Defs

namespace MLTT
open ABT

inductive Head where
  | Pi | Lam | App
  | Sigma | Pair | Proj₁ | Proj₂
  | True | tt
  | False | exfalso

def sig : Head → List Sig
| Head.Pi => [◾, ν ◾ ]
| Head.Lam => [◾, ν ◾ ]
| Head.App => [◾, ◾]
| Head.Sigma => [◾, ν ◾ ]
| Head.Pair => [◾, ◾]
| Head.Proj₁ => [◾]
| Head.Proj₂ => [◾]
| Head.True => []
| Head.tt => []
| Head.False => []
| Head.exfalso => [◾, ◾]

def Term (n : ℕ) :  Type :=
  ABT sig n ABTArg.Term'
-- set_option maxRecDepth 1000

notation "Πx∷" T ",," S =>
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

notation "⟨" s ",," t "⟩" =>
  Head.Pair (ABT.argsCons (ABT.termArg s) (ABT.argsCons (ABT.termArg t) ABT.argsNil))


notation "π₁" s  =>
  Head.Proj₁ (ABT.argsCons (ABT.termArg s) ABT.argsNil)


notation "π₂" s  =>
  Head.Proj₂ (ABT.argsCons (ABT.termArg s) ABT.argsNil)

notation "True" => ABT.op Head.True ABT.argsNil

notation "tt" => ABT.op Head.tt ABT.argsNil


notation "False" => ABT.op Head.False ABT.argsNil

notation "exfalso" T t => ABT.op Head.exfalso
 ((ABT.termArg T) (ABT.argsCons (ABT.termArg t) ABT.argsNil))


end MLTT
