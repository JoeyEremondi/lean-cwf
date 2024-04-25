

import CwF.ABT.Defs
import CwF.ABT.Subst
import CwF.ABT.SubstProperties
import Mathlib.Data.Vector3
import CwF.MLTT.Sig

namespace MLTT
open ABT

structure CaseSplit (n : ℕ) : Type where
  {numBranch : ℕ}
  {numScrut : ℕ}
  ts : TermVec sig n numScrut
  Ts : TermTele sig 0 numScrut
  Tmotive : Term numScrut
  xs :  ((i : Fin2 numBranch) → PatCtx )
  lhss : ((i : Fin2 numBranch) → (TermVec sig (xs i).fst numScrut))
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


abbrev unCases (t : ABT sig n (ABTArg.Args (sig (Head.CaseSplit (numBranch := numBranch) vars numScrut))))
  : CaseSplit n:= by
    simp [sig] at t
    cases t with
    | argsCons ts rest => cases rest with
    | argsCons Ts rest => cases Ts with
    | nClosed Ts => cases rest with
    | argsCons Tmotive rest => cases Tmotive with
    | nClosed Tmotive => cases Tmotive with
    | termArg Tmotive => cases rest with
    | argsCons xs rest => cases xs with
    | termVec xs => cases rest with
    | argsCons lhss rest => cases lhss with
    | termVec lhss => cases rest with
    | argsCons rhss rest => cases rhss with
    | termVec rhss =>
      fapply CaseSplit.mk ts Ts Tmotive <;> (try intros i) <;> try simp
      . fconstructor
        . apply vars i
        . cases (xs i) ; assumption
      . cases (lhss i) ; assumption
      . cases (rhss i) with
        | nClosed x => cases x ; assumption



-- We use "casesplit" to avoid conflicts with "case" or "match" in lean
notation "casesplit" ts "∷" Ts " to " Tmotive "[[" xs ",," lhss "↦" rhss "]]"  => mkCases ⟨ts, Ts, Tmotive, xs, lhss, rhss⟩

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
