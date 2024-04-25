

import CwF.ABT.ABT
import CwF.ABT.Subst
import CwF.ABT.SubstProperties
import Mathlib.Data.Vector3
import CwF.MLTT.Sig

namespace MLTT
open ABT


abbrev unCases (t : ABT n (ABTArg.Args (sig (Head.CaseSplit (numBranch := numBranch) vars numScrut))))
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



