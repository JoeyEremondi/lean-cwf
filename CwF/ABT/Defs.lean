
import Mathlib.Data.Fin.Fin2
import Mathlib.Logic.Unique
import Mathlib.CategoryTheory.Category.Basic


universe u v'

-- Loosely based off of Jeremy Siek's agda ABTs

inductive Sig : Type where
| plain : Sig
| bind : Sig → Sig

notation "◾" => Sig.plain
notation "ν" x => Sig.bind x

namespace ABT

inductive ABTArg : Type where
  | Term' : ABTArg
  | Args : (List Sig) → ABTArg
  | Arg : Sig → ABTArg


section
    open ABTArg
    variable {Op : Type u} (sig : Op → List Sig)


    inductive ABT : Nat → ABTArg → Type u where
    | var : Fin2 n → ABT n Term'
    | op : (op : Op) → ABT n (Args (sig op)) → ABT n Term'
    | nil : ABT n (Args [])
    | cons :  ABT n (Arg g) →  ABT n (Args t) → ABT n (Args (h :: t))
    | plain : ABT n Term' → ABT n (Arg ◾)
    | bind : ABT (Nat.succ n) (Arg s) → ABT n (Arg (ν s))

end

abbrev Term (sig : Op → List Sig) (n : ℕ) := ABT sig n ABTArg.Term'







