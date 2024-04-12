
import Mathlib.Data.Fin.Fin2
import Mathlib.Logic.Unique
import Mathlib.CategoryTheory.Category.Basic


universe u v'

-- Loosely based off of Jeremy Siek's agda ABTs

inductive Sig : Type where
| plain : Sig
| tele : Sig → Sig
| vec : ℕ → Sig → Sig
| list : Sig → Sig
| bind : Sig → Sig

notation "◾" => Sig.plain
notation "ν" x => Sig.bind x

namespace ABT

inductive ABTArg : Type where
  | Term' : ABTArg
  | Args : (List Sig) → ABTArg
  | Arg : Sig → ABTArg
  -- | Vec : ℕ → ABTArg
  -- | List : ABTArg


section
    open ABTArg
    variable {Op : Type u} (sig : Op → List Sig)


    inductive ABT : Nat → ABTArg → Type u where
    -- Terms: variables, or an operation applied to some arguments
    | var : Fin2 n → ABT n Term'
    | op : (op : Op) → ABT n (Args (sig op)) → ABT n Term'

    -- Args consist of an arg for each inductive in the signature
    | nil : ABT n (Args [])
    | cons :  ABT n (Arg g) →  ABT n (Args t) → ABT n (Args (h :: t))

    -- Arg for ◾ is just a term
    | termArg : ABT n Term' → ABT n (Arg ◾)
    -- Arg for list is zero or more terms
    | termListNil : ABT n (Arg (Sig.list s))
    | termListCons : ABT n (Arg s) → ABT n (Arg (Sig.list s)) → ABT n (Arg (Sig.list s))
    -- Arg for vec is exactly n terms, handy when we want parallel lists constrained
    -- to have the same length
    | termVecNil : ABT n (Arg (Sig.vec 0 s))
    | termVecCons : ABT n (Arg s) → ABT n (Arg (Sig.vec len s)) → ABT n (Arg (Sig.vec (Nat.succ len) s))
    -- Telescope is like a list, but we gain a binding for each element
    | teleArgNil : ABT n (Arg (Sig.tele s))
    | teleArgCons : ABT n Term' → ABT n (Arg (Sig.bind (Sig.tele s)) ) → ABT n (Arg (Sig.tele s))
    -- Arg for a binding is a term with one more free variable
    | bind : ABT (Nat.succ n) (Arg s) → ABT n (Arg (ν s))



end

abbrev Term (sig : Op → List Sig) (n : ℕ) := ABT sig n ABTArg.Term'


-- Generic traversal structure for substitution, renaming, etc.
abbrev map {V : ℕ → Type u}
  (quote : ∀ {a}, V a → Term sig a )
  (wk : ∀ {a} {b}, (Fin2 a → V b) → Fin2 (Nat.succ a) → V (Nat.succ b))
  (ρ : Fin2 n → V m) :
  ( ABT sig n tag) → ABT sig m tag
| ABT.var x => (quote (ρ x))
| ABT.op op args => ABT.op op (map quote wk ρ args)
| ABT.nil => ABT.nil
| ABT.cons h t => ABT.cons (map quote wk ρ h) (map quote wk ρ t)
| ABT.termArg t => ABT.termArg (map quote wk ρ t)
| ABT.teleArgNil => ABT.teleArgNil
| ABT.teleArgCons ts t => ABT.teleArgCons (map quote wk ρ ts) (map quote wk ρ t)
| ABT.termListNil  => ABT.termListNil
| ABT.termListCons h t  => ABT.termListCons (map quote wk ρ h) (map quote wk ρ t)
| ABT.termVecNil  => ABT.termVecNil
| ABT.termVecCons h t  => ABT.termVecCons (map quote wk ρ h) (map quote wk ρ t)
| ABT.bind t => ABT.bind (map quote wk (wk ρ ) t)

end ABT
