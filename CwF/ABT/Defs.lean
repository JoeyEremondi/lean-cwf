
import Mathlib.Data.Fin.Fin2
import Mathlib.Logic.Unique
import Mathlib.CategoryTheory.Category.Basic


universe u v'

-- Loosely based off of Jeremy Siek's agda ABTs

inductive Sig : Type where
| plain : Sig
| tele : Sig
| vec : ℕ → Sig
| list : ℕ → Sig
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
  | Tele : ABTArg


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
    | termListNil : ABT n (Arg list)
    | termListCons : ABT n Term' → ABT n (Arg list) → ABT n (Arg list)
    -- Arg for vec is exactly n terms, handy when we want parallel lists constrained
    -- to have the same length
    | termVecNil : ABT n (Arg (Sig.vec 0))
    | termVecCons : ABT n Term' → ABT n (Arg (Sig.vec len)) → ABT n (Arg (Sig.vec (Nat.succ len)))
    -- Arg for tele is just a telescope
    -- Having this lets us have a single case for binding, makes the proofs easier
    | teleArg : ABT n Tele → ABT n (Arg tele)
    -- Arg for a binding is a term with one more free variable
    | bind : ABT (Nat.succ n) (Arg s) → ABT n (Arg (ν s))


    -- --Telescope for n is a list of n terms, where each term has one more variable than the last
    | teleNil : ABT n Tele
    | teleCons : ABT n Term' → ABT n (Arg (Sig.bind Sig.tele) ) → ABT n Tele


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
| ABT.teleArg t => ABT.teleArg (map quote wk ρ t)
| ABT.termListNil  => ABT.termListNil
| ABT.termListCons h t  => ABT.termListCons (map quote wk ρ h) (map quote wk ρ t)
| ABT.termVecNil  => ABT.termVecNil
| ABT.termVecCons h t  => ABT.termVecCons (map quote wk ρ h) (map quote wk ρ t)
| ABT.bind t => ABT.bind (map quote wk (wk ρ ) t)
| ABT.teleNil => ABT.teleNil
| ABT.teleCons ts t => ABT.teleCons (map quote wk ρ ts) (map quote wk ρ t)

end ABT
