
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
| numLit : Sig
-- | empty : Sig

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
    | numLit : ℕ → ABT n (ABTArg.Arg (Sig.numLit))

    -- Args consist of an arg for each inductive in the signature
    | argsNil : ABT n (Args [])
    | argsCons :  ABT n (Arg h) →  ABT n (Args t) → ABT n (Args (h :: t))

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

open ABT

abbrev Term (sig : Op → List Sig) (n : ℕ) := ABT sig n ABTArg.Term'

abbrev x0 : Term sig (Nat.succ n) := ABT.var Fin2.fz

-- infixr:67 "∷" => argsCons
-- notation:67 "∅" => argsNil
-- infixr:67 "∷" => termListCons
-- notation:67 "∅" => termListNil
-- infixr:67 "∷" => termVecCons
-- notation:67 "∅" => termVecNil
-- infixr:67 "∷" => teleArgCons
-- notation:67 "∅" => teleArgNil

-- Generic traversal structure for substitution, renaming, etc.
abbrev map {V : ℕ → Type u}
  (quote : ∀ {a}, V a → Term sig a )
  (wk : ∀ {a} {b}, (Fin2 a → V b) → Fin2 (Nat.succ a) → V (Nat.succ b))
  (ρ : Fin2 n → V m) :
  ( ABT sig n tag) → ABT sig m tag
| numLit x => numLit x
| var x => (quote (ρ x))
| op o args => op o (map quote wk ρ args)
| argsNil => argsNil
| argsCons h t => argsCons (map quote wk ρ h) (map quote wk ρ t)
| termArg t => termArg (map quote wk ρ t)
| teleArgNil => teleArgNil
| teleArgCons ts t => teleArgCons (map quote wk ρ ts) (map quote wk ρ t)
| termListNil  => termListNil
| termListCons h t  => termListCons (map quote wk ρ h) (map quote wk ρ t)
| termVecNil  => termVecNil
| termVecCons h t  => termVecCons (map quote wk ρ h) (map quote wk ρ t)
| ABT.bind t => bind (map quote wk (wk ρ ) t)


-- --nothing combined with list gives us a hacky way of encoding numbers
-- def emptyListToNat : ABT sig n (ABTArg.Arg (Sig.list Sig.empty)) → ℕ
-- | termListNil => 0
-- | termListCons _ t => Nat.succ (emptyListToNat t)

-- def emptyListFromNat : ℕ → ABT sig n (ABTArg.Arg (Sig.list Sig.empty))
-- | Nat.zero => termListNil
-- | (Nat.succ x) => termListCons nothing (emptyListFromNat x)

-- theorem toFromNat : ∀ (x : ABT sig n (ABTArg.Arg (Sig.list Sig.empty))),
--   emptyListFromNat (emptyListToNat x) = x
-- | termListNil => by simp [emptyListToNat, emptyListFromNat]
-- | termListCons h t => by
--   simp [emptyListToNat, emptyListFromNat]
--   cases h
--   simp
--   apply toFromNat


-- def emptyListEquiv : ABT sig n (ABTArg.Arg (Sig.list Sig.empty)) ≃ ℕ where
--   toFun := emptyListToNat
--   invFun := emptyListFromNat
--   right_inv x := by
--     induction x <;> simp [emptyListToNat, emptyListFromNat] <;> assumption
--   left_inv := toFromNat

-- Helpers for encoding, easier notation, etc
abbrev pair (s t : ABT sig n ABTArg.Term') : ABT sig n (ABTArg.Args [◾, ◾]) :=
  argsCons (termArg s) (argsCons (termArg t) argsNil)
abbrev singleton (s : ABT sig n ABTArg.Term') : ABT sig n (ABTArg.Args [◾]) :=
  argsCons (termArg s) argsNil
abbrev fromNat (x : ℕ) : ABT sig n (ABTArg.Args [Sig.numLit]) :=
  argsCons (numLit x) argsNil

end ABT
