
import Mathlib.Data.Fin.Fin2
import Mathlib.Data.Vector3
import Mathlib.Logic.Unique
import Mathlib.CategoryTheory.Category.Basic

import Lean.Elab.Deriving.DecEq

universe u v'

namespace Vector3
def toFun {A : Type u} (v : Vector3 A n) : (Fin2 n → A) := by
  simp [Vector3] at v
  apply v

end Vector3

-- Loosely based off of Jeremy Siek's agda ABTs

inductive Sig : Type where
| plain : Sig
| depVec : (len : ℕ) → (Fin2 len → Sig) → Sig
| list : Sig → Sig
| bind : Sig → Sig
| nClosed : ℕ → Sig → Sig
-- | lhsRhs : Sig → Sig →Sig
| numLit : Sig
-- | empty : Sig
--
class Signature : Type (u + 1) where
  Op : Type u
  -- [dec : DecidableEq Op]
  sig : Op → List Sig
open Signature

notation "◾" => Sig.plain
notation "ν" x => Sig.bind x

namespace ABT

inductive ABTArg : Type where
  | Term' : ABTArg
  | Args : (List Sig) → ABTArg
  | Arg : Sig → ABTArg
  -- | Vec : ℕ → ABTArg
  -- | List : ABTArg

variable [Signature]

section
    open ABTArg

    --TODO move this elsewhere




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
    -- to have the same length.
    -- We allow the signature to depend on the index of the vector
    | termVec : ((i : Fin2 len) → ABT n (Arg (ss i)))
      → ABT n (Arg (Sig.depVec _ ss))
    | bind : ABT (Nat.succ n) (Arg s) → ABT n (Arg (ν s))
    -- nClosed is a "top level" binding with n parameters. Substitutions do not
    -- propagate into nClosed. The only way to substitute in them is to
    -- explicitly decompose them.
    -- This models e.g. branches of a top-level pattern match
    | nClosed : ABT (num) (Arg s) → ABT n (Arg (Sig.nClosed num s))



  abbrev abtVecLookup {tags : Fin2 len → Sig} :
    ABT n (Arg (Sig.depVec _ tags))
    → (i : Fin2 len)
    → ABT n (Arg (tags i)) := by
    intros v i
    cases v
    aesop

  abbrev abtVecExt {tags : Fin2 len → Sig}
    (ts1 ts2 : ABT n (Arg (Sig.depVec _ tags)))
    (eq : ∀ i, abtVecLookup ts1 i = abtVecLookup ts2 i)
      : ts1 = ts2 := by
    cases ts1
    cases ts2
    apply congrArg ABT.termVec
    funext i
    apply eq

open ABT

def vecEquiv {ss : Fin2 len → Sig} :
  ABT n (ABTArg.Arg (Sig.depVec _ ss))
  ≃ ((i : Fin2 len) → ABT n (ABTArg.Arg (ss i))) where
  toFun ts := by
    cases ts
    assumption
  invFun := ABT.termVec
  left_inv f := by
    cases f
    rfl
  right_inv f := by rfl



abbrev Term (n : ℕ) := ABT n ABTArg.Term'

abbrev x0 : Term (Nat.succ n) := ABT.var Fin2.fz

notation "◾vec" n => (Sig.depVec (len := n) (fun _ => ◾))

def depVecNil : ABT n (ABTArg.Arg (Sig.depVec (len := 0) ss)) := by
  apply termVec ; intros ; contradiction

abbrev TermVec  (n len : ℕ) := ABT n (ABTArg.Arg (◾vec len))

def vecNil : TermVec n 0 := depVecNil

@[irreducible]
def vecCons (h : Term n) : (ts : TermVec n len) → TermVec n (Nat.succ len)
| termVec ts => termVec (Fin2.cases' (termArg h) ts)

def vecConcat  (v1 : TermVec n a) (v2 : TermVec n b) : TermVec n (a + b) := by
  let f1 := vecEquiv.toFun v1
  let f2 := vecEquiv.toFun v2
  rw [Nat.add_comm]
  apply vecEquiv.invFun (Vector3.append (Vector3.ofFn f1) (Vector3.ofFn f2))


abbrev nBinds : (i : ℕ) → Sig → Sig
| Nat.zero, s => s
| Nat.succ n, s => Sig.bind (nBinds n s)
notation "◾tele" n => (Sig.depVec (len := n) (fun i => nBinds (Fin2.toNat i) ◾))

abbrev bindN : (i : ℕ) → ABT (n + i) (ABTArg.Arg s) → ABT n (ABTArg.Arg (nBinds i s))
| Nat.zero, t => t
| Nat.succ i, t => ABT.bind (bindN i (by
        rw [Nat.add_succ] at t
        rw [Nat.succ_add]
        apply t
  ))

def TermTele (n len : ℕ) := ABT n (ABTArg.Arg (◾tele len))

def teleNil : TermTele n 0 := depVecNil

@[irreducible]
def teleCons (h : Term n) (ts : TermTele (Nat.succ n) len)
  :  TermTele n (Nat.succ len) :=
  termVec (Fin2.cases' (termArg h) (fun i => ABT.bind (vecEquiv.toFun ts i)))


def teleHead (ts : TermTele n (Nat.succ len)) : Term n := by
  cases abtVecLookup ts Fin2.fz
  assumption

def teleTail (ts : TermTele n (Nat.succ len)) : TermTele (Nat.succ n) len := by
  apply termVec
  intros i
  cases abtVecLookup ts (Fin2.fs i)
  assumption

def teleSnoc (ts : TermTele n len) (t : Term (n + len)) : TermTele n (Nat.succ len) :=
  match len with
  | Nat.zero => teleCons t teleNil
  | Nat.succ len => by
    apply teleCons (teleHead ts) (teleSnoc (teleTail ts) _)
    simp [Nat.succ_add]
    simp [Nat.add_succ] at t
    apply t

@[simp]
def teleConsHead : teleHead (teleCons h t) = h := by
  unfold teleCons
  simp [teleCons]
  cases (abtVecLookup (teleCons h t) Fin2.fz)
  rfl



def teleConcat {len1 : ℕ} :
  ∀ {n} (ts1 : TermTele n len1) (ts2 : TermTele (n + len1) len2), TermTele n (len1 + len2) := by
  induction len1 with intros n ts1 ts2
  | zero => simp ; apply ts2
  | succ len1 IH =>
    simp [Nat.succ_add]
    apply teleCons (teleHead ts1)
    apply IH (teleTail ts1)
    simp [Nat.add_succ] at ts2
    simp [Nat.succ_add]
    apply ts2



def nClosedEquiv : ABT n (ABTArg.Arg (Sig.nClosed m s)) ≃ ABT m (ABTArg.Arg s) where
  toFun x := by
    cases x
    assumption
  invFun := ABT.nClosed
  left_inv x := by
    cases x
    rfl
  right_inv x := by rfl

notation "[[]]" => depVecNil
notation "[[x∷ " T ",, " Ts "]]" => teleCons T Ts
infixr:80 "∷v" => vecCons

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
  (quote : ∀ {a}, V a → Term a )
  (wk : ∀ {a} {b}, (Fin2 a → V b) → Fin2 (Nat.succ a) → V (Nat.succ b))
  (ρ : Fin2 n → V m) :
  ( ABT n tag) → ABT m tag
| numLit x => numLit x
| var x => (quote (ρ x))
| op o args => op o (map quote wk ρ args)
| argsNil => argsNil
| argsCons h t => argsCons (map quote wk ρ h) (map quote wk ρ t)
-- | argLhsRhs lhs rhs => argLhsRhs (map quote wk ρ lhs) (map quote wk ρ rhs)
| termArg t => termArg (map quote wk ρ t)
| termListNil  => termListNil
| termListCons h t  => termListCons (map quote wk ρ h) (map quote wk ρ t)
| termVec f  => termVec (fun x => map quote wk ρ (f x) )
| ABT.bind t => bind (map quote wk (wk ρ ) t)
| ABT.nClosed t => ABT.nClosed t


-- --nothing combined with list gives us a hacky way of encoding numbers
-- def emptyListToNat : ABT n (ABTArg.Arg (Sig.list Sig.empty)) → ℕ
-- | termListNil => 0
-- | termListCons _ t => Nat.succ (emptyListToNat t)

-- def emptyListFromNat : ℕ → ABT n (ABTArg.Arg (Sig.list Sig.empty))
-- | Nat.zero => termListNil
-- | (Nat.succ x) => termListCons nothing (emptyListFromNat x)

-- theorem toFromNat : ∀ (x : ABT n (ABTArg.Arg (Sig.list Sig.empty))),
--   emptyListFromNat (emptyListToNat x) = x
-- | termListNil => by simp [emptyListToNat, emptyListFromNat]
-- | termListCons h t => by
--   simp [emptyListToNat, emptyListFromNat]
--   cases h
--   simp
--   apply toFromNat


-- def emptyListEquiv : ABT n (ABTArg.Arg (Sig.list Sig.empty)) ≃ ℕ where
--   toFun := emptyListToNat
--   invFun := emptyListFromNat
--   right_inv x := by
--     induction x <;> simp [emptyListToNat, emptyListFromNat] <;> assumption
--   left_inv := toFromNat

-- Helpers for encoding, easier notation, etc
notation "ABTpair" s "," t =>
  argsCons (termArg s) (argsCons (termArg t) argsNil)
notation "ABTsingleton" s =>
  argsCons (termArg s) argsNil
notation "ABTfromNat" x =>
  argsCons (numLit x) argsNil

