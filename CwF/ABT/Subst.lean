
import Mathlib.Data.Fin.Fin2
import Mathlib.Logic.Unique
import Mathlib.CategoryTheory.Category.Basic
import CwF.ABT.ABT
import CwF.ABT.Renaming

universe u v'

namespace ABT

variable [signature : Signature]

abbrev Subst (m n : Nat) : Type u :=
  Fin2 n → Term m


namespace Subst
  def id : Subst n n := fun x => ABT.var x

  def ext (f : Subst m n) (t : Term m) : Subst m (Nat.succ n)
  | Fin2.fz => t
  | Fin2.fs x => f x

  def ofRenaming (ρ : Renaming m n) : Subst m n := fun x =>
    ABT.var (ρ x)

  abbrev proj : Subst (Nat.succ m) m  := ofRenaming Fin2.fs



  def wk (θ : Subst m n)  : Subst (Nat.succ m) (Nat.succ n)
  | Fin2.fz => ABT.var Fin2.fz
  | Fin2.fs x => Renaming.shift (θ x)

  def wkN (offset : ℕ) (θ : Subst m n) : Subst (m + offset) (n + offset) :=
    match offset with
    | Nat.zero => θ
    | Nat.succ offset => wk (wkN offset θ)

  -- Deleted this because Lean prints goals better if we have it purely as a notation
  abbrev subst (θ : Subst m n) : ABT n a →  ABT m a :=
    ABT.map (fun x => x) wk θ
end Subst

-- @[app_unexpander ABT.map]
-- def ABT.map.unexpander : Lean.PrettyPrinter.Unexpander
--   | `($_ fun $x:ident ↦ $p) => `({ $x:ident | $p })
--   | `($_ fun ($x:ident : $ty:term) ↦ $p) => `({ $x:ident : $ty:term | $p })
--   | _ => throw ()

notation:max t "⦇" θ "⦈" => Subst.subst θ t
-- ABT.map (fun {a} x => x) (fun {a} {b} => Subst.wk) θ t


namespace Subst
  def comp (θ : Subst a b) (θ' : Subst b c) : Subst a c := fun x =>
    (θ' x)⦇θ⦈


--A substitution is just a length-n vector of terms with m variables
--So we can internalize this into our ABT
--TODO avoid duplicate names?
-- abbrev Syntactic (sig : Op → List Sig) (m n : ℕ) := TermVec m n

end Subst

infixr:80  " ⨟ "  => Subst.comp


notation:max t "/[" s "/x]" => t⦇Subst.ext Subst.id s⦈

notation:max  "⟪" θ " ● " t "⟫" => Subst.ext θ t


-- Tactic for unrolling the recursion of subst one level
theorem subst_rewrite {t : ABT n tag} {θ : Subst m n}
  : map (fun {a} x => x) (fun {a b} => Subst.wk) θ t = t⦇θ⦈ := by simp [Subst.subst]

macro "unfold_subst" : tactic => `(tactic| (unfold Subst.subst ; try simp [subst_rewrite]))
macro "unfold_subst_at" hyp:Lean.Parser.Tactic.locationHyp : tactic => `(tactic| (unfold Subst.subst at $hyp ; try simp [subst_rewrite] at $hyp))
macro "unfold_subst_all"  : tactic => `(tactic| (unfold Subst.subst at * ; try simp [subst_rewrite] at *))



namespace Subst


abbrev projN (offset : ℕ) : Subst (m + offset) m :=
  match offset with
  | Nat.zero => Subst.id
  | Nat.succ offset => proj ⨟ projN offset

-- Syntactic substitutions are equivalent to substitutions as functions
def syntacticEquiv : TermVec m n ≃ Subst m n where
    toFun θ i :=
      match abtVecLookup θ i with
      | ABT.termArg t => t
    invFun f := ABT.termVec (fun i => ABT.termArg (f i))
    left_inv θ := by
      cases θ with
      | termVec f =>
        simp
        funext i
        generalize eq :  abtVecLookup (ABT.termVec f) i = x
        cases x
        simp
        simp [abtVecLookup] at eq
        apply eq.symm
    right_inv f := by
      funext i
      simp

-- Composition of syntactic substitutions is just applying one substitution to the other
theorem syntacticSubComp {θ1 : Subst a b} {θ2 : TermVec b c}
  : θ1 ⨟ (syntacticEquiv θ2) = syntacticEquiv (θ2⦇θ1⦈) := by
  funext i
  let (ABT.termVec f) := θ2
  unfold_subst
  simp [syntacticEquiv, Subst.comp, abtVecLookup]
  unfold_subst
  generalize eq : f i = fi
  cases fi
  unfold_subst
end Subst

end ABT
