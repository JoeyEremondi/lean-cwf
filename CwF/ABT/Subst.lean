
import Mathlib.Data.Fin.Fin2
import Mathlib.Logic.Unique
import Mathlib.CategoryTheory.Category.Basic
import CwF.ABT.Defs
import CwF.ABT.Renaming

universe u v'

namespace ABT

abbrev Subst {Op : Type u} (sig : Op → List Sig) (m n : Nat) : Type u :=
  Fin2 n → Term sig m


namespace Subst
  def id : Subst sig n n := fun x => ABT.var x

  def ext (f : Subst sig m n) (t : Term sig m) : Subst sig m (Nat.succ n)
  | Fin2.fz => t
  | Fin2.fs x => f x

  def ofRenaming (ρ : Renaming m n) : Subst sig m n := fun x =>
    ABT.var (ρ x)

  abbrev proj : Subst sig (Nat.succ m) m  := ofRenaming Fin2.fs

  def wk (θ : Subst sig m n)  : Subst sig (Nat.succ m) (Nat.succ n)
  | Fin2.fz => ABT.var Fin2.fz
  | Fin2.fs x => Renaming.shift (θ x)

  -- Deleted this because Lean prints goals better if we have it purely as a notation
  abbrev subst (θ : Subst sig m n) : ABT sig n a →  ABT sig m a :=
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
  def comp (θ : Subst sig a b) (θ' : Subst sig b c) : Subst sig a c := fun x =>
    (θ' x)⦇θ⦈


--A substitution is just a length-n vector of terms with m variables
--So we can internalize this into our ABT
abbrev Syntactic (sig : Op → List Sig) (m n : ℕ) := ABT sig m (ABTArg.Arg (◾vec n))

end Subst

infixr:80  " ⨟ "  => Subst.comp


notation:max t "/[" s "/x]" => t⦇Subst.ext Subst.id s⦈

notation:max  "⟪" θ " ● " t "⟫" => Subst.ext θ t


-- Tactic for unrolling the recursion of subst one level
theorem subst_rewrite {t : ABT sig n tag} {θ : Subst sig m n}
  : map (fun {a} x => x) (fun {a b} => Subst.wk) θ t = t⦇θ⦈ := by simp

macro "unfold_subst" : tactic => `(tactic| (unfold Subst.subst ; try simp [subst_rewrite]))
macro "unfold_subst_at" hyp:Lean.Parser.Tactic.locationHyp : tactic => `(tactic| (unfold Subst.subst at $hyp ; try simp [subst_rewrite] at $hyp))




-- Syntactic substitutions are equivalent to substitutions as functions
def syntacticEquiv : Subst.Syntactic sig m n ≃ Subst sig m n where
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
theorem syntaxSubComp {θ1 : Subst sig a b} {θ2 : Subst.Syntactic sig b c}
  : θ1 ⨟ (syntacticEquiv.toFun θ2) = syntacticEquiv.toFun (θ2⦇θ1⦈) := by
  funext i
  let (ABT.termVec f) := θ2
  unfold_subst
  simp [syntacticEquiv, Subst.comp, abtVecLookup]
  generalize eq : f i = fi
  cases fi
  simp


end ABT
