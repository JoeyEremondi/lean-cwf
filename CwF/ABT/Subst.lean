
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

end Subst

infixr:80  " ⨟ "  => Subst.comp


notation:max t "/[" s "/x]" => t⦇Subst.ext Subst.id s⦈

notation:max  "⟪" θ " ● " t "⟫" => Subst.ext θ t





end ABT
