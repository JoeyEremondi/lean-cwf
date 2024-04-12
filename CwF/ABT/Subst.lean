
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

  def proj : Subst sig (Nat.succ m) m  := ofRenaming Fin2.fs

  def wk (θ : Subst sig m n)  : Subst sig (Nat.succ m) (Nat.succ n)
  | Fin2.fz => ABT.var Fin2.fz
  | Fin2.fs x => Renaming.shift (θ x)


  abbrev subst (θ : Subst sig m n) : ABT sig n a →  ABT sig m a :=
    ABT.map (fun x => x) wk θ


  def comp (θ : Subst sig a b) (θ' : Subst sig b c) : Subst sig a c := fun x =>
    subst θ (θ' x)


end Subst

infixr:80  "⨟"  => Subst.comp

notation:max t "⦇" θ "⦈" => Subst.subst θ t

end ABT
