

import Mathlib.Data.Fin.Fin2
import Mathlib.Logic.Unique
import Mathlib.CategoryTheory.Category.Basic
import Init.Tactics

import CwF.ABT.ABT
import CwF.Util


universe u v'

namespace ABT
variable [Signature]

def Renaming (m n : Nat) : Type :=
  Fin2 n → Fin2 m

namespace Renaming

  def id : Renaming n n := fun x => x

  def wk (θ : Renaming m n) : Renaming (Nat.succ m) (Nat.succ n)
  | Fin2.fz => Fin2.fz
  | Fin2.fs x => Fin2.fs (θ x)


  def rename (ρ : Renaming m n) : ABT n a →  ABT m a := ABT.map ABT.var wk ρ

  def shift  (t : ABT m ty) : ABT (Nat.succ m) ty :=
    rename Fin2.fs t

  -- 0 is the initial context, so we can rename things with 0 variables to anything
  def fromClosed : Renaming m 0 := by
    intros x ; contradiction

end Renaming

notation:max t "⦇" ρ "⦈ᵣ" => Renaming.rename ρ t

namespace Renaming


  theorem id_def {n : ℕ} : (fun x => x) = id (n := n) := by
    unfold id
    rfl

  @[simp]
  theorem wk_id : wk (n := n) id = id := by
    funext x
    simp only [wk, id, shift]
    cases x <;> try aesop_cat


  @[simp]
  theorem wk_comp {ρ1 : Renaming a b} {ρ2 : Renaming b c} : wk ρ1 ∘ wk ρ2 = wk (ρ1 ∘ ρ2) := by
    funext x
    cases x <;> try aesop_cat



  @[simp]
  theorem rename_id {t : ABT n a} : t⦇id⦈ᵣ = t := by
    induction t <;> simp [rename, id] <;> try aesop_cat

  @[simp]
  theorem rename_comp {t : ABT c tag} : ∀ {a} {b} {ρ1 : Renaming a b} {ρ2 : Renaming b c} ,  t⦇ρ2⦈ᵣ⦇ρ1⦈ᵣ = t⦇ρ1 ∘ ρ2⦈ᵣ := by
    induction t <;> intros a b ρ1 ρ2 <;> simp_all [rename, ABT.map, wk_comp]


  @[simp]
  theorem weaken_wk {t : ABT n tag} : ∀ {ρ : Renaming m n }, (shift t)⦇Renaming.wk ρ⦈ᵣ = shift t⦇ρ⦈ᵣ := by
   induction t <;> intros ρ  <;> simp [shift] <;> aesop_cat

  -- Macro for unrolling the recursion one level
  theorem ren_rewrite {m n : ℕ} {t : ABT n tag} {ρ : Renaming m n}
    : map (fun {a} x => ABT.var x) (fun {a b} => Renaming.wk) ρ t = t⦇ρ⦈ᵣ := by simp [Renaming.rename]
  macro "unfold_rename" : tactic => `(tactic| (unfold Renaming.rename ; try simp [ren_rewrite]))
  macro "unfold_rename_at" hyp:Lean.Parser.Tactic.locationHyp : tactic => `(tactic| (unfold Renaming.rename at $hyp ; try simp [ren_rewrite] at $hyp))
  macro "unfold_rename_all"  : tactic => `(tactic| (unfold Renaming.rename at * ; try simp [ren_rewrite] at *))



  --Renamings have no effect on closed terms, so they're all equivalent to "introduce unused vars"
  @[simp]
  theorem fromClosedRen {ρ0 : Renaming m 0} : ρ0 =  Renaming.fromClosed := by
    funext i ; contradiction


end Renaming

end ABT
