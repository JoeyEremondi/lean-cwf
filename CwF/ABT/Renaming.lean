

import Mathlib.Data.Fin.Fin2
import Mathlib.Logic.Unique
import Mathlib.CategoryTheory.Category.Basic


import CwF.ABT.Defs
import CwF.Util


universe u v'

namespace ABT

def Renaming (m n : Nat) : Type :=
  Fin2 n → Fin2 m

namespace Renaming

  def id : Renaming n n := fun x => x

  def wk (θ : Renaming m n) : Renaming (Nat.succ m) (Nat.succ n)
  | Fin2.fz => Fin2.fz
  | Fin2.fs x => Fin2.fs (θ x)


  def rename (θ : Renaming m n) : ABT sig n a →  ABT sig m a
  | ABT.var x => ABT.var (θ x)
  | ABT.op op args => ABT.op op (rename θ args)
  | ABT.nil => ABT.nil
  | ABT.cons h t => ABT.cons (rename θ h) (rename θ t)
  | ABT.plain t => ABT.plain (rename θ t)
  | ABT.bind t => ABT.bind (rename (wk θ ) t)

  def shift  (t : ABT sig m ty) : ABT sig (Nat.succ m) ty :=
    rename Fin2.fs t
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
  theorem rename_id {t : ABT sig n a} : t⦇id⦈ᵣ = t := by
    induction t <;> simp [rename, id] <;> try aesop_cat

  @[simp]
  theorem rename_comp {t : ABT sig c tag} : ∀ {a} {b} {ρ1 : Renaming a b} {ρ2 : Renaming b c} ,  t⦇ρ2⦈ᵣ⦇ρ1⦈ᵣ = t⦇ρ1 ∘ ρ2⦈ᵣ := by
    induction t <;> intros a b ρ1 ρ2 <;> simp [rename, wk_comp] <;> try aesop_cat



  @[simp]
  theorem weaken_wk {t : ABT sig n tag} : ∀ {ρ : Renaming m n }, (shift t)⦇Renaming.wk ρ⦈ᵣ = shift t⦇ρ⦈ᵣ := by
   induction t <;> intros ρ  <;> simp [shift] <;> aesop_cat


end Renaming

end ABT
