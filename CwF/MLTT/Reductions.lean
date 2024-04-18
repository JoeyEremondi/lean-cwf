

import CwF.ABT.Defs
import CwF.ABT.Subst
import CwF.ABT.SubstProperties
import CwF.MLTT.Sig

namespace MLTT
open ABT


inductive Reduces : (s t : Term n) → Prop where
| Reducesβ : Reduces ((λx∷ T ,, t) $ s) s
| Reducesπ1 : Reduces (π₁ ⟨x↦ s ,, t ∷x,, T ⟩ ) s
| Reducesπ2 : Reduces (π₂ ⟨x↦ s ,, t ∷x,, T ⟩ ) t

theorem substPreserveRed {s t : Term n}
  (red : Reduces s t) : ∀ (θ : Subst sig m n), Reduces s⦇θ⦈ t⦇θ⦈ := by
  intros θ
  cases red <;> simp [Subst.subst] <;> fconstructor

-- instance {n : ℕ} {t : Term n} : Decidable (∃x, Reduces t x) := by
--   cases t with
--   | var x =>
--       apply isFalse
--       intros s
--       cases s
--       contradiction
--   | op h args =>
--     cases h with
--       try (rcases args <;> (try apply isFalse <;> intros s <;> cases s <;> contradiction ) <;> done)
--     | App =>
--       simp [sig] at args
--       rcases args
--       rename_i t
--       rename_i f
--       cases f <;> (try apply isFalse <;> intros s <;> cases s <;> contradiction )
--       apply isTrue
--     | Proj₁ => simp
--     | Proj₂ => simp


inductive DefEq : (s t : Term n) → Prop where
| ApplyRed  : Reduces s t → DefEq s t
| InContext  : {s t : Term n} → {C : Term (Nat.succ n)}
  → DefEq s t → DefEq (C/[s /x]) (C/[ t /x])
| Refl : DefEq s s
| Symm : DefEq s t → DefEq t s
| Trans : DefEq s t → DefEq t u → DefEq s u

attribute [simp] DefEq.Refl

@[simp]
theorem subst_rewrite {t : ABT sig n tag} {θ : Subst sig m n}
  : map (fun {a} x => x) (fun {a b} => Subst.wk) θ t = t⦇θ⦈ := by simp


@[simp]
theorem ren_rewrite {m n : ℕ} {t : Term n} {ρ : Renaming m n}
  : map (fun {a} x => ABT.var x) (fun {a b} => Renaming.wk) ρ t = t⦇ρ⦈ᵣ := by simp [Renaming.rename]

namespace DefEq

  @[aesop unsafe 90% apply]
  theorem substPreserve {s t : Term n}   (eq : DefEq s t)
    : ∀  (θ : Subst sig m n), DefEq s⦇θ⦈ t⦇θ⦈ := by
    induction eq with intros θ <;> try (constructor <;> aesop_cat)
    | Refl => apply Refl
    | Symm x IH => apply Symm <;> aesop_cat
    | @InContext s' t' C eq IH =>
      let ic := @InContext _ s'⦇θ⦈ t'⦇θ⦈ (C⦇Subst.wk θ⦈) (IH θ)
      simp [Subst.singleSubSub, Subst.wk_def] at ic
      simp
      apply ic
    | Trans _ _  IH1 IH2 =>
      apply DefEq.Trans <;> aesop_cat
    | ApplyRed red => constructor ; apply substPreserveRed red θ

end DefEq

infix:10 "≡" => DefEq

