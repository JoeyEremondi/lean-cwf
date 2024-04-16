

import CwF.ABT.Defs
import CwF.ABT.Subst
import CwF.ABT.SubstProperties
import CwF.MLTT.Sig

namespace MLTT
open ABT


inductive Reduces : (s t : Term n) → Type where
| Reducesβ : Reduces ((λx∷ T ,, t) $ s) s
| Reducesπ1 : Reduces (π₁ ⟨s ,, t⟩ ) s
| Reducesπ2 : Reduces (π₂ ⟨s ,, t⟩ ) t

theorem substPreserveRed {s t : Term n}
  (eq : Reduces s t) : ∀ (θ : Subst sig m n), Reduces s⦇θ⦈ t⦇θ⦈ := by
  intros θ
  cases eq <;> simp [Subst.subst] <;> fconstructor

inductive DefEq : (s t : Term n) → Prop where
| InContext  : {s t : Term n} → {C : Term (Nat.succ n)}
  → Reduces s t → DefEq (C[s /x]) (C[ t /x])
| Refl : DefEq s s
| Symm : DefEq s t → DefEq t s
| Trans : DefEq s t → DefEq t u → DefEq s u

attribute [simp] DefEq.Refl

@[simp]
theorem subst_rewrite {t : Term n} {θ : Subst sig m n}
  : map (fun {a} x => x) (fun {a b} => Subst.wk) θ t = t⦇θ⦈ := by simp


@[simp]
theorem ren_rewrite {m n : ℕ} {t : Term n} {ρ : Renaming m n}
  : map (fun {a} x => ABT.var x) (fun {a b} => Renaming.wk) ρ t = t⦇ρ⦈ᵣ := by simp [Renaming.rename]

namespace DefEq

  @[aesop unsafe 90% apply]
  theorem substPreserve {s t : Term n}   (eq : DefEq s t)
    : ∀  (θ : Subst sig m n), DefEq s⦇θ⦈ t⦇θ⦈ := by
    induction eq with intros θ <;> try (fconstructor <;> aesop_cat)
    | @InContext s t C red =>
          simp
          let θeq := substPreserveRed red θ
          let ret := DefEq.InContext (s := s⦇θ⦈) (t := t⦇θ⦈) (C := C⦇Subst.wk θ⦈) θeq
          simp [Subst.wk_def] at ret
          apply ret
    | Trans _ _  IH1 IH2 =>
      apply DefEq.Trans <;> aesop_cat

end DefEq

infix:10 "≡" => DefEq

instance Termoid {n : ℕ} : Setoid  (Term n) where
  r := DefEq
  iseqv := by
    fconstructor <;> intros
    . apply DefEq.Refl
    . apply DefEq.Symm
      assumption
    . apply DefEq.Trans <;> assumption

-- Values are equivalence classes of the transitive-symmetric closure of reduction
def Value (n : ℕ) : Type := Quotient (Termoid (n := n))

namespace Value
  def subst (θ : Subst sig m n) : Value n → Value m :=
    Quotient.lift (fun (t : Term n) => Quotient.mk Termoid (Subst.subst θ t) )
    (by
       intros a b rel
       simp
       apply Quotient.sound
       apply DefEq.substPreserve rel
    )

end Value
