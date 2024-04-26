

import CwF.ABT.ABT
import CwF.ABT.Subst
import CwF.ABT.SubstProperties
import CwF.MLTT.Sig
import Mathlib.Data.Vector3

namespace MLTT
open ABT

variable  [Ind] [Arities]

class inductive Reduces : (s : Term n) → (t : outParam (Term n)) → Prop where
| Reducesβ : Reduces ((λx∷ T ,, t) s) t /[ s /x]
| ReducesMatch
  {θmatch : Subst n (xs i).fst}
  : Reduces (casesplit (lhss i)⦇θmatch⦈ ∷ Ts to T [[xs ,, lhss ↦ rhss]]) (rhss i)⦇θmatch⦈
  deriving Decidable

--Useful tool for proving properties about reuductions
lemma reduces_eq {s t t' : Term n} [Reduces s t] (eq : t = t')
  : Reduces s t' := by simp [<- eq] ; assumption

attribute [instance] Reduces.Reducesβ


theorem substPreserveRed {s t : Term n}
  (red : Reduces s t) : ∀ (θ : Subst m n), Reduces s⦇θ⦈ t⦇θ⦈ := by
  intros θ
  cases red <;>
    (try  unfold_subst
    <;> (try simp [Subst.wk_def])
    <;>  (try constructor ; done)
    <;> (try apply reduces_eq <;> aesop_cat)
    <;> done)



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


class inductive DefEq : ∀ {n : ℕ} {tag : ABTArg}, (s t : ABT.ABT n tag) → Prop where
| ApplyRed  : {s t : Term n} → Reduces s t → DefEq s t
-- | InContext  : (s t : Term n) → (C : ABT (Nat.succ n) tag)
--   → DefEq s t →  DefEq (C/[s /x]) (C/[ t /x])
| CongrHead : {ss ts : ABT.ABT n (ABTArg.Args (sig h))}
  → DefEq ss ts → DefEq (ABT.op h ss) (ABT.op h ts)
| CongrCons : ∀ {n : ℕ} {tag : Sig} {as : List Sig},
  {s t : ABT.ABT n (ABTArg.Arg tag)}
  → {ss ts : ABT.ABT n (ABTArg.Args as)}
  → DefEq (n := n) s t → DefEq (n := n) ss ts → DefEq (ABT.argsCons (h := tag) (t := as) s ss) (ABT.argsCons t ts)
| CongrBind : DefEq s t →  DefEq (ABT.bind s) (ABT.bind t)
| CongrTerm : DefEq s t →  DefEq (ABT.termArg s) (ABT.termArg t)
| CongrVec : (∀ {i}, DefEq (f i) (g i)) →  DefEq (ABT.termVec f) (ABT.termVec g)
| Refl : DefEq s s
| Symm : {s t : Term n} → DefEq s t → DefEq t s
| Trans : {s t : Term n} → DefEq s t → DefEq t u → DefEq s u


infix:10 " ≡ " => DefEq

-- Instances to automate deducing definitional equality
-- When terms have the same head, we try reducing the parts in parallel
instance instCongrHead {ss ts : ABT.ABT n (ABTArg.Args (sig h))} [eq : ss ≡ ts]
  : (ABT.op h ss) ≡ (ABT.op h ts) := by
    apply DefEq.CongrHead <;> assumption
instance  instContrCons [eq : DefEq s t ] [eqs : DefEq ss ts]
  : DefEq (ABT.argsCons s ss) (ABT.argsCons t ts) := by
    apply DefEq.CongrCons <;> assumption
instance instCongrBind [eq : DefEq s t] :  DefEq (ABT.bind s) (ABT.bind t) := by
  constructor ; assumption
instance instCongrTerm [eq : DefEq s t] :  DefEq (ABT.termArg s) (ABT.termArg t) := by
  constructor ; assumption

-- @[default_instance]
-- instance byEq {s t : ABT n tag} [eq : Fact (s = t)] : s ≡ t := by
--   simp [eq.out]
--   apply DefEq.Refl

attribute [instance, simp] DefEq.Refl
attribute [simp] DefEq.CongrHead
attribute [simp] DefEq.CongrCons
attribute [simp] DefEq.CongrBind
attribute [simp] DefEq.CongrTerm





instance stepLeft {n : ℕ} {s s' t : Term n} [Reduces s s'] [DefEq s' t] : DefEq s t := by
  apply DefEq.Trans
  . apply DefEq.ApplyRed
    assumption
  . assumption

instance stepRight {n : ℕ} {s t' t : Term n} [Reduces t t'] [DefEq s t'] : DefEq s t := by
  apply DefEq.Trans
  . assumption
  . apply DefEq.Symm
    apply DefEq.ApplyRed
    assumption


namespace DefEq
theorem substPreserve {s t : ABT n tag}   (eq : DefEq s t)
    : ∀  {m : ℕ} (θ : Subst m n), DefEq s⦇θ⦈ t⦇θ⦈ := by
    induction eq with intros m θ
      <;> (try (unfold Subst.subst) <;> simp)
      <;> try (constructor <;> aesop_cat)
    | Trans _ _  IH1 IH2 =>
      apply DefEq.Trans <;> aesop_cat
    | ApplyRed red => constructor ; apply substPreserveRed red θ
    | Symm eq IH =>
      apply DefEq.Symm
      apply IH
end DefEq
