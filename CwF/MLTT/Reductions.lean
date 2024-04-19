

import CwF.ABT.Defs
import CwF.ABT.Subst
import CwF.ABT.SubstProperties
import CwF.MLTT.Sig

namespace MLTT
open ABT


class inductive Reduces : (s : Term n) → (t : outParam (Term n)) → Prop where
| Reducesβ : Reduces ((λx∷ T ,, t) $ s) s
| Reducesπ1 : Reduces (π₁ ⟨x↦ s ,, t ∷x,, T ⟩ ) s
| Reducesπ2 : Reduces (π₂ ⟨x↦ s ,, t ∷x,, T ⟩ ) t
  deriving Decidable

attribute [instance] Reduces.Reducesβ Reduces.Reducesπ1 Reduces.Reducesπ2


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


class inductive DefEq : (s t : ABT.ABT sig n tag) → Prop where
| ApplyRed  : {s t : Term n} → Reduces s t → DefEq s t
| InContext  : (s t : Term n) → (C : ABT sig (Nat.succ n) tag)
  → DefEq s t →  DefEq (C/[s /x]) (C/[ t /x])
| Refl : {s : ABT sig n tag} → DefEq s s
| Symm : {s t : Term n} → DefEq s t → DefEq t s
| Trans : {s t : Term n} → DefEq s t → DefEq t u → DefEq s u



infix:10 "≡" => DefEq

theorem gen_trans_helper {a b c : ABT sig n tag}
  (s t : Term n)   (C : ABT sig (Nat.succ n) tag)
  (eq1 : DefEq s t)
  (ford : C/[t /x] = b)
  (eq2 : (b ≡ c))
  : (C/[s /x]) ≡ c := by
    let eq1' := DefEq.InContext s t C eq1
    let eq2' := eq2
    cases eq2 with
    | ApplyRed => simp [<- ford] at eq2' ;  apply DefEq.Trans eq1' eq2'
    | Symm s => simp [<- ford] at eq2' ; apply DefEq.Trans eq1' eq2'
    | Trans _ _ => simp [<- ford] at eq2' ; apply DefEq.Trans eq1' eq2'
    | Refl =>
      simp [<- ford]
      apply DefEq.InContext s t C
      assumption
    | InContext s' t' C' eq' =>
      -- Terrible abuse of syntax, is this a mistake TODO
      let θ1 : Subst sig (Nat.succ n) (Nat.succ n) :=
        Subst.ext (Subst.proj) (π₁ x0)
      let θ2 : Subst sig (Nat.succ n) (Nat.succ n) :=
        Subst.ext (Subst.proj) (π₂ x0)
      let st1 := (s)

theorem gen_trans {a b c : ABT sig n tag}
  (eq1 : a ≡ b) (eq2 : b ≡ c)
  : a ≡ c := by
    let eq1' := eq1
    let eq2' := eq2
    cases eq1 with
    | ApplyRed => apply DefEq.Trans eq1' eq2
    | Symm s => apply DefEq.Trans eq1' eq2
    | Trans _ _ => apply DefEq.Trans eq1' eq2
    | Refl => assumption
    | InContext s1 t1 C1 ctxEq2 =>
      cases eq2 
        | ApplyRed => apply DefEq.Trans eq1' eq2'
        | Symm s => apply DefEq.Trans eq1' eq2'
        | Trans _ _ => apply DefEq.Trans eq1' eq2'
        | Refl => assumption
        | InContext s2 t2 C2 ctxEq2 =>
            simp


--Helpers to aid with the typeclass search
class inductive DefEqArg

attribute [instance] DefEq.Refl


--TODO dangerous?
@[simp]
theorem subst_rewrite {t : ABT sig n tag} {θ : Subst sig m n}
  : map (fun {a} x => x) (fun {a b} => Subst.wk) θ t = t⦇θ⦈ := by simp


@[simp]
theorem ren_rewrite {m n : ℕ} {t : Term n} {ρ : Renaming m n}
  : map (fun {a} x => ABT.var x) (fun {a b} => Renaming.wk) ρ t = t⦇ρ⦈ᵣ := by simp [Renaming.rename]

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

 lemma tagCast {t : ABT sig n tag1} {eq : tag1 = tag2} {θ : Subst sig m n}
   : ((cast (by simp [eq]) t) : ABT sig n tag2)⦇θ⦈ = (cast (by simp [eq]) (t⦇θ⦈)) := by aesop

 theorem stepCtxHelper
   (as : List Sig)
   {h : Head}
   (args1 args2 : ABT sig n (ABTArg.Args as))
   [argEq : DefEq args1 args2]
   (eq : as = sig h)
  : DefEq (ABT.op h (cast (by simp [eq] ; rfl ) args1)) (ABT.op h (cast (by simp [eq]) args2)) := by
    . cases argEq with
      | InContext s t C deq =>
        let C' : Term (Nat.succ n) :=
          ABT.op h (cast (by simp [eq]) C )
        let ret := DefEq.InContext s t C' (by assumption)
        unfold Subst.subst at ret
        simp at ret
        rw [tagCast] at ret <;> try aesop_cat
        rw [tagCast] at ret <;> try aesop_cat
        apply ret
      | Refl =>  apply DefEq.Refl


 instance stepCtx
   {h : Head}
   {args1 args2 : ABT sig n (ABTArg.Args (sig h))}
   [argEq : DefEq args1 args2]
  : DefEq (ABT.op h args1) (ABT.op h (args2)) := by
    let ret := stepCtxHelper (as := sig h) args1 args2 (by rfl)
    simp at ret
    apply ret

 lemma argsConsEqHelper
   (args1 args2 : ABT sig n (ABTArg.Args as))
   (arg : ABT sig n (ABTArg.Arg tag))
   [argsEq : DefEq args1 args2]
   : DefEq (tag := ABTArg.Args (tag :: as))
     (ABT.argsCons arg args1) (ABT.argsCons arg args2) := by
     cases argsEq with
     | InContext ss ts Cs st =>
       let C' : ABT sig (Nat.succ n) (ABTArg.Args (tag :: as))
         := ABT.argsCons (Renaming.shift arg) Cs
       let ret :=  DefEq.InContext ss ts C' (by assumption)
       unfold Subst.subst at ret
       simp [Renaming.shift] at ret
       apply ret
     | Refl => apply DefEq.Refl


 instance argsConsEq
   {args1 args2 : ABT sig n (ABTArg.Args as)}
   {arg1 arg2 : ABT sig n (ABTArg.Arg tag)}
   [argEq : DefEq arg1 arg2]
   [argsEq : DefEq args1 args2]
   : DefEq (tag := ABTArg.Args (tag :: as))
     (ABT.argsCons arg1 args1) (ABT.argsCons arg2 args2) := by
     cases argsEq with
     | InContext ss ts Cs st =>
       let C' : ABT sig (Nat.succ n) (ABTArg.Args (tag :: as))
         := ABT.argsCons (Renaming.shift arg1) Cs
       let ret :=  DefEq.InContext ss ts C' (by assumption)
       unfold Subst.subst at ret
       simp [Renaming.shift] at ret
       apply ret
     | Refl => apply DefEq.Refl


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
