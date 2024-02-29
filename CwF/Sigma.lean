import Std.Tactic.Ext

-- Helper module for a Sigma lemma we need over and over again
-- Helps dealing with HEq for sigma types
theorem Sigma_HExt
  {α : Type u_1} {β : α → Type u_2} {x y : Sigma β}
  (eq : x.fst = y.fst) (heq : x.fst = y.fst -> HEq x.snd y.snd)
  : x = y := Sigma.ext eq (heq eq)

theorem Subtype_Sigma_ext
  {A : Type u}
  {B : A -> Type u}
  {P : {a : A} -> B a -> Prop}
  {x y : (a : A) × @Subtype (B a) P}
  (eq1 : x.fst = y.fst)
  (eq2 : HEq x.snd.val y.snd.val)
  : x = y := by cases x with
  | mk x1 x2 => cases y with
  | mk y1 y2 =>
    fapply Sigma.ext
    . assumption
    . cases eq1
      simp
      apply Subtype.eq
      simp at eq2
      assumption
