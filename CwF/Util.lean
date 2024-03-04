import Mathlib.CategoryTheory.Category.Basic


theorem hCong {A : Type u} {B : A → Type v} {f g : (a : A) → B a} {x y : A}
    (funEq : f = g) (argEq : x = y) :
      HEq (f x) (g y) := by aesop


theorem hCongFun {A : Type u} {B C : A → Type v} {f : (a : A) → B a} {g : (a : A) → C a}
    (x : A)
    (eq : B = C)
    (funEq : HEq f g)  :
      HEq (f x) (g x) := by aesop

theorem hCongFunSimp {A : Type u} {B C :  Type v} {f : (a : A) → B } {g : (a : A) → C }
    (x : A)
    (eq : B = C)
    (funEq : HEq f g)  :
      HEq (f x) (g x) := by aesop


theorem hFunExt {A B C : Type u}
  {f : A -> B} {g : A -> C}
  (eq : B = C)
  (extEq : (a : A) -> HEq (f a) (g a))
  : HEq f g := by
    let funEq : (A -> B) = (A -> C) := by aesop
    fapply heq_of_cast_eq funEq
    funext x
    let fxEq : HEq (cast funEq f x) (f x) := by aesop
    fapply eq_of_heq
    fapply HEq.trans fxEq
    fapply extEq



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

theorem Subtype_HExtEq  {A : Type u} {P Q : A -> Prop}
 {x : Subtype P} {y : Subtype Q}
 (eq : x.val = y.val)
 (equiv : P = Q)
 : HEq x y := by aesop

theorem Subtype_HExt  {A : Type u} {P Q : A -> Prop}
 {x : Subtype P} {y : Subtype Q}
 (eq : x.val = y.val)
 (equiv : (x : A) -> P x ↔ Q x)
 : HEq x y :=  by
   let PeqQ : P = Q := by
     funext x
     apply propext
     apply equiv x
   apply Subtype_HExtEq <;> assumption

theorem HEq_iff {P : Prop}
  (p : P)
  (t : True)
  : HEq p t := by aesop