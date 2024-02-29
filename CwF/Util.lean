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
