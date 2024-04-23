import Mathlib.Data.ULift
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.Types

open CategoryTheory

universe w u v

-- abbrev uliftIso  (A : Type u) (B : Type v) (W : Type (w+1)) : Type _ :=
--   uliftFunctor.{max v w, u}.obj A ≅ uliftFunctor.obj.{max u w,v} B
-- abbrev uliftIsoMax  (A : Type u) (B : Type v)  : Type _ :=
--   uliftFunctor.{v,u}.obj A ≅ uliftFunctor.obj.{u,v} B

-- def maxType (_ : Type u) (_ : Type v) : Type _ := Type (max u v)

-- notation:10 X "[" w "]≅" Y => (uliftIso X Y (Type w) )
-- notation:10 X "[" u "," v "]≅" Y => (uliftIso X Y (Type (max u v)) )
-- notation:10 X "↑≅" Y => (uliftIsoMax X Y)

-- @[simp]
-- def uliftSimp {A : Type u} (x : ULift.{max v u} A) : ULift.{v} A :=
--   by aesop

-- def  simpIso  {A : Type u} {B : Type v}
--   (iso : A [w]≅ B) : (A ↑≅ B)  where
--     hom a := by
--       let b := iso.hom (ULift.up (a.down))
--       apply ULift.up
--       apply b.down
--     inv b := by
--       let a := iso.inv (ULift.up (b.down))
--       apply ULift.up
--       apply a.down
--     hom_inv_id := by
--       funext a
--       simp
--       cases a
--       apply ULift.ext
--       simp
--       let x := iso.inv_comp_eq
--       apply Iso.comp
--       cases a
--       apply ULift.ext
--       simp


-- def  liftIso  {A : Type u} {B : Type u}
--   (iso : A ≅ B) : (A [w]≅ B) := by
--     apply Functor.mapIso (X := A) (Y := B) uliftFunctor iso

-- @[simp]
-- def  unliftIso  {A : Type u} {B : Type u}
--   (iso : A [w]≅ B) : (A ≅ B) := by
--     dsimp [uliftIso] at iso
--     apply Functor.preimageIso (X := A) (Y := B) uliftFunctor iso

-- def viaUlift {A B : Type u} {X Y : Type v}
--   (iso1 : A ↑≅ X) (iso2 : B ↑≅ Y) (iso3 : X ≅ Y) : A ≅ B :=
--     Functor.preimageIso (X := A) (Y := B) uliftFunctor
--       (iso1 ≪≫ Functor.mapIso uliftFunctor iso3 ≪≫ iso2.symm)
