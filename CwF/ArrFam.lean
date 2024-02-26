

import Mathlib.CategoryTheory.Comma.Arrow
import Mathlib.CategoryTheory.Types
import Mathlib.CategoryTheory.Comma.Over
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.Data.Opposite
import Mathlib.CategoryTheory.Equivalence



open CategoryTheory
open Opposite


universe  u

-- Fam is equivalent to the arrow category of Set
-- Fam can be defined fibrationally the arrow category of Set
abbrev ArrFam : Type (u + 1)
  := Arrow (Type u)



-- We can make a family from any type and something indexed by this type
def mkFam (A : Type u) (B : A → Type u) :  ArrFam :=
  { left := Σ x : A , B x
    right := A
    hom := Sigma.fst }

--Projection to get the index type
def ixSet (arr : ArrFam) : Type u :=
  arr.right

--Projection to get the indexed type
def famFor (arr : ArrFam) (a : ixSet arr) : Type u :=
  {ab : arr.left // arr.hom ab = a}

--The index projection cancels with the constructor
theorem famForIxInv (A : Type u) (B : A → Type u) : ixSet (mkFam A B) = A
  := rfl

-- For any index, the family projection cancels with the constructor,
-- up to isomorphism
@[aesop safe]
theorem famForInv (A : Type u) (B : A → Type u) (a : A)
  : famFor (mkFam A B) a ≅ B a where
  hom := fun
    | .mk ab eq => by
      rw [<- eq]
      exact ab.snd
  inv := fun b => {
    val := .mk a b
    property := rfl
  }
  hom_inv_id := by
    funext abPf
    cases abPf with
    | mk ab aa' => cases ab with
    | mk a' b =>
      cases aa'
      rfl
  inv_hom_id := by
    funext b
    reduce
    rfl



-- For any family, making a new family from the projections
-- of that family prodices the original family, up to isomorphism
@[aesop safe]
theorem mkFamInv (arr : ArrFam ) : mkFam (ixSet arr) (famFor arr) ≅ arr where
  hom := by
    fapply Arrow.homMk
    . intro a_ab_pf
      exact a_ab_pf.2.1
    . exact id
    . funext a_ab_pf
      reduce
      reduce at a_ab_pf
      rw [a_ab_pf.2.2]

  inv := by
    fapply Arrow.homMk
    . intro b
      reduce
      fapply Sigma.mk
      . apply arr.hom
        exact b
      . fapply (Subtype.mk b)
        rfl
    . exact id
    . funext b
      rfl

  hom_inv_id := by
    cases arr with
    | mk B A hom =>
      reduce
      congr
      . funext a_ab_pf
        cases a_ab_pf with
        | mk a abpf =>
          cases abpf with
          | mk ab pf =>
            cases pf
            rfl
  inv_hom_id := by
    cases  arr with
    | mk B A hom =>
      reduce
      congr




--A Fam arrow gives us a function on indices
def mapIx  {AB₁ AB₂ : ArrFam}  (f : AB₁ ⟶ AB₂) : ixSet AB₁ → ixSet AB₂ := f.right

-- Mapping the identity morphism over a family's index is the identity
@[simp]
theorem mapIxId {AB : ArrFam} {x : ixSet AB} : mapIx (𝟙 AB) x = x := by
  rfl

-- Mapping a composite arrow over an index gives the composite
@[simp]
theorem mapIxComp  {AB₁ AB₂ AB₃ : ArrFam}  (f : AB₁ ⟶ AB₂) (g : AB₂ ⟶ AB₃) : mapIx (f ≫ g) = mapIx g ∘ mapIx f := by rfl

-- For an index a, a Fam arrow gives a function from the domain family over index a
-- to the codomain family, whose index is the arrow mapped over a
def mapFam {AB₁ AB₂ : ArrFam}
  (f : AB₁ ⟶ AB₂)
  {a : ixSet AB₁}
  (b : famFor AB₁ a )
  : famFor AB₂ (mapIx f a) :=
  ⟨f.left b.val, by
    cases b with
    | mk ab abEq =>
      simp [<- abEq, mapIx]
      apply (congrFun f.w ab)
  ⟩

def unmapFam {AB₁ AB₂ : ArrFam}
  (ixMap : ixSet AB₁ → ixSet AB₂)
  (famMap : {a : ixSet AB₁} -> famFor AB₁ a -> famFor AB₂ (ixMap a))
  : (AB₁ ⟶ AB₂) where
  left x := (famMap ⟨x , Eq.refl _⟩).val
  right := ixMap
  w := by
    funext x
    let prop := (famMap ⟨x , Eq.refl _⟩).property
    simp_all






-- -- def test {C : Type u} [CCat : Category.{v}  C]
-- --   (F : C -> Type u)
-- --   (opMap : {Γ Δ : C} ->  F Γ -> (θ : Δ ⟶ Γ) -> F Δ)
-- --   (Γ Δ : Cᵒᵖ)
-- --   (θ : Γ ⟶ Δ)
-- --   : F (unop Γ) ⟶ F (unop Δ) := by
-- --     intros a
-- --     fapply opMap a
-- --     aesop_cat --fails




-- -- Useful for dealing with dependent equalities
-- def castFam {AB : ArrFam} {a a' : ixSet AB} (b : famFor AB a) (eq : a = a') : famFor AB a' :=
--   cast (by aesop) b

-- @[aesop safe]
-- def mapCast {AB₁ AB₂ : ArrFam} {a : ixSet AB₁} {f g : AB₁ ⟶ AB₂} (b : famFor AB₁ a)  (eq : g = f)
--   : mapFam f b = castFam (mapFam g b) (congrArg₂ mapIx eq (refl a)) := by
--     subst eq
--     rfl

-- -- Mapping the idenitity over an element of a family is the identity
-- @[simp]
-- def mapFamId {AB : ArrFam}  {a : ixSet AB} (b : famFor AB a ) : mapFam (𝟙 AB) b = b := by
--   cases b with
--   | mk ab abEq =>
--     aesop_subst [abEq]
--     simp only [mapIxId, Functor.id_obj]
--     rfl

-- -- Mapping a composite arrow over an element of a family
-- -- is the composition of the mappings
-- @[simp]
-- theorem mapFamComp {AB₁ AB₂ AB₃ : ArrFam}  (f : AB₁ ⟶ AB₂) (g : AB₂ ⟶ AB₃) {a : ixSet AB₁} (b : famFor AB₁ a)
--   : (mapFam (f ≫ g) b) = castFam (mapFam g (mapFam f b)) (by aesop) := by
--     simp [mapIxComp, Function.comp_apply]
--     rfl


--   -- Every family for a given index type is equivalent to the slice over that type
--   def toSlice (arr : ArrFam) : Over (ixSet arr) := Over.mk (arr.hom)

--   def fromSlice {A : Type} (arr : Over A) : ArrFam := Arrow.mk arr.hom

--   @[simp]
--   theorem fromToSlice  {arr : ArrFam} : fromSlice (toSlice arr) = arr := rfl


--   @[simp]
--   theorem toFromSlice  {A : Type} (arr : Over (ixSet arr)) : (toSlice (fromSlice arr)) = arr := by
--     cases arr with
--     | mk left right hom => rfl



-- -- Make a Fam-valued Presheaf from the associated types and morphism-actions
-- def mkPsh {C : Type u} [CCat : Category.{v}  C]
--   (Ty : C -> Type u)
--   (Tm : {Γ : C} -> (T : Ty Γ) -> Type u)
--   (tySub : {Γ Δ : C} -> (T : Ty Γ) -> (θ : Δ ⟶ Γ) -> Ty Δ)
--   (tmSub : {Γ Δ : C} -> {T : Ty Γ} -> (t : Tm T)  -> (θ : Δ ⟶ Γ) -> Tm (tySub T θ))
--   (tyId : {Γ : C} -> {T : Ty Γ} -> tySub T (𝟙 Γ) = T)
--   (tmId : {Γ : C} -> {T : Ty Γ} -> {t : Tm T} -> tmSub t (𝟙 Γ) = cast (by aesop) t)
--   (tyComp : {Γ Δ Ξ : C} -> {T : Ty Γ} -> {ρ : Ξ ⟶ Δ} -> {θ : Δ ⟶ Γ} ->
--      tySub (tySub T θ) ρ = tySub T (ρ ≫ θ))

--   (tmComp : {Γ Δ Ξ : C} -> {T : Ty Γ} -> {t : Tm T} -> {ρ : Ξ ⟶ Δ} -> {θ : Δ ⟶ Γ} ->
--      tmSub (tmSub t θ) ρ = cast (by aesop) (tmSub t (ρ ≫ θ)))
--   :  Cᵒᵖ ⥤ ArrFam where
--   obj Γ := mkFam (Ty (unop Γ)) Tm

--   map θ := by
--     simp_all
--     fapply unmapFam
--     . intros T
--       fapply tySub T
--       exact θ.unop
--     . intros T t
--       apply (Iso.inv (famForInv _ _ _))
--       simp [ixSet, mkFam] at T
--       apply tmSub
--       . apply (Iso.hom (famForInv _ _ _)) at t
--         exact t

--   map_id X := by
--     intros
--     simp_all
--     simp [ mkFam ]
--     apply CommaMorphism.ext <;> try aesop_cat
--     . funext t
--       simp at t
--       cases t with
--       | mk T t =>
--         apply Sigma.ext
--         . simp
--         . simp



--   map_comp := _
