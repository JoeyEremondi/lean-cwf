import Mathlib.CategoryTheory.Arrow
import Mathlib.CategoryTheory.Types
import Mathlib.CategoryTheory.Over


open CategoryTheory


universe  u

-- Fam can be defined fibrationally the arrow category of Set
abbrev Fam : Type (u + 1) := Arrow (Type u)


-- We can make a family from any type and something indexed by this type
def mkFam (A : Type u) (B : A → Type u) :  Fam :=
  { left := Σ x : A , B x
    right := A
    hom := Sigma.fst }

--Projection to get the index type
def ixSet (arr : Fam) : Type u :=
  arr.right

--Projection to get the indexed type
def famFor (arr : Fam) (a : ixSet arr) : Type u :=
  {ab : arr.left // arr.hom ab = a}

--The index projection cancels with the constructor
theorem famForIxInv (A : Type u) (B : A → Type u) : ixSet (mkFam A B) = A := rfl

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
theorem mkFamInv (arr : Fam ) : mkFam (ixSet arr) (famFor arr) ≅ arr where
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
def mapIx  {AB₁ AB₂ : Fam}  (f : AB₁ ⟶ AB₂) : ixSet AB₁ → ixSet AB₂ := f.right

-- Mapping the identity morphism over a family's index is the identity
@[simp]
theorem mapIxId {AB : Fam} {x : ixSet AB} : mapIx (𝟙 AB) x = x := by
  rfl

-- Mapping a composite arrow over an index gives the composite
@[simp]
theorem mapIxComp  {AB₁ AB₂ AB₃ : Fam}  (f : AB₁ ⟶ AB₂) (g : AB₂ ⟶ AB₃) : mapIx (f ≫ g) = mapIx g ∘ mapIx f := by rfl

-- For an index a, a Fam arrow gives a function from the domain family over index a
-- to the codomain family, whose index is the arrow mapped over a
def mapFam {AB₁ AB₂ : Fam}  (f : AB₁ ⟶ AB₂) {a : ixSet AB₁} (b : famFor AB₁ a ) : famFor AB₂ (mapIx f a) :=
  ⟨f.left b.val, by
    cases b with
    | mk ab abEq =>
      simp [<- abEq, mapIx]
      apply (congrFun f.w ab)
  ⟩

-- Mapping the idenitity over an element of a family is the identity
@[simp]
def mapFamId {AB : Fam}  {a : ixSet AB} (b : famFor AB a ) : mapFam (𝟙 AB) b = b := by
  cases b with
  | mk ab abEq =>
    aesop_subst [abEq]
    simp only [mapIxId, Functor.id_obj]
    rfl

-- Mapping a composite arrow over an element of a family
-- is the composition of the mappings
@[simp]
theorem mapFamComp {AB₁ AB₂ AB₃ : Fam}  (f : AB₁ ⟶ AB₂) (g : AB₂ ⟶ AB₃) {a : ixSet AB₁} (b : famFor AB₁ a)
  : HEq (mapFam (f ≫ g) b) (mapFam g (mapFam f b)) := by
    simp [mapFam, <- b.property]



  -- Every family for a given index type is equivalent to the slice over that type
  def toSlice (arr : Fam) : Over (ixSet arr) := Over.mk (arr.hom)

  def fromSlice {A : Type} (arr : Over A) : Fam := Arrow.mk arr.hom

  @[simp]
  theorem fromToSlice  {arr : Fam} : fromSlice (toSlice arr) = arr := rfl


  @[simp]
  theorem toFromSlice  {A : Type} (arr : Over (ixSet arr)) : (toSlice (fromSlice arr)) = arr := by
    cases arr with
    | mk left right hom => rfl
