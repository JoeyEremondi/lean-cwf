
import CwF.Fam
import CwF.Sigma
import CwF.CwFProperties
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.NatTrans
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Presheaf
import Mathlib.CategoryTheory.Elements
import Mathlib.Data.Opposite
import Mathlib.CategoryTheory.Types



import CwF.CwF

open CategoryTheory

-- Pi type structure in a category with families


universe u v u₂
variable {C : Type u} [CCat : Category.{v}  C]

-- abbrev PShC : Type _ :=
--   Cᵒᵖ ⥤ Type u₂

-- def PshCat : Category.{max u u₂,max u v (u₂ + 1)} PShC  :=
--   @Functor.category (Cᵒᵖ) _ (Type u₂) _

-- A type is a presheaf over the elements of Γ
def pshTy  (Γ : Cᵒᵖ ⥤ Type u₂) : Type (max u v (u₂ + 1)) :=
  Functor.Elements Γ ⥤ Type u₂

-- A term is a mapping from stages and its context's elements at that stage
-- to the type's elements at that stage and element
def pshTm  (Γ : Cᵒᵖ ⥤ Type u₂) (T : pshTy Γ) : Type (max u v (u₂ + 1)) :=
  (i : Cᵒᵖ) -> (ρ : Γ.obj i) -> ULift.{max u v (u₂ + 1)} (T.obj ⟨i , ρ⟩)

def pshTySub {Γ Δ : Cᵒᵖ ⥤ Type u₂} (θ : Δ ⟶ Γ) (T : pshTy Γ) : pshTy Δ :=
  (CategoryOfElements.map θ) ⋙ T

def pshTmSub {Γ Δ : Cᵒᵖ ⥤ Type u₂} (θ : Δ ⟶ Γ) (T : pshTy Γ) (t : pshTm Γ T) :
  pshTm Δ (pshTySub θ T) := (fun i => fun δ =>
    t i (θ.app i δ))



abbrev pshTmTyFunctor : (Cᵒᵖ ⥤ Type u₂)ᵒᵖ ⥤ Fam where
  obj
  | ⟨ Γ ⟩ => mkFam
    (pshTy Γ)
    (pshTm Γ)

  map := @fun ⟨X⟩ ⟨Y⟩ ⟨ θ ⟩  =>
    unmapFam
      (pshTySub θ)
      (@fun T x => by
        simp_all [ixSet, mkFam]
        simp [famFor, mkFam] at x
        let y := x.val
        let z := y.snd
        simp [x.property] at z
        let ret := pshTmSub θ T
        simp [famFor]
        simp at ret
        let retz := ret z
        fconstructor <;> try fconstructor <;> try aesop_cat
        . exact retz
        )

instance pshTmTy: TmTy (Cᵒᵖ ⥤ Type u₂)  where
  F := pshTmTyFunctor

abbrev pshSnocObj (Γ : Cᵒᵖ ⥤ Type u₂) (T : Ty Γ) (k : Cᵒᵖ) :  Type u₂ :=
  (γ : Γ.obj k) × (T.obj ⟨k,γ⟩)


-- Helps with stupid HEq stuff
abbrev pshSnocMapSnd  {Γ : Cᵒᵖ ⥤ Type u₂} {T : Ty Γ} {k1 k2 : Cᵒᵖ}
  (θ : k1 ⟶ k2) (γτ : pshSnocObj Γ T k1) (f : Γ.obj k1 -> Γ.obj k2)
  (eq : Γ.map θ γτ.fst = f γτ.fst) :
  T.obj ⟨k2 , f γτ.fst⟩ := T.map (X := ⟨k1 , _⟩) (Y := ⟨k2, _⟩) ⟨θ , eq⟩ γτ.snd

theorem pshSnocMapSndId {Γ : Cᵒᵖ ⥤ Type u₂} {T : Ty Γ} {k : Cᵒᵖ}
  (γτ : pshSnocObj Γ T k) {eq : _}
  : pshSnocMapSnd (𝟙 k) γτ id eq = γτ.snd := by
    simp only [pshSnocMapSnd]
    let helper : T.map (X := ⟨k , _⟩) (Y := ⟨k, _⟩) ⟨𝟙 k , eq⟩  = T.map (𝟙 ⟨k,γτ.fst⟩) := by
      fapply congrArg T.map
      fapply Subtype.eq
      rfl
    fapply Eq.trans (congrFun helper γτ.snd)
    fapply congrFun (T.map_id _) _

abbrev pshSnocMap {Γ : Cᵒᵖ ⥤ Type u₂} {T : Ty Γ} {k1 k2 : Cᵒᵖ}
  (θ : k1 ⟶ k2) (γτ : pshSnocObj Γ T k1) : pshSnocObj Γ T k2 :=
      ⟨ Γ.map θ γτ.fst
      , pshSnocMapSnd θ γτ (Γ.map θ) rfl
      ⟩



-- def pshCwF : CwF (Cᵒᵖ ⥤ Type u₂) where
--   empty := Limits.terminal _

--   emptyUnique := Limits.uniqueToTerminal

--   snoc Γ T := {
--     obj := pshSnocObj Γ T
--     map := pshSnocMap
--     map_id := fun k => by
--       funext γτ
--       simp at γτ
--       simp only
--       let helper : pshSnocMap (𝟙 k) γτ  = ⟨γτ.fst , (T.map (X := ⟨k , _⟩) (Y := ⟨k , _⟩)  (⟨𝟙 k , by aesop⟩) γτ.snd) ⟩
--         := by
--           dsimp only [pshSnocMap]
--           fapply Eq.refl
--       let eq := congrFun (Γ.map_id k) _
--       simp [Γ.map_id k]
--       dsimp
--       reduce
--     -- by
--     --   funext γτ
--     --   cases γτ with
--     --   | mk γ τ =>
--     --     fapply Sigma.ext
--     --     . aesop_cat
--     --     . let Teq := (T.map_id ⟨k, γ⟩)
--     --       simp only at Teq
--     --       simp
--     --       fapply hCong (x := τ) (y := τ) (g := id)



--   }

--   -- p :=
--   --   ⟨ fun k => by  reduce
--   --   , fun k => by simp    ⟩
