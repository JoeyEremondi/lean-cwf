
import CwF.Fam
import CwF.Util
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


def pshTyMap {Γ : Cᵒᵖ ⥤ Type u₂} (T : Ty Γ) {k1 k2 : Cᵒᵖ}
  (θ : k1 ⟶ k2) (γ : Γ.obj k1) : T.obj ⟨k1 , γ⟩ -> T.obj ⟨k2, Γ.map θ γ⟩ := fun τ =>
  T.map (X := ⟨k1, γ⟩) (Y := ⟨k2 , Γ.map θ γ⟩) ⟨θ , rfl⟩ τ


def pshTyMapEq {Γ : Cᵒᵖ ⥤ Type u₂} {T : Ty Γ} {k1 k2 : Cᵒᵖ}
  (f g : k1 ⟶ k2) (γ : Γ.obj k1)
  (eq1 : f = g) (eq2 : γ1 = γ2)
  : HEq (pshTyMap (T := T) f γ) (pshTyMap (T := T) g γ) := by
    fapply hFunExt <;> try aesop_cat


abbrev pshSnocObj (Γ : Cᵒᵖ ⥤ Type u₂) (T : Ty Γ) (k : Cᵒᵖ) :  Type u₂ :=
  (γ : Γ.obj k) × (T.obj ⟨k,γ⟩)


-- Helps with stupid HEq stuff
abbrev pshSnocMapSnd  {Γ : Cᵒᵖ ⥤ Type u₂} {T : Ty Γ} {k1 k2 : Cᵒᵖ}
  (θ : k1 ⟶ k2) (γτ : pshSnocObj Γ T k1) (f : Γ.obj k1 -> Γ.obj k2)
  (eq : Γ.map θ γτ.fst = f γτ.fst) :
  T.obj ⟨k2 , f γτ.fst⟩ := cast (by aesop) (pshTyMap T θ γτ.fst γτ.snd)

-- theorem pshSnocMapSndId {Γ : Cᵒᵖ ⥤ Type u₂} {T : Ty Γ} {k : Cᵒᵖ}
--   (γτ : pshSnocObj Γ T k) {f : Γ.obj k -> Γ.obj k} {eq : Γ.map (𝟙 k) γτ.fst = f γτ.fst}
--   : HEq (pshSnocMapSnd (𝟙 k) γτ f eq)  γτ.snd := by
--     simp only [pshSnocMapSnd]
--     let helper : HEq (pshSnocMapSnd (𝟙 k) γτ f eq)  (T.map (𝟙 ⟨k,γτ.fst⟩)) := by
--       fapply congrArg T.map
--       fapply Subtype.eq
--       rfl
--     fapply heq_of_eq_of_heq -- (congrFun helper γτ.snd)
--     . simp
--     fapply congrFun (T.map_id _) _

abbrev pshSnocMap {Γ : Cᵒᵖ ⥤ Type u₂} {T : Ty Γ} {k1 k2 : Cᵒᵖ}
  (θ : k1 ⟶ k2) (γτ : pshSnocObj Γ T k1) : pshSnocObj Γ T k2 :=
      ⟨ Γ.map θ γτ.fst
      , pshSnocMapSnd θ γτ (Γ.map θ) rfl
      ⟩

-- theorem pshSnocMapId {Γ : Cᵒᵖ ⥤ Type u₂} {T : Ty Γ} {k : Cᵒᵖ}
--   (γτ : pshSnocObj Γ T k)
--   : pshSnocMap (𝟙 k) γτ = γτ := by
--   fapply Sigma.ext <;> try aesop_cat
--   dsimp only [ pshSnocMap ]
--   simp_rw [Γ.map_id k]
--   fapply heq_of_eq_of_heq (pshSnocMapSndId )
--   aesop_cat


def pshCwF : CwF (Cᵒᵖ ⥤ Type u₂) where
  empty := Limits.terminal _

  emptyUnique := Limits.uniqueToTerminal

  snoc Γ T := {
    obj := pshSnocObj Γ T
    map := pshSnocMap
    map_id := fun k => by
      funext γτ
      simp at γτ
      cases γτ with
      | mk γ τ =>
        let τeq : τ = T.map (𝟙 ⟨k, γ⟩) τ := by
          symm
          fapply congrFun _ τ <;> simp
        symm
        simp
        fapply heq_of_eq_of_heq τeq
        simp [pshSnocMapSnd]
        fapply  hCong (f := T.map (𝟙 ⟨k,γ⟩)) (g := T.map _) (x := τ) (y := τ)
      -- . simp
      -- . dsimp only [pshSnocMap]
      --   let helper : _ := pshSnocMapSndId γτ
      --   fapply helper
    --   funext γτ
    --   cases γτ with
    --   | mk γ τ =>
    --     fapply Sigma.ext
    --     . aesop_cat
    --     . let Teq := (T.map_id ⟨k, γ⟩)
    --       simp only at Teq
    --       simp
    --       fapply hCong (x := τ) (y := τ) (g := id)
    map_comp := by admit

  }

  -- p :=
  --   ⟨ fun k => by  reduce
  --   , fun k => by simp    ⟩
