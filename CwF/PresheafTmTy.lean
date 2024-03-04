
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


def pshTyMap {Γ : Cᵒᵖ ⥤ Type u₂} (T : pshTy Γ) {k1 k2 : Cᵒᵖ}
  (θ : k1 ⟶ k2) (γ : Γ.obj k1) : T.obj ⟨k1 , γ⟩ -> T.obj ⟨k2, Γ.map θ γ⟩ :=
  T.map (X := ⟨k1, γ⟩) (Y := ⟨k2 , Γ.map θ γ⟩) ⟨θ , rfl⟩

-- A term is a mapping from stages and its context's elements at that stage
-- to the type's elements at that stage and element
structure pshTm  {Γ : Cᵒᵖ ⥤ Type u₂} (T : pshTy Γ) : Type (max u v (u₂ + 1)) :=
   tmFun : (k : Cᵒᵖ) -> (γ : Γ.obj k) ->  (T.obj ⟨k,γ⟩)
   tmNat : (i j : Cᵒᵖ) -> (θ : i ⟶ j) -> (γ : Γ.obj i)
          -> pshTyMap T θ γ (tmFun i γ)  = tmFun j (Γ.map θ γ) := by aesop_cat


def pshTySub {Γ Δ : Cᵒᵖ ⥤ Type u₂} (T : pshTy Γ) (θ : Δ ⟶ Γ) : pshTy Δ :=
  (CategoryOfElements.map θ) ⋙ T

def pshTyMapSub {Γ Δ : Cᵒᵖ ⥤ Type u₂} {θ : Δ ⟶ Γ} {T : pshTy Γ}
   {k1 k2 : Cᵒᵖ} {f : k1 ⟶ k2} {δ : Δ.obj k1}
  : HEq (pshTyMap (pshTySub T θ) f δ)  (pshTyMap T f (θ.app k1 δ)) := by
    simp [pshTyMap, pshTySub,CategoryOfElements.map]
    let natDel :=  congrFun (θ.naturality f) δ
    congr
    . funext
      simp [natDel]
      constructor <;> intros assum <;> simp [assum] <;> try assumption
      . symm
        assumption
    . simp
      apply HEq_iff


def pshTyMapSubArg {Γ Δ : Cᵒᵖ ⥤ Type u₂} {θ : Δ ⟶ Γ} {T : pshTy Γ}
   {k1 k2 : Cᵒᵖ} {f : k1 ⟶ k2} {δ : Δ.obj k1} {x : T.obj _}
  : HEq (pshTyMap (pshTySub T θ) f δ x)  (pshTyMap T f (θ.app k1 δ) x) :=
    hCongFunSimp x
      (by
        simp [pshTyMap, pshTySub,CategoryOfElements.map]
        congr
        apply congrFun (θ.naturality f) δ
      )
      (pshTyMapSub)



theorem pshTyMapId {Γ : Cᵒᵖ ⥤ Type u₂} (T : pshTy Γ) {k : Cᵒᵖ} {γ : Γ.obj k}
  : HEq (pshTyMap T (𝟙 k) γ) (id : T.obj ⟨k, γ⟩ -> T.obj ⟨k,γ⟩)  := by
    let Tlem := T.map_id ⟨k, γ⟩
    fapply heq_of_heq_of_eq _ Tlem
    rw [pshTyMap]
    congr <;> try aesop_cat


theorem pshTyMapComp {Γ : Cᵒᵖ ⥤ Type u₂} (T : pshTy Γ) {k1 k2 k3 : Cᵒᵖ} {γ : Γ.obj k1}
  (f : k1 ⟶ k2 ) (g : k2 ⟶ k3)
    : HEq (pshTyMap T (f ≫ g) γ) ((pshTyMap T g _) ∘ (pshTyMap T f γ)) := by
    let Tlem :=
      T.map_comp (X := ⟨k1 , γ⟩) (Y := ⟨k2 , Γ.map f γ⟩) (Z := ⟨k3, Γ.map g (Γ.map f γ)⟩) ⟨f , rfl⟩ ⟨g , rfl⟩
    fapply heq_of_heq_of_eq _ Tlem
    rw [pshTyMap]
    congr <;> try aesop_cat

def pshTyMapEq {Γ : Cᵒᵖ ⥤ Type u₂} {T : pshTy Γ} {k1 k2 : Cᵒᵖ}
  (f g : k1 ⟶ k2) (γ : Γ.obj k1)
  (eq1 : f = g) (eq2 : γ1 = γ2)
  : HEq (pshTyMap (T := T) f γ) (pshTyMap (T := T) g γ) := by
    fapply hFunExt <;> try aesop_cat


def pshTmSub {Γ Δ : Cᵒᵖ ⥤ Type u₂} {T : pshTy Γ} (t : pshTm T) (θ : Δ ⟶ Γ)   :
  pshTm (pshTySub T θ) :=
    ⟨
      (fun i => fun δ => t.tmFun i (θ.app i δ)),
      (by
        intros i j f δ
        dsimp only
        let eq := t.tmNat i j f (θ.app i δ)
        let nat := symm (congrFun (θ.naturality f) δ)
        let nat' := hCong (refl (t.tmFun j)) nat
        simp at nat'
        eapply eq_of_heq
        fapply HEq.trans _ nat'
        fapply heq_of_heq_of_eq _ eq
        apply pshTyMapSubArg
        )
    ⟩


abbrev pshTmTyFunctor : (Cᵒᵖ ⥤ Type u₂)ᵒᵖ ⥤ Fam where
  obj Γ := mkFam
    (pshTy (Opposite.unop Γ))
    (pshTm (Γ := Opposite.unop Γ))

  map := @fun ⟨X⟩ ⟨Y⟩ ⟨ θ ⟩  =>
    unmapFam
      (fun T => pshTySub T θ)
      (@fun T x => by
        simp_all [ixSet, mkFam]
        simp [famFor, mkFam] at x
        let y := x.val
        let z := y.snd
        simp [x.property] at z
        let ret (t : pshTm T) := pshTmSub (T := T) t θ
        simp [famFor]
        simp at ret
        let retz := ret z
        fconstructor <;> try fconstructor <;> try aesop_cat
        )



instance pshTmTy: TmTy (Cᵒᵖ ⥤ Type u₂)  where
  F := pshTmTyFunctor