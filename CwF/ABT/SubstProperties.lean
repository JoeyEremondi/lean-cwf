
import Mathlib.Data.Fin.Fin2
import Mathlib.Logic.Unique
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Init.Data.Nat.Lemmas

import CwF.ABT.ABT
import CwF.ABT.Renaming
import CwF.ABT.Subst

universe u v'

namespace ABT

--Namespace we open when we want to treat all renamings as substitutions

namespace Subst
  @[simp ]
  theorem wkRenaming (ρ : Renaming m n)
    : ofRenaming (sig := sig) (ρ.wk) = (ofRenaming ρ).wk := by
    funext x
    simp [ofRenaming, Renaming.wk, wk, Renaming.shift, Renaming.rename]
    cases x <;> simp [Fin2.add]

  -- @[simp]
  theorem substOfRenaming {t : ABT sig n a} : {m : ℕ} →  {ρ : Renaming m n}
      → t⦇ρ⦈ᵣ = t⦇ofRenaming ρ⦈ := by
    induction t
      <;> intros m ρ
      <;> simp_all [ABT.map, Renaming.rename, Renaming.wk, wk, ofRenaming ]

      

  -- Useful in contexts where we're focused on renaming
  theorem unOfRenaming {t : ABT sig n a} : {m : ℕ} →  {ρ : Renaming m n}
      → t⦇ofRenaming ρ⦈ = t⦇ρ⦈ᵣ := by simp [substOfRenaming]


  @[simp]
  theorem wk_id : wk (sig := sig) (n := n) id = id := by
    funext x
    simp only [wk, id, Renaming.shift]
    cases x <;> simp [Renaming.rename, Fin2.add]

  @[simp]
  theorem sub_id (t : ABT sig n a) : t⦇id⦈ = t := by
    induction t
      <;> simp only [subst, Renaming.rename, Renaming.wk, wk, ofRenaming, id ]
      <;> try aesop_cat


  -- @[simp]
  -- theorem sub_comp {t : ABT sig c tag} : ∀ {a} {b}, {θ : Subst sig a b} →  {θ2 : Subst sig b c} →
  --   subst θ (subst θ2 t) = subst (θ ⨟ θ2) t := by
  --   induction t with
  --     intros θ θ2
  --     <;> simp only [ABT.map, Renaming.rename, Renaming.wk, wk, ofRenaming ]
  --     <;> try aesop_cat


  @[local simp]
  theorem sub_rename_extL {ρ : Renaming b c} {θ : Subst sig a b} :
    θ.wk ⨟ (ofRenaming ρ).wk  = (θ ⨟ ofRenaming ρ).wk := by
     funext x
     cases x <;> aesop_cat
     -- | fs x =>
     --    dsimp only [comp, wk, Renaming.shift, ofRenaming,subst]
     --    rw [Renaming.rename]
     --    simp [ABT.map, Fin2.add, wk]
     --    rw [Renaming.shift]

  @[local simp]
  theorem sub_rename_extR {ρ : Renaming a b} {θ : Subst sig b c} :
   (ofRenaming ρ).wk ⨟ θ.wk = wk (ofRenaming ρ ⨟  θ) := by
     funext x
     cases x <;> try aesop_cat
     simp [comp, wk, ABT.map]
     rw [<- substOfRenaming]
     rw [<- wkRenaming]
     rw [<- substOfRenaming]
     simp only [Renaming.weaken_wk]

  @[local simp]
  theorem sub_rename_fusionL {t : ABT sig c tag} : ∀ {a} {b} {ρ : Renaming b c} {θ : Subst sig a b},
    t⦇ ρ ⦈ᵣ⦇ θ ⦈ = t⦇  θ ⨟ ofRenaming ρ ⦈ := by
   induction t <;> intros a b ρ θ <;> simp_all [ABT.map, Renaming.rename]
   aesop

  lemma proj_wk : (θ.wk⨟ proj) = (proj ⨟ θ) := by
      funext x
      dsimp only [comp, ofRenaming]
      simp [wk, proj]
      rw [<- substOfRenaming, ofRenaming]
      simp [subst, ABT.map, wk, Renaming.shift]

  @[local simp]
  theorem sub_rename_fusionR {t : ABT sig c tag} : ∀ {a} {b} {ρ : Renaming a b} {θ : Subst sig b c},
    t⦇ θ ⦈⦇ ρ ⦈ᵣ = t⦇  ofRenaming ρ ⨟ θ ⦈ := by
  induction t <;> intros a b ρ θ <;> try (simp_all [ABT.map, ABT.map, Renaming.rename] <;> aesop_cat)
  . simp [ABT.map, ABT.map]
    unfold comp
    simp [substOfRenaming]




  lemma wk_comp
    {θ : Subst sig a b}  {θ2 : Subst sig b c}
    :  θ.wk ⨟ θ2.wk = (θ ⨟ θ2).wk := by
    funext x
    cases x with simp [wk, comp]
    | fz => aesop
    | fs x =>
      let helper := proj_wk (θ := θ)
      rw [proj] at helper
      simp [Renaming.shift, helper, proj]



  @[simp]
  theorem ofRenameId : ofRenaming (sig := sig) (n := n) Renaming.id = id := by
    funext x
    simp [ofRenaming, Renaming.id, id]

  @[simp]
  theorem ofRenameIdDef : ofRenaming (sig := sig) (n := n) (fun x => x) = id := by
    funext x
    simp [ofRenaming, Renaming.id, id]





  --Category and CwF
  --CwF laws for substitutions
  --It turns out these make a terminating rewrite system
  @[simp]
  theorem sub_comp {t : ABT sig c tag} : ∀ {a} {b}, {θ : Subst sig a b} →  {θ2 : Subst sig b c} →
    t⦇θ2⦈⦇θ⦈ = t⦇θ⨟θ2⦈ := by
    induction t with
      (intros a b θ θ2
       simp only [subst, Renaming.rename, Renaming.wk, wk, ofRenaming]
       try aesop_cat)
    | bind xt IH => simp [IH, wk_comp]

  @[simp]
  theorem comp_idL (θ : Subst sig m n) :
    θ ⨟ id = θ := by
    funext
    aesop

  @[simp]
  theorem comp_idR (θ : Subst sig m n) :
    id ⨟ θ = θ := by
    funext
    simp [comp]

  @[simp]
  theorem comp_assoc (θ1 : Subst sig a b) (θ2 : Subst sig b c) (θ3 : Subst sig c d)
    : θ1 ⨟ (θ2 ⨟ θ3) = (θ1 ⨟ θ2) ⨟ θ3  := by
    funext x
    simp [comp]

  @[simp]
  theorem sub_dist {t : Term sig c } {θ1 : Subst sig b c} {θ2 : Subst sig c a}
    : θ1⨟⟪θ2 ● t⟫ = ⟪θ1 ⨟ θ2 ● t⦇θ1⦈⟫ := by
      funext x
      cases x <;> simp [comp, ext]

  @[simp]
  theorem z_shift : ext (n := n) (sig := sig) proj x0 = id := by
    funext x
    simp [ext, proj, id]
    cases x <;> try aesop_cat

  @[simp]
  theorem sub_eta {θ : Subst sig m (Nat.succ n)} :
    ext (θ ⨟ proj) x0⦇θ⦈ = θ := by
      funext x
      cases x <;> simp [ext, subst, comp, ABT.map]


  -- @[simp]
  theorem wk_def {θ : Subst sig a b} :
    θ.wk = ext (proj ⨟ θ) (ABT.var Fin2.fz)  := by
    funext x
    simp [wk, ext, proj, comp, Renaming.shift]
    cases x <;> simp [substOfRenaming]

  @[simp]
  theorem sub_head {θ : Subst sig m n} {t : Term sig m} :
      (ext θ t) (Fin2.fz) = t := by simp [ext]

  @[simp]
  theorem sub_tail {θ : Subst sig m n} {t : Term sig m} :
      ext θ t ⨟ proj = θ := by
      funext x
      cases x <;> aesop_cat

  -- Useful when dealing with renamings
  theorem singleSubRename {s : Term sig (Nat.succ n)} {t : Term sig n} {ρ : Renaming m n}
    : s/[ t /x]⦇ρ⦈ᵣ = (s⦇Renaming.wk ρ⦈ᵣ)/[t⦇ρ⦈ᵣ /x] := by
      simp [wkRenaming, wk_def, substOfRenaming, Subst.subst, ABT.map]

  @[simp]
  theorem singleSubSub {s : Term sig (Nat.succ n)} {t : Term sig n} {θ : Subst sig m n}
    : s/[ t /x]⦇θ⦈ = (s⦇θ.wk⦈)/[t⦇θ⦈ /x] := by simp [wk_def, Subst.subst, ABT.map]


  -- We never want the user to have to think about renamings, generally
  -- TODO undo this?
  attribute [simp] substOfRenaming
  attribute [simp] ABT.map

  @[simp]
  theorem subVecNil : (depVecNil (ss := ss))⦇θ⦈ = depVecNil := by
    simp [depVecNil]
    funext
    contradiction

  @[simp]
  theorem subVecCons : (ABT.vecCons h t)⦇θ⦈ = ABT.vecCons h⦇θ⦈ t⦇θ⦈ := by
    unfold vecCons
    cases t
    unfold_subst
    funext i
    simp [Fin2.cases']
    cases i <;> simp

  @[simp]
  theorem subTeleCons : (ABT.teleCons h t)⦇θ⦈ = ABT.teleCons h⦇θ⦈ t⦇wk θ⦈ := by
    unfold teleCons
    cases t
    unfold_subst
    funext i
    simp [Fin2.cases']
    cases i <;> simp
    unfold_subst
    rfl

@[simp]
  theorem renVecNil {θ : Renaming m n} : (depVecNil (sig := sig) (ss := ss))⦇θ⦈ᵣ = depVecNil := by
    simp [depVecNil]
    funext
    contradiction

  @[simp]
  theorem renVecCons : (ABT.vecCons h t)⦇θ⦈ᵣ = ABT.vecCons h⦇θ⦈ᵣ t⦇θ⦈ᵣ := by
    simp [substOfRenaming]

  @[simp]
  theorem renTeleCons : (ABT.teleCons h t)⦇θ⦈ᵣ = ABT.teleCons h⦇θ⦈ᵣ t⦇Renaming.wk θ⦈ᵣ := by
    simp [substOfRenaming]


  --Substitutions have no effect on closed terms, so they're all equivalent
  --to "introduce unused variables"
  @[simp]
  theorem fromClosedSubst  {θ : Subst sig n 0} : θ  = ofRenaming fromClosed := by
    funext i ; contradiction


end Subst


-- def weaken (t : ABT sig n a) : ABT sig (n+1) a := by
--   cases t <;> try (constructor <;> aesop) <;> try (apply Fin2.fs)





end ABT
