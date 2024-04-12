
import Mathlib.Data.Fin.Fin2
import Mathlib.Logic.Unique
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Init.Data.Nat.Lemmas

import CwF.ABT.Defs
import CwF.ABT.Renaming
import CwF.ABT.Subst

universe u v'

namespace ABT

namespace Subst


  @[simp ]
  theorem wkRenaming (ρ : Renaming m n)
    : ofRenaming (sig := sig) (ρ.wk) = (ofRenaming ρ).wk := by
    funext x
    simp [ofRenaming, Renaming.wk, wk, Renaming.shift, Renaming.rename]
    cases x <;> simp [Fin2.add]

  -- @[simp]
  theorem substOfRenaming {t : ABT sig n a} : {m : ℕ} →  {ρ : Renaming m n}
      → Renaming.rename ρ t = subst (ofRenaming ρ) t := by
    induction t
      <;> intros m ρ
      <;> simp_all [subst, Renaming.rename, Renaming.wk, wk, ofRenaming ]
      <;> aesop

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
  --     <;> simp only [subst, Renaming.rename, Renaming.wk, wk, ofRenaming ]
  --     <;> try aesop_cat


  @[simp]
  theorem sub_rename_extL {ρ : Renaming b c} {θ : Subst sig a b} :
    (wk θ) ⨟ (wk (ofRenaming ρ))  = wk (θ ⨟ ofRenaming ρ) := by
     funext x
     cases x <;> aesop_cat
     -- | fs x =>
     --    dsimp only [comp, wk, Renaming.shift, ofRenaming,subst]
     --    rw [Renaming.rename]
     --    simp [subst, Fin2.add, wk]
     --    rw [Renaming.shift]

  @[simp]
  theorem sub_rename_extR {ρ : Renaming a b} {θ : Subst sig b c} :
   (wk (ofRenaming ρ)) ⨟ (wk θ) = wk (ofRenaming ρ ⨟  θ) := by
     funext x
     cases x <;> try aesop_cat
     simp [comp, wk]
     rw [<- substOfRenaming]
     rw [<- wkRenaming]
     rw [<- substOfRenaming]
     simp

  @[simp]
  theorem sub_rename_fusionL {t : ABT sig c tag} : ∀ {a} {b} {ρ : Renaming b c} {θ : Subst sig a b},
    t⦇ ρ ⦈ᵣ⦇ θ ⦈ = t⦇  θ ⨟ ofRenaming ρ ⦈ := by
   induction t <;> intros a b ρ θ <;> simp_all [subst, Renaming.rename] <;> try aesop_cat

  @[simp]
  theorem sub_rename_fusionR {t : ABT sig c tag} : ∀ {a} {b} {ρ : Renaming a b} {θ : Subst sig b c},
    t⦇ θ ⦈⦇ ρ ⦈ᵣ = t⦇  ofRenaming ρ ⨟ θ ⦈ := by
   induction t <;> intros a b ρ θ <;> try (simp_all [subst, ABT.map, Renaming.rename] <;> aesop_cat)
   . simp [subst, ABT.map]
     unfold comp
     simp [substOfRenaming]


  theorem proj_wk : (wk θ⨟ proj) = (proj ⨟ θ) := by
      funext x
      dsimp only [comp, ofRenaming, subst, ABT.map]
      simp_all [<- substOfRenaming, Fin2.add, proj]
      simp_all [ wk, Renaming.shift, Fin2.add]

  theorem wk_comp
    {θ : Subst sig a b}  {θ2 : Subst sig b c}
    :  (wk θ ) ⨟ (wk θ2) = wk (θ ⨟ θ2) := by
    funext x


    cases x with simp [wk, comp] <;> try aesop_cat
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
      intros a b θ θ2
      <;> simp only [subst, Renaming.rename, Renaming.wk, wk, ofRenaming]
      <;> try aesop_cat
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
    : (θ1 ⨟ θ2) ⨟ θ3 = θ1 ⨟ (θ2 ⨟ θ3) := by
    funext x
    simp [comp]

  @[simp]
  theorem sub_dist {t : Term sig c } {θ1 : Subst sig b c} {θ2 : Subst sig c a}
    : (θ1 ⨟ (ext θ2 t)) = ext (θ1 ⨟ θ2) (subst θ1 t) := by
      funext x
      cases x <;> simp [comp, ext]

  @[simp]
  theorem z_shift : ext (n := n) (sig := sig) proj (ABT.var Fin2.fz) = id := by
    funext x
    simp [ext, proj, id]
    cases x <;> try aesop_cat

  @[simp]
  theorem sub_eta {θ : Subst sig m (Nat.succ n)} :
    ext (θ ⨟ proj) (subst θ (ABT.var Fin2.fz)) = θ := by
      funext x
      cases x <;> simp [ext, subst, comp, ABT.map]

  @[simp]
  theorem wk_def {θ : Subst sig a b} :
    wk θ = ext (proj ⨟ θ) (ABT.var Fin2.fz)  := by
    funext x
    simp [wk, ext, proj, comp, Renaming.shift]
    cases x <;> simp [substOfRenaming]

  @[simp]
  theorem sub_tail {θ : Subst sig m n} {t : Term sig m} :
      ext θ t ⨟ proj = θ := by
      funext x
      cases x <;> aesop_cat


end Subst

-- def weaken (t : ABT sig n a) : ABT sig (n+1) a := by
--   cases t <;> try (constructor <;> aesop) <;> try (apply Fin2.fs)





end ABT
