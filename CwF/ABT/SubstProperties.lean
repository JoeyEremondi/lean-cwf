
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
    simp [ofRenaming, Renaming.wk, wk, Renaming.weaken, Renaming.rename]
    cases x <;> simp [Fin2.add]

  -- @[simp]
  theorem substOfRenaming {t : ABT sig n a} : {m : ℕ} →  {ρ : Renaming m n}
      → Renaming.rename ρ t = subst (ofRenaming ρ) t := by
    induction t
      <;> intros m ρ
      <;> simp only [subst, Renaming.rename, Renaming.wk, wk, ofRenaming ]
      <;> aesop

  @[simp]
  theorem wk_id : wk (sig := sig) (n := n) id = id := by
    funext x
    simp only [wk, id, Renaming.weaken]
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
     cases x with try aesop_cat
     | fs x =>
        dsimp only [comp, wk, Renaming.weaken, ofRenaming,subst]
        rw [Renaming.rename]
        simp [subst, Fin2.add, wk]
        rw [Renaming.weaken]
        rfl

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
   induction t <;> intros a b ρ θ <;> simp [subst, Renaming.rename] <;> try aesop_cat

  @[simp]
  theorem sub_rename_fusionR {t : ABT sig c tag} : ∀ {a} {b} {ρ : Renaming a b} {θ : Subst sig b c},
    t⦇ θ ⦈⦇ ρ ⦈ᵣ = t⦇  ofRenaming ρ ⨟ θ ⦈ := by
   induction t <;> intros a b ρ θ <;> simp [subst, Renaming.rename] <;> try aesop_cat
   simp [comp, substOfRenaming]



  @[simp]
  theorem wk_comp
    {θ : Subst sig a b}  {θ2 : Subst sig b c}
    :  (wk θ ) ⨟ (wk θ2) = wk (θ ⨟ θ2) := by
    funext x

    let helper : (wk θ⨟ofRenaming fun x => Fin2.add x 1) = ((ofRenaming fun x => Fin2.add x 1) ⨟ θ) := by
      funext x
      dsimp only [comp, ofRenaming, subst]
      simp [<- substOfRenaming, Fin2.add]
      simp [ wk, Renaming.weaken, Fin2.add]

    cases x with simp [wk, comp] <;> try aesop_cat
    | fs x =>
      calc (Renaming.weaken 1 (θ2 x))⦇wk θ⦈
        = (θ2 x)⦇ (fun x => Fin2.add x 1) ⦈ᵣ⦇wk θ⦈ := by simp [Renaming.weaken]
      _ = (θ2 x)⦇wk θ⨟ofRenaming fun x => Fin2.add x 1⦈ := by simp
      _ = ((θ2 x))⦇θ⦈⦇ (fun x => Fin2.add x 1) ⦈ᵣ := by simp [helper]
      _ = Renaming.weaken 1 (θ2 x)⦇θ⦈ := by simp [Renaming.weaken]

  def wkOne_subst_commut {n : ℕ} : ∀ {sig : Op → List Sig}, ∀ {t : ABT sig b tag}  {θ : Subst sig a b},
    Renaming.weaken 1 t⦇θ⦈ = (Renaming.weaken 1 t)⦇wk θ⦈ := by
      intros sig t
      induction t <;> intros θ <;> simp [Renaming.weaken, Renaming.rename] <;> try aesop_cat
      simp [Renaming.rename_comp]

  def wk_subst_commut'  {t : ABT sig b tag}  : ∀ {a} {n} {θ : Subst sig a b},
    Renaming.weaken n t⦇θ⦈ = (Renaming.weaken n t)⦇wkN n θ⦈ := by
    induction t with intros a n θ <;> try (simp [subst, Renaming.rename, Renaming.weaken] <;> aesop_cat)
    | var x => admit
    | bind xt IH =>
      simp [subst, Renaming.rename, Renaming.weaken, Renaming.wk]
      simp [subst, Renaming.rename, Renaming.weaken] at IH
      let helper := IH (n := Nat.succ n) (θ := wk θ)

  def wk_subst_commut {n : ℕ} : ∀ {sig : Op → List Sig}, ∀ {t : ABT sig b tag}  {θ : Subst sig a b},
    Renaming.weaken n t⦇θ⦈ = (Renaming.weaken n t)⦇wkN n θ⦈ := by
      induction n with intros sig t <;> try (simp [Renaming.weaken, Fin2.add, wkN, Renaming.id_def] <;>  aesop_cat)
        | succ n' nIH =>
          generalize eq : (Nat.succ n') = n at *
          induction t with intros θ <;> try (simp [subst, Renaming.rename, Renaming.weaken] <;> aesop_cat)
          | op t IH => apply IH

        -- | var x =>
        --   induction n with
        --   | zero =>
        --     simp [Renaming.weaken, subst, Fin2.add, Renaming.id_def, wkN]
        --   | succ n IH =>
        --     simp [subst] at IH
        --     rw [Renaming.weaken_succ]
        --     simp [subst]
        -- | bind t IH => simp
      -- induction n with intros sig t <;> try (simp [Renaming.weaken, Fin2.add, wkN, Renaming.id_def] <;>  aesop_cat)
      --   | succ n nIH =>
      --   intros θ
      --   let eq1 := Renaming.weaken_succ (n := n) (t := t)
      --   let eq2  :=  Renaming.weaken_succ (n := n) (t := t⦇θ⦈)
      --   simp [eq1, eq2, nIH]
      --   -- generalize θ
      --   induction t <;> intros θ <;> let eq := eq2 θ <;> simp [eq1, eq, nIH, subst, Renaming.rename] <;> try rw [nIH] <;> try aesop_cat


      -- | succ n =>
      --   induction t <;> intros θ <;> simp [Renaming.weaken, wk, subst] <;> try aesop_cat


  @[simp]
  theorem weakenAsSubst {t : ABT sig n ty} : Renaming.weaken m t = t⦇projN m⦈ := by simp [Renaming.weaken, projN]

  @[simp]
  theorem ofRenameId : ofRenaming (sig := sig) (n := n) Renaming.id = id := by
    funext x
    simp [ofRenaming, Renaming.id, id]

  @[simp]
  theorem ofRenameIdDef : ofRenaming (sig := sig) (n := n) (fun x => x) = id := by
    funext x
    simp [ofRenaming, Renaming.id, id]


  theorem wkN_proj {n : ℕ} : ∀ {tag} (t : ABT sig b tag), t⦇projN n⦈  = (weaken t)⦇wkN n θ⦈ := by
  
  theorem wkN_rename_comp {n : ℕ} : ∀ {tag} (t : ABT sig b tag), ∀ {a}, {θ : Subst sig a b} →  t⦇θ⦈⦇projN n⦈  = t⦇projN n⦈⦇wkN n θ⦈ := by
    induction n with
    | zero => simp [wkN, projN, Fin2.add]
    | succ n' nIH =>
      intros tag t
      induction t with intros a θ <;>  simp [subst, Fin2.add]  <;> try aesop_cat
      | var x =>
        simp [wkOne, wk, projN]
        unfold ofRenaming
        simp
        simp [projN, wk, wkN]
        apply nIH
      | bind xt IH => simp
      -- | var x  =>
      --   let lem : wk (wkN n' θ) = wkN (Nat.succ n') θ := by simp [wkN]
      --   rw [<- lem]


      -- | bind t IH => simp




  theorem wk_def {θ : Subst sig a b} :
    wk θ = ext (proj ⨟ θ) (ABT.var Fin2.fz)  := by
    funext x
    simp [wk, ext, proj, comp, Renaming.weaken]


  theorem projWk {θ : Subst sig m n} : θ ⨟ proj  = proj ⨟ (wk θ) := by
    funext x

      -- simp [wk_def, ext]



  --Category and CwF
  --CwF laws for substitutions
  --It turns out these make a terminating rewrite system
  @[simp]
  theorem sub_comp {t : ABT sig c tag} : ∀ {a} {b}, {θ : Subst sig a b} →  {θ2 : Subst sig b c} →
    subst θ (subst θ2 t) = subst (θ ⨟ θ2) t := by
    induction t with
      intros θ θ2
      <;> simp only [subst, Renaming.rename, Renaming.wk, wk, ofRenaming ]
      <;> try aesop_cat
    -- | bind _ IH =>
    --   intros θ θ2
    --   apply congrArg ABT.bind
    --   let lem : wk (θ ⨟ θ2) = (wk θ ) ⨟ (wk θ2) := by
    --     funext x
    --     simp only [wk, comp]
    --     cases x <;> try aesop_cat
    --     simp [Renaming.weaken]
    --     apply @IH _ _
    --   rw [lem]
    --   apply @IH _ _  (wk θ) (wk θ2)
    -- rw [lem]


  --
  --
  theorem comp_idL (θ : Subst sig m n) :
    θ ⨟ id = θ := by
    funext
    aesop

  theorem comp_idR (θ : Subst sig m n) :
    id ⨟ θ = θ := by
    funext
    simp [comp]

  theorem comp_assoc (θ1 : Subst sig a b) (θ2 : Subst sig b c) (θ3 : Subst sig c d)
    : (θ1 ⨟ θ2) ⨟ θ3 = θ1 ⨟ (θ2 ⨟ θ3) := by
    funext x
    simp [comp]

end Subst

-- def weaken (t : ABT sig n a) : ABT sig (n+1) a := by
--   cases t <;> try (constructor <;> aesop) <;> try (apply Fin2.fs)





def subst


end ABT
