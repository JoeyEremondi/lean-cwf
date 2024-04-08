import Mathlib.Data.Fin.Fin2

universe u v'

-- Loosely based off of Jeremy Siek's agda ABTs

inductive Sig : Type where
| plain : Sig
| bind : Sig → Sig

notation "◾" => Sig.plain
notation "ν" x => Sig.bind x

namespace ABT

mutual

    variable {Op : Type u} (sig : Op → List Sig)
    inductive ABT : Nat → Type u where
    | var : Fin2 n → ABT n
    | op : (op : Op) → Args n (sig op) → ABT n

    inductive Args : Nat →  List Sig → Type u where
    | nil : Args n []
    | cons :  Arg n h →  Args n t → Args n (h :: t)

    inductive Arg : Nat →  Sig → Type u where
    | plain : ABT n → Arg n ◾
    | bind : Arg (Nat.succ n) s → Arg n (ν s)

end

mutual
    def weaken : ABT sig n → ABT sig (n+1)
    | ABT.var x => ABT.var (Fin2.fs x)
    | ABT.op op args => _


    def weakenArgs : Args sig n ss → Args sig (n+1) ss
    | Args.nil => Args.nil
    | Args.cons h t => Args.cons (weakenArg h) (weakenArgs t)


    def weakenArg : Arg sig n s → Arg sig (n+1) s
    | Arg.plain t => Arg.plain (weaken t)
    | Arg.bind x => Arg.bind (weakenArg x)

end

abbrev Subst {Op : Type u} (sig : Op → List Sig) (m n : Nat) : Type u :=
  Fin2 n → ABT sig m

namespace Subst
  def id : Subst sig n n := fun x => ABT.var x

  def ext (f : Subst sig m n) (t : ABT sig m) : Subst sig m (Nat.succ n)
  | Fin2.fz => t
  | Fin2.fs x => f x

  def wkSub (θ : Subst sig m n) : Subst sig (m+1) n := fun x =>
    weaken (θ x)

end Subst

def subst


end ABT
