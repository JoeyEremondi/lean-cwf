import Mathlib.Data.Fin.Fin2
instance finFunDecEq {n : ℕ} {A : Fin2 n → Type} [dec : ∀ i, DecidableEq (A i)] : DecidableEq ((i : Fin2 n) → A i) := by
    induction n with intros f g
    | zero =>
    apply isTrue
    funext
    contradiction
    | succ n IH =>
    cases dec _ (f Fin2.fz) (g Fin2.fz) with
    | isFalse npf =>
        apply isFalse
        intros pf
        have eq := congrFun pf (Fin2.fz)
        apply npf eq
    | isTrue hpf =>
        let ftail (x : Fin2 n) : A (Fin2.fs x) := f (Fin2.fs x)
        let gtail (x : Fin2 n) : A (Fin2.fs x) := g (Fin2.fs x)
        cases IH ftail gtail with
        | isTrue tpf =>
        simp [ftail, gtail] at hpf
        apply isTrue
        funext x
        cases x <;> try assumption
        apply congrFun tpf _
        | isFalse npf =>
        simp [ftail, gtail] at npf
        apply isFalse
        intros pf
        apply npf
        funext
        apply congrFun pf _

    instance finDec {n : ℕ} :  DecidableEq  (Fin2 n) := by
        intros x
        cases x with intros y <;> cases y <;> (try apply isTrue <;> aesop_cat) <;> (try apply isFalse <;> aesop_cat)
        | fs x  =>
        rename_i y
        cases finDec x y with
        | isFalse npf =>
            apply isFalse
            aesop_cat
        | isTrue pf => apply isTrue ; aesop_cat
