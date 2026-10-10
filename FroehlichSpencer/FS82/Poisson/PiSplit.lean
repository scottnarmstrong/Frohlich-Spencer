module
public import Mathlib.Logic.Equiv.Basic
public import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public section

namespace FroehlichSpencer.FS82.Poisson

noncomputable def piSumEquiv (n : ℕ) :
    ((Fin n ⊕ Fin 1) → ℤ) ≃ ((Fin n → ℤ) × ℤ) where
  toFun f := (fun i => f (Sum.inl i), f (Sum.inr 0))
  invFun p := Sum.elim p.1 (fun _ => p.2)
  left_inv f := by
    funext s
    cases s with
    | inl i => rfl
    | inr j => have hj : j = 0 := Subsingleton.elim _ _; subst j; rfl
  right_inv p := by
    cases p
    rfl

noncomputable def finSumPiEquiv (n : ℕ) : ((Fin n → ℤ) × ℤ) ≃ (Fin (n + 1) → ℤ) :=
  (piSumEquiv n).symm.trans
    (Equiv.piCongrLeft (fun _ : Fin (n + 1) => ℤ) (finSumFinEquiv : Fin n ⊕ Fin 1 ≃ Fin (n + 1)))

@[simp] theorem finSumPiEquiv_apply_castSucc (n : ℕ) (p : (Fin n → ℤ) × ℤ) (i : Fin n) :
    finSumPiEquiv n p (Fin.castSucc i) = p.1 i := by
  simp [finSumPiEquiv, piSumEquiv, Equiv.piCongrLeft_apply, finSumFinEquiv_symm_apply_castSucc]

@[simp] theorem finSumPiEquiv_apply_last (n : ℕ) (p : (Fin n → ℤ) × ℤ) :
    finSumPiEquiv n p (Fin.last n) = p.2 := by
  simp [finSumPiEquiv, piSumEquiv, Equiv.piCongrLeft_apply, finSumFinEquiv_symm_last]

end FroehlichSpencer.FS82.Poisson
