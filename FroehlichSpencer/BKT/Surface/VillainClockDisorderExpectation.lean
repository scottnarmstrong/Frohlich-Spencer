module
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import FroehlichSpencer.BKT.Surface.VillainClockModel
public import FroehlichSpencer.BKT.Surface.VillainClockDisorderObservable

@[expose] public section

open MeasureTheory

namespace FroehlichSpencer.BKT

/-- The finite free-square expectation of (1.32) in the Villain-constrained clock law. -/
noncomputable def villainClockDisorderExpectation (N : ℕ) (hN : 0 < N) (β : ℝ)
    (hβ : 0 < β) (ξ : ℝ) (L r : ℕ) (hL : 0 < L) (hr : r ≤ L) : ℝ :=
  let Λ := Finset.Icc (0 : ℤ) ((2 * L : ℕ) : ℤ) ×ˢ Finset.Icc (0 : ℤ) ((2 * L : ℕ) : ℤ)
  ∫ θ, villainClockDisorderObservable β hβ ξ L r Λ
    (fun m => by
      have hm := m.isLt
      dsimp [Λ]
      simp only [Finset.mem_product, Finset.mem_Icc]
      constructor <;> omega) θ
    ∂villainClockModel N hN β hβ Λ

end FroehlichSpencer.BKT

end
