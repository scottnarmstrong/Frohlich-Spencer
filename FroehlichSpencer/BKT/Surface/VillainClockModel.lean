module
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Dirac.Def
public import Mathlib.MeasureTheory.Measure.WithDensity
public import FroehlichSpencer.BKT.Surface.ClockLaw
public import FroehlichSpencer.BKT.Surface.ClockCorrelation
public import FroehlichSpencer.BKT.Surface.FreeVillainLaw

@[expose] public section

open MeasureTheory

namespace FroehlichSpencer.BKT

/-- The free-boundary Villain law with every site restricted to the N clock atoms,
FS81 (1.26), (1.27), (7.2), Remark 4. -/
noncomputable def villainClockModel (N : ℕ) (_hN : 0 < N) (β : ℝ) (_hβ : 0 < β)
    (Λ : Finset (ℤ × ℤ)) : Measure (Λ → ℝ) :=
  let μ : Measure (Λ → ℝ) :=
    Measure.pi fun _ : Λ => ∑ k : Fin N, Measure.dirac (2 * Real.pi * (k : ℝ) / N)
  let w : (Λ → ℝ) → ℝ := fun θ =>
    ∏ b : Λ × Λ,
      (if (b.2 : ℤ × ℤ) = (b.1 : ℤ × ℤ) + (1, 0) ∨
          (b.2 : ℤ × ℤ) = (b.1 : ℤ × ℤ) + (0, 1) then
        (fun x : ℝ => ∑' m : ℤ, Real.exp (-(β / 2) * (x + 2 * Real.pi * m) ^ 2))
      else fun _ => 1) (θ b.1 - θ b.2)
  μ.withDensity fun θ => ENNReal.ofReal (w θ / ∫ θ, w θ ∂μ)

end FroehlichSpencer.BKT

end
