module
public import Mathlib
public import FroehlichSpencer.BKT.Surface.VillainClock.LatticeAngle

@[expose] public section

open MeasureTheory

noncomputable section

namespace FroehlichSpencer.BKT.Surface.VillainClock

/-- Literal finite-volume Villain two-point correlation: the normalized integral of the
cosine character against the positive-direction bond product in (1.26)–(1.27). -/
noncomputable def villainContinuousCorrelation (β : ℝ) (_hβ : 0 < β) (ξ : ℤ)
    (Λ : Finset (ℤ × ℤ)) (u v : ℤ × ℤ) : ℝ :=
  let μ : Measure (Λ → ℝ) :=
    Measure.pi fun _ : Λ => volume.restrict (Set.Ico (-Real.pi) Real.pi)
  let w : (Λ → ℝ) → ℝ := fun θ =>
    ∏ b : Λ × Λ,
      (if (b.2 : ℤ × ℤ) = (b.1 : ℤ × ℤ) + (1, 0) ∨
          (b.2 : ℤ × ℤ) = (b.1 : ℤ × ℤ) + (0, 1) then
        (fun x : ℝ => ∑' m : ℤ, Real.exp (-(β / 2) * (x + 2 * Real.pi * m) ^ 2))
      else fun _ => 1) (θ b.1 - θ b.2)
  (∫ θ, Real.cos (ξ *
      (latticeAngleLiteral θ u - latticeAngleLiteral θ v)) * w θ ∂μ) /
    ∫ θ, w θ ∂μ

end FroehlichSpencer.BKT.Surface.VillainClock
