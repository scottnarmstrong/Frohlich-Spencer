module
public import Mathlib
@[expose] public section
open MeasureTheory

/-- A countable sum of normalized nonnegative point masses is a probability
measure as soon as the positive normalizer is the sum of its weights. -/
theorem normalizedCountableDirac_probability {α : Type*} [MeasurableSpace α]
    (w : α → ℝ) (Z : ℝ) (hZ : 0 < Z)
    (hw : ∀ a, 0 ≤ w a) (hsum : HasSum w Z) :
    IsProbabilityMeasure
      (Measure.sum fun a => ENNReal.ofReal (w a / Z) • Measure.dirac a) := by
  apply HasSum.isProbabilityMeasure_sum_dirac
  · intro a
    exact div_nonneg (hw a) hZ.le
  · simpa [hZ.ne'] using hsum.div_const Z

end
