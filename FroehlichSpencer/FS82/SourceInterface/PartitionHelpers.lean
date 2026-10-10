module
public import Mathlib
@[expose] public section
open MeasureTheory

/-- Summability and one strictly positive term give the unique positive
normalizer required by a discrete partition function. -/
theorem existsUnique_positive_hasSum_of_summable {α : Type*}
    (w : α → ℝ) (hw : ∀ a, 0 ≤ w a) (hs : Summable w)
    (hpos : ∃ a, 0 < w a) :
    ∃! Z : ℝ, HasSum w Z ∧ 0 < Z := by
  let Z : ℝ := ∑' a, w a
  obtain ⟨a, ha⟩ := hpos
  have hZsum : HasSum w Z := by
    exact hs.hasSum
  have hZpos : 0 < Z := by
    exact hs.tsum_pos hw a ha
  refine ⟨Z, ⟨hZsum, hZpos⟩, ?_⟩
  intro Z' hZ'
  exact hZ'.1.unique hZsum

/-- Characteristic functionals separate finite measures once they agree on
the full continuous dual. -/
theorem finiteMeasures_eq_of_charFunDual_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [CompleteSpace E] {μ ν : Measure E}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : charFunDual μ = charFunDual ν) : μ = ν :=
  Measure.ext_of_charFunDual h

end
