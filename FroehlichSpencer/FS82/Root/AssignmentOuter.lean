module

public import FroehlichSpencer.FS82.Root.SourceMoment
public import FroehlichSpencer.FS82.Poisson.PerAssignment

/-!
# FS82 (2.40): the source dual moment as an outer mixture over assignments

and write the tested expectation as `Ξ⁻¹ Σ_q a_q m_q(t)`, a countable
sum over link mode assignments `q` of the assignment coefficient `a_q` times
the finite co-closed chord-fiber moment `m_q = gaugeAssignmentMoment`
(`source_testedExpectation_eq_tsum_assignment`).

This module records the same
identity as a `HasSum` for the real source dual moment, which is the form the
outer hypothesis of `fs82_moment_comparison_of_expansion` takes once each
`m_q` is identified with a expansion system.

`Root/PhysicalOuter.lean`
rewrites each `m_q` as physical signed-pattern moment .
-/

@[expose] public section

open scoped BigOperators

namespace FroehlichSpencer.FS82.Root

open FroehlichSpencer.FS82
open FroehlichSpencer.FS82.Poisson
open FroehlichSpencer.FS82.Moment.SourceConstructor

noncomputable section

variable {B : Cubical.Box 4}

/--
/assignment outer sum, as a `HasSum` of the complex tested
expectation times `Ξ`.
-/
theorem sourceTested_hasSum_assignment {β : ℝ} (hβ : 0 < β)
    (τ : (sourceRootedTree B).Chord → ℝ) (t : ℝ)
    (z : ℕ → ℝ) (hnorm : HasSum (inactiveWeight z) 1)
    (hweight_nonneg : ∀ q, 0 ≤ inactiveWeight z q)
    (hz : ∀ q, 0 < z (positiveMode q)) :
    HasSum (fun q : SourcePoissonEdge B → ℕ =>
      (assignmentCoefficient z q : ℂ) *
        gaugeAssignmentMoment (sourceRootedTree B) (sourceChordMatrix (B := B) β)
          τ t z q)
      (sourceFiniteModelTestedExpectation (B := B) Cubical.originZero β τ t *
        (xi (sourceChordMatrix (B := B) β) : ℂ)) := by
  classical
  let T := sourceRootedTree B
  let A := sourceChordMatrix (B := B) β
  let w := realTiltParameter τ t
  have hA : A.PosDef := scaledChordMatrix_posDef _ _ hβ
  have hReg := gaugeCharacterRegroup_hasSum T A hA w z hnorm hweight_nonneg
  have hfactor (b : GaugeCharacterBranch T) :
      GaugeCharacterBranch.coefficient z b =
        assignmentCoefficient z (b.assignment) *
          GaugeCharacterBranch.assignmentRelativeCoefficient z b.assignment b := by
    have hc : assignmentCoefficient z b.assignment ≠ 0 :=
      ne_of_gt (assignmentCoefficient_pos z b.assignment hz)
    unfold GaugeCharacterBranch.assignmentRelativeCoefficient
    field_simp
  have hGrouped := hasSum_assignment_factor (GaugeCharacterBranch.assignment (T := T))
    (fun q => gaugeCharacterBranch_assignmentFiber_finite T q)
    (fun b => GaugeCharacterBranch.coefficient z b)
    (fun q => assignmentCoefficient z q)
    (GaugeCharacterBranch.assignmentRelativeCoefficient z)
    (fun b => dualQuadraticExp A w (T.restrictChord b.1.1)) _ hfactor hReg
  have hGrouped' : HasSum (fun q : SourcePoissonEdge B → ℕ =>
      (assignmentCoefficient z q : ℂ) * gaugeAssignmentMoment T A τ t z q)
      (∑' j : {j : SourcePoissonEdge B → ℤ // RootedTreeGauge.CoClosed T j},
        dualQuadraticExp A w (T.restrictChord j.1)) := by
    simpa [gaugeAssignmentMoment] using hGrouped
  have hEq := source_testedExpectation_eq_tsum_assignment (B := B)
    Cubical.originZero hβ τ t z hnorm hweight_nonneg hz
  have hxi : (xi A : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (xi_pos A hA).ne'
  convert hGrouped' using 1
  rw [hEq, div_mul_cancel₀ _ hxi]
  exact hGrouped'.tsum_eq

/-- **The outer assignment mixture of the source dual moment.**
`⟨e^{tα(μ)}⟩_Λ = Σ_q (a_q/Ξ) · Re m_q(t)`, as a `HasSum`. -/
theorem sourceDualMoment_hasSum_assignment {β : ℝ} (hβ : 0 < β)
    (z : ℕ → ℝ) (hnorm : HasSum (inactiveWeight z) 1)
    (hweight_nonneg : ∀ q, 0 ≤ inactiveWeight z q)
    (hz : ∀ q, 0 < z (positiveMode q)) (μ : SourceW B) (t : ℝ) :
    HasSum (fun q : SourcePoissonEdge B → ℕ =>
      assignmentCoefficient z q *
        (gaugeAssignmentMoment (sourceRootedTree B) (sourceChordMatrix (B := B) β)
          (sourceChordTest μ) t z q).re / xi (sourceChordMatrix (B := B) β))
      (sourceDualMoment β μ t) := by
  have hxi := xi_pos (sourceChordMatrix (B := B) β) (scaledChordMatrix_posDef _ _ hβ)
  have h := (Complex.hasSum_re (sourceTested_hasSum_assignment hβ (sourceChordTest μ)
    t z hnorm hweight_nonneg hz)).div_const (xi (sourceChordMatrix (B := B) β))
  rw [sourceFiniteModelTestedExpectation_eq_sourceDualMoment, ← Complex.ofReal_mul,
    Complex.ofReal_re, mul_div_assoc, div_self hxi.ne', mul_one] at h
  simpa only [Complex.re_ofReal_mul] using h

end

end FroehlichSpencer.FS82.Root
