module

public import FroehlichSpencer.FS82.Root.AssignmentOuter
public import FroehlichSpencer.FS82.Moment.PhysicalChordIdentity

/-!
# FS82 (2.40), (2.97): the source dual moment over physical assignment moments

identifies each chord-fiber assignment moment `gaugeAssignmentMoment` with
physical signed-pattern moment `sourceAssignmentGaussianMoment` under the
gauge-averaged Gaussian.

Combined with `sourceDualMoment_hasSum_assignment`,
the source observable is a countable mixture of these physical moments.
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
**The source dual moment as an outer mixture of physical assignment
moments.** By , each chord-fiber moment is physical signed-pattern
moment under the gauge-averaged Gaussian:
`⟨e^{tα(μ)}⟩_Λ = Σ_q (a_q/Ξ) · Re M_q(t)`.
-/
theorem sourceDualMoment_hasSum_physicalAssignment {β : ℝ} (hβ : 0 < β)
    (z : ℕ → ℝ) (hnorm : HasSum (inactiveWeight z) 1)
    (hweight_nonneg : ∀ q, 0 ≤ inactiveWeight z q)
    (hz : ∀ q, 0 < z (positiveMode q)) (μ : SourceW B) (t : ℝ) :
    HasSum (fun q : SourcePoissonEdge B → ℕ =>
      assignmentCoefficient z q *
        (Moment.ExpansionIntegral.sourceAssignmentGaussianMoment β hβ.le t μ q z).re /
          xi (sourceChordMatrix (B := B) β))
      (sourceDualMoment β μ t) := by
  have hq : ∀ q : SourcePoissonEdge B → ℕ,
      Moment.ExpansionIntegral.sourceAssignmentGaussianMoment β hβ.le t μ q z =
        gaugeAssignmentMoment (sourceRootedTree B) (sourceChordMatrix (B := B) β)
          (sourceChordTest μ) t z q :=
    fun q => Moment.PhysicalChordIdentity.sourceAssignmentGaussianMoment_eq_gaugeAssignmentMoment
      β hβ t μ q z hz
  simp only [hq]
  exact sourceDualMoment_hasSum_assignment hβ z hnorm hweight_nonneg hz μ t

end

end FroehlichSpencer.FS82.Root
