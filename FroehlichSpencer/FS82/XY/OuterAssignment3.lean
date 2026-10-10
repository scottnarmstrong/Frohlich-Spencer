/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.XY.Poisson3
public import FroehlichSpencer.FS82.Poisson.PerAssignment

/-!
# the endpoint current sums as outer sums over mode assignments (D = 3)

The abstract character regrouping of §2 (`Poisson/GaugeCharacter.lean`,
`Poisson/PerAssignment.lean`) applies to the grounded dual complex's rooted tree and writes each of them as a countable
sum over link mode assignments of the finite co-closed chord-fiber moments, the 3D form of
FS82 (2.40) / (4.29)–(4.31).
-/

@[expose] public section

open scoped BigOperators

namespace FroehlichSpencer.FS82.XY

open FroehlichSpencer.FS82.Poisson

noncomputable section

variable {B : Dual3Box}

/-- The sum over integer co-closed currents is the sum over integer chord fields. -/
theorem xy3_tsum_coClosed_eq_tsum_chord (f : ((xyDual3RootedTree B).Chord → ℤ) → ℂ) :
    ∑' j : {j : Dual3Links B → ℤ // RootedTreeGauge.CoClosed (xyDual3RootedTree B) j},
        f ((xyDual3RootedTree B).restrictChord j.1) =
      ∑' k : (xyDual3RootedTree B).Chord → ℤ, f k := by
  rw [← (xyDual3ChordCurrentEquiv (B := B)).tsum_eq]
  refine tsum_congr fun k => ?_
  congr 1
  funext c
  simp [xyDual3ChordCurrentEquiv, RootedTreeGauge.circulationEquiv,
    RootedTreeGauge.cycleExtension, RootedTreeGauge.restrictChord]

/-- **The outer assignment sum in three dimensions.** For every chord test `τ` and real tilt
`t`, the tilted dual chord sum is the sum over link mode assignments `q` of the assignment
coefficient times the finite co-closed chord-fiber moment. -/
theorem xy3_chordSum_hasSum_assignment {β : ℝ} (hβ : 0 < β)
    (τ : (xyDual3RootedTree B).Chord → ℝ) (t : ℝ)
    (z : ℕ → ℝ) (hnorm : HasSum (inactiveWeight z) 1)
    (hweight_nonneg : ∀ q, 0 ≤ inactiveWeight z q)
    (hz : ∀ q, 0 < z (positiveMode q)) :
    HasSum (fun q : Dual3Links B → ℕ =>
      (assignmentCoefficient z q : ℂ) *
        gaugeAssignmentMoment (xyDual3RootedTree B) (xyDual3ChordMatrix (B := B) β) τ t z q)
      (∑' k : (xyDual3RootedTree B).Chord → ℤ,
        dualQuadraticExp (xyDual3ChordMatrix (B := B) β) (realTiltParameter τ t) k) := by
  classical
  let T := xyDual3RootedTree B
  let A := xyDual3ChordMatrix (B := B) β
  let w := realTiltParameter τ t
  have hA : A.PosDef := xyDual3ChordMatrix_posDef hβ
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
  have hGrouped' : HasSum (fun q : Dual3Links B → ℕ =>
      (assignmentCoefficient z q : ℂ) * gaugeAssignmentMoment T A τ t z q)
      (∑' j : {j : Dual3Links B → ℤ // RootedTreeGauge.CoClosed T j},
        dualQuadraticExp A w (T.restrictChord j.1)) := by
    simpa [gaugeAssignmentMoment] using hGrouped
  rw [← xy3_tsum_coClosed_eq_tsum_chord (fun k => dualQuadraticExp A w k)]
  exact hGrouped'

end

end FroehlichSpencer.FS82.XY

end
