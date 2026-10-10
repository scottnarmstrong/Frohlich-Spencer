/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.XY.DualFieldD
public import FroehlichSpencer.FS82.XY.ExpansionRelationD
import all FroehlichSpencer.FS82.XY.CurrentExpansionD

/-!
# the Gaussian form of a separated current state, `d ≥ 3`

The dimension-generic form of `XY/Branch3.lean`.

For a terminal state `s` of the expansion with
the base-near relation, the gauge-averaged integral of its cosine product, with the field
translated by `shift`, is the integral of
`∏_l (1 + amp_l cos(y_l + ⟨shift, J_l⟩))` against a centred Gaussian `N(0, R)`:

* lineages whose current is not co-closed drop out (`DualD.coClosed_of_separated_sum`), so
  `J_l = stateCurrentD` is the lineage current or zero, and `stateActivityD` its coefficient or
  zero;
* `amp_l = stateAmpD = stateActivityD · exp(−lineageGain/2)`;
* `R = stateCovarianceD` is positive semidefinite (`DualD.family_gain_le`).
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

@[expose] public section

namespace FroehlichSpencer.FS82.XY.DualD

open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Gaussian
open FroehlichSpencer.FS82.Currents
open FroehlichSpencer.FS82.XY.GaugeAverage
open FroehlichSpencer.FS82.XY.ExpansionD.Generic
open FroehlichSpencer.FS82.Gaussian.RenormalizedFamily.RenormalizedCharacters

variable {d : ℕ} {B : Box d}

/-- The lineages of a current state: the index of its Gaussian. -/
abbrev StateIndexD (s : Finset (ActivityLineage (DualDForm B (d - 2)))) := {l // l ∈ s}

/-- The current of a lineage of a state, zero if it is not co-closed. -/
noncomputable def stateCurrentD (q : DualDForm B (d - 2) → ℤ)
    (s : Finset (ActivityLineage (DualDForm B (d - 2)))) (i : StateIndexD s) :
    DualDForm B (d - 2) → ℤ :=
  closedCurrentD stencilInt (lineageCurrent q i.1)

/-- The activity of a lineage of a state, zero if its current is not co-closed. -/
noncomputable def stateActivityD (q : DualDForm B (d - 2) → ℤ) (z : ℤ → ℝ)
    (s : Finset (ActivityLineage (DualDForm B (d - 2)))) (i : StateIndexD s) : ℝ :=
  closedActivityD stencilInt (lineageCoefficient q z i.1) (lineageCurrent q i.1)

/-- The renormalized amplitude of a lineage of a state. -/
noncomputable def stateAmpD (β : ℝ) (q : DualDForm B (d - 2) → ℤ) (z : ℤ → ℝ)
    (s : Finset (ActivityLineage (DualDForm B (d - 2)))) (i : StateIndexD s) : ℝ :=
  stateActivityD q z s i * Real.exp (-(lineageGain d β (stateCurrentD q s i) / 2))

/-- The covariance of the renormalized angles of a state. -/
noncomputable def stateCovarianceD (hd : 3 ≤ d) (β : ℝ) (q : DualDForm B (d - 2) → ℤ)
    (s : Finset (ActivityLineage (DualDForm B (d - 2)))) :
    Matrix (StateIndexD s) (StateIndexD s) ℝ :=
  branchCovarianceD (dualCovariance hd B β) (stateCurrentD q s)
    fun i => lineageGain d β (stateCurrentD q s i)

/-- The gauge-averaged integral of the cosine product of a state, with the field translated by
`shift`. -/
noncomputable def stateIntegralD (hd : 3 ≤ d) (β : ℝ) (q : DualDForm B (d - 2) → ℤ)
    (z : ℤ → ℝ) (s : Finset (ActivityLineage (DualDForm B (d - 2))))
    (shift : DualDForm B (d - 2) → ℝ) : ℝ :=
  ∫ ω, ExpansionD.Generic.currentStateProduct q z
      (fun e => gaugeFieldD stencilInt ω e + shift e) s
    ∂gaugeMeasureD (DualDForm B (d - 3)) (dualCovariance hd B β)

theorem stateCurrentD_coClosed (hd : 3 ≤ d) (q : DualDForm B (d - 2) → ℤ)
    (s : Finset (ActivityLineage (DualDForm B (d - 2)))) (i : StateIndexD s) :
    currentVector (stateCurrentD q s i) ∈ coClosed (dualDExactOneComplex hd B) :=
  (closedD_stencilInt_iff hd _).mp (closedCurrentD_closed _ _)

theorem stateCurrentD_ne_zero_imp {q : DualDForm B (d - 2) → ℤ}
    {s : Finset (ActivityLineage (DualDForm B (d - 2)))} {i : StateIndexD s}
    {e : DualDForm B (d - 2)} (h : stateCurrentD q s i e ≠ 0) :
    lineageCurrent q i.1 e ≠ 0 ∧ stateCurrentD q s i = lineageCurrent q i.1 := by
  obtain ⟨h1, h2⟩ := closedCurrentD_ne_zero_imp h
  exact ⟨h1, closedCurrentD_of_closed h2⟩

theorem stateCurrentD_separated {q : DualDForm B (d - 2) → ℤ}
    {s : Finset (ActivityLineage (DualDForm B (d - 2)))}
    (hs : IsSeparatedCurrentState (baseNearRelation B (d - 2)) q s) (i j : StateIndexD s)
    (hij : i ≠ j) (e f : DualDForm B (d - 2)) (he : stateCurrentD q s i e ≠ 0)
    (hf : stateCurrentD q s j f ≠ 0) : ¬ cellBaseNear e.1 f.1 :=
  hs i.1 i.2 j.1 j.2 (fun h => hij (Subtype.ext h)) e
    (mem_currentSupport_iff.mpr (stateCurrentD_ne_zero_imp he).1) f
    (mem_currentSupport_iff.mpr (stateCurrentD_ne_zero_imp hf).1)

theorem stateCurrentD_disjoint {q : DualDForm B (d - 2) → ℤ}
    {s : Finset (ActivityLineage (DualDForm B (d - 2)))}
    (hs : IsSeparatedCurrentState (baseNearRelation B (d - 2)) q s) (i j : StateIndexD s)
    (hij : i ≠ j) (e : DualDForm B (d - 2)) (he : stateCurrentD q s i e ≠ 0) :
    stateCurrentD q s j e = 0 := by
  by_contra hf
  exact stateCurrentD_separated hs i j hij e e he hf (cellBaseNear_refl e.1)

theorem stateCovarianceD_posSemidef (hd : 3 ≤ d) {β : ℝ} (hβ : 0 ≤ β)
    {q : DualDForm B (d - 2) → ℤ} {s : Finset (ActivityLineage (DualDForm B (d - 2)))}
    (hs : IsSeparatedCurrentState (baseNearRelation B (d - 2)) q s) :
    (stateCovarianceD hd β q s).PosSemidef :=
  family_branchCovarianceD_posSemidef hd hβ _ (stateCurrentD_coClosed hd q s)
    (stateCurrentD_disjoint hs)

/-- **The renormalized identity for a separated current state.** -/
theorem stateIntegralD_eq_gaussian (hd : 3 ≤ d) {β : ℝ} (hβ : 0 ≤ β)
    (q : DualDForm B (d - 2) → ℤ) (z : ℤ → ℝ)
    (s : Finset (ActivityLineage (DualDForm B (d - 2))))
    (hs : IsSeparatedCurrentState (baseNearRelation B (d - 2)) q s)
    (shift : DualDForm B (d - 2) → ℝ) :
    stateIntegralD hd β q z s shift =
      ∫ y : EuclideanSpace ℝ (StateIndexD s),
        ∏ i, (1 + stateAmpD β q z s i *
          Real.cos (y i + linkPairing shift (stateCurrentD q s i)))
        ∂multivariateGaussian 0 (stateCovarianceD hd β q s) := by
  classical
  have hS := dualCovariance_posSemidef hd B hβ
  have hraw : ∀ ω : EuclideanSpace ℝ (DualDForm B (d - 2)) × (DualDForm B (d - 3) → ℝ),
      ExpansionD.Generic.currentStateProduct q z
          (fun e => gaugeFieldD stencilInt ω e + shift e) s =
        ∏ i : StateIndexD s, (1 + lineageCoefficient q z i.1 *
          Real.cos (linkPairing (gaugeFieldD stencilInt ω) (lineageCurrent q i.1) +
            linkPairing shift (lineageCurrent q i.1))) := by
    intro ω
    unfold ExpansionD.Generic.currentStateProduct ExpansionD.Generic.currentFactor
    rw [← Finset.prod_coe_sort]
    refine Finset.prod_congr rfl fun i _ => ?_
    congr 3
    unfold ExpansionD.Generic.currentPhase linkPairing
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun e _ => by ring
  unfold stateIntegralD
  simp_rw [hraw]
  rw [integral_cosineProduct_eq_closedD stencilInt hS
    (fun i : StateIndexD s => lineageCoefficient q z i.1)
    (fun i : StateIndexD s => lineageCurrent q i.1) shift
    (fun σ hsum i hi => by
      rw [closedD_stencilInt_iff hd] at hsum ⊢
      refine coClosed_of_separated_sum hd (fun i : StateIndexD s => lineageCurrent q i.1)
        (fun i => signZ (σ i))
        (fun a b hab e f he hf => hs a.1 a.2 b.1 b.2 (fun h => hab (Subtype.ext h)) e
          (mem_currentSupport_iff.mpr he) f (mem_currentSupport_iff.mpr hf))
        hsum i ?_
      exact fun h0 => hi ((signZ_eq_zero_iff (σ i)).mp h0))]
  exact branch_integral_eq_gaussianD stencilInt hS (stateActivityD q z s)
    (fun i => linkPairing shift (stateCurrentD q s i))
    (fun i => lineageGain d β (stateCurrentD q s i)) (stateCurrentD q s)
    (fun _ => closedCurrentD_closed _ _) (stateCovarianceD_posSemidef hd hβ hs)

end FroehlichSpencer.FS82.XY.DualD

end
