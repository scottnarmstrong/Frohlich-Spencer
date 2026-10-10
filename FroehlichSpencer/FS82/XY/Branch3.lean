/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.XY.ClosedLineage3
public import FroehlichSpencer.FS82.XY.LocalEnergy3

/-!
# the renormalized Gaussian form of a terminal branch in three dimensions

For a separated current state, the gauge-averaged integral of its cosine product, with the link
field translated by a real field `shift`, equals the integral of

`∏ (1 + amp_l cos(y_l + ⟨shift, J_l⟩))`

against a centred Gaussian on the lineages of the state.

This is FS82 (4.36).

* `familyGain`, `family_gain_le_chordBilinear`: the gains of a separated family and the local
  lower bound that makes the renormalized covariance positive semidefinite.
* `family_integral_eq_gaussian`: the identity for a separated co-closed family.
* `stateIntegral_eq_gaussian`: the identity for a separated current state.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

@[expose] public section

namespace FroehlichSpencer.FS82.XY

open FroehlichSpencer.FS82.Gaussian
open FroehlichSpencer.FS82.Gaussian.ConditionalGaussian
open FroehlichSpencer.FS82.Poisson
open FroehlichSpencer.FS82.XY.Expansion3
open FroehlichSpencer.FS82.XY.Renormalization3
open FroehlichSpencer.FS82.XY.GaugeAverage

variable {B : Dual3Box}

section Family

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The gain of current `i` of a family: `(2π)²β` times the mass of its selected block, each
link weighted by the inverse number of its plaquettes. -/
noncomputable def familyGain (β : ℝ) (J : ι → Dual3Links B → ℤ) (i : ι) : ℝ :=
  (2 * Real.pi) ^ 2 * β *
    ∑ b ∈ selectedFamilyBlock (fun i e => (J i e : ℝ)) i,
      ((J i b : ℤ) : ℝ) ^ 2 / linkMass (dual3ChartIncidence (B := B)) b


omit [Fintype ι] [DecidableEq ι] in
theorem family_realSeparated (J : ι → Dual3Links B → ℤ)
    (hsep : ∀ i j, i ≠ j → ∀ e f, J i e ≠ 0 → J j f ≠ 0 → ¬ Expansion3.currentNear e f) :
    ∀ i j, i ≠ j → ∀ e ∈ familyCurrentSupport (fun i e => (J i e : ℝ)) i,
      ∀ f ∈ familyCurrentSupport (fun i e => (J i e : ℝ)) j, ¬ Expansion3.currentNear e f := by
  intro i j hij e he f hf
  exact hsep i j hij e f (fun h0 => (Finset.mem_filter.mp he).2 (by simp [h0]))
    (fun h0 => (Finset.mem_filter.mp hf).2 (by simp [h0]))

/-- **The local lower bound for a separated co-closed family.** -/
theorem family_gain_le_chordBilinear {β : ℝ} (hβ : 0 < β) (J : ι → Dual3Links B → ℤ)
    (hJ : ∀ i, RootedTreeGauge.CoClosed (xyDual3RootedTree B) (J i))
    (hsep : ∀ i j, i ≠ j → ∀ e f, J i e ≠ 0 → J j f ≠ 0 → ¬ Expansion3.currentNear e f)
    (s : ι → ℝ) :
    ∑ i, s i ^ 2 * familyGain β J i ≤
      2 * Real.pi * chordBilinear (xyDual3RootedTree B) (xyDual3ChordMatrix (B := B) β)
        (∑ i, s i • chordVector (xyDual3RootedTree B) (J i))
        (∑ i, s i • chordVector (xyDual3RootedTree B) (J i)) := by
  classical
  set ρ : ι → Dual3Links B → ℝ := fun i e => (J i e : ℝ) with hρ
  have hsep' := family_realSeparated J hsep
  let μ : coClosed (dual3ExactOneComplex B) :=
    ⟨∑ i, s i • currentVector (J i), Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (currentVector_mem_coClosed (hJ i))⟩
  have hμapply : ∀ b, μ.1 b = ∑ i, s i * ρ i b := by
    intro b
    simp [μ, currentVector, ρ, Finset.sum_apply]
  have hchord : (xyDual3RootedTree B).restrictChord μ.1.ofLp =
      ∑ i, s i • chordVector (xyDual3RootedTree B) (J i) := by
    funext c
    have := hμapply c.1
    simp only [RootedTreeGauge.restrictChord, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      chordVector]
    exact this
  have hbridge := chordBilinear_restrictChord_eq hβ μ
  rw [hchord] at hbridge
  have hLLB := dual3_selectedEnergy_le_covarianceQuadratic μ (selectedFamilyDomain ρ)
    (selectedFamily_chartBlocks_independent ρ hsep')
  obtain ⟨hdisj, hcross⟩ := selectedFamily_blocks_disjoint_and_crossZero ρ hsep'
  have hsum : ∑ b ∈ selectedFamilyDomain ρ,
      (μ.1 b) ^ 2 / linkMass (dual3ChartIncidence (B := B)) b =
      ∑ i, ∑ b ∈ selectedFamilyBlock ρ i,
        (s i * ρ i b) ^ 2 / linkMass (dual3ChartIncidence (B := B)) b := by
    unfold selectedFamilyDomain
    rw [Finset.sum_biUnion (fun i _ j _ hij => hdisj i j hij)]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun b hb => ?_
    rw [hμapply b, Finset.sum_eq_single i (fun j _ hji => by
      rw [hcross i j b (Ne.symm hji) hb, mul_zero]) (fun h => absurd (Finset.mem_univ i) h)]
  have hgain : ∑ i, s i ^ 2 * familyGain β J i =
      (2 * Real.pi) ^ 2 * β * ∑ b ∈ selectedFamilyDomain ρ,
        (μ.1 b) ^ 2 / linkMass (dual3ChartIncidence (B := B)) b := by
    rw [hsum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    unfold familyGain
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [ρ]
    ring
  rw [hgain, hbridge]
  have hpos : 0 ≤ (2 * Real.pi) ^ 2 * β := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hLLB hpos]

/-- The renormalized covariance of a separated co-closed family is positive semidefinite. -/
theorem family_branchCovariance_posSemidef {β : ℝ} (hβ : 0 < β) (J : ι → Dual3Links B → ℤ)
    (hJ : ∀ i, RootedTreeGauge.CoClosed (xyDual3RootedTree B) (J i))
    (hsep : ∀ i j, i ≠ j → ∀ e f, J i e ≠ 0 → J j f ≠ 0 → ¬ Expansion3.currentNear e f) :
    (branchCovariance (xyDual3RootedTree B) (xyDual3ChordMatrix (B := B) β) J
      (familyGain β J)).PosSemidef :=
  branchCovariance_posSemidef _ (xyDual3ChordMatrix_posDef hβ) J _
    (family_gain_le_chordBilinear hβ J hJ hsep)

/-- The renormalized amplitude of current `i`. -/
noncomputable def familyAmp (β : ℝ) (K : ι → ℝ) (J : ι → Dual3Links B → ℤ) (i : ι) : ℝ :=
  K i * Real.exp (-(familyGain β J i / 2))

/-- **The renormalized identity for a separated co-closed family.** -/
theorem family_integral_eq_gaussian {β : ℝ} (hβ : 0 < β) (K θ : ι → ℝ)
    (J : ι → Dual3Links B → ℤ)
    (hJ : ∀ i, RootedTreeGauge.CoClosed (xyDual3RootedTree B) (J i))
    (hsep : ∀ i j, i ≠ j → ∀ e f, J i e ≠ 0 → J j f ≠ 0 → ¬ Expansion3.currentNear e f) :
    ∫ ω, ∏ i, (1 + K i * Real.cos (linkPairing (gaugeField (xyDual3RootedTree B) ω) (J i) +
        θ i)) ∂gaugeMeasure (xyDual3RootedTree B) (xyDual3ChordMatrix (B := B) β) =
      ∫ y : EuclideanSpace ℝ ι, ∏ i, (1 + familyAmp β K J i * Real.cos (y i + θ i))
        ∂multivariateGaussian 0 (branchCovariance (xyDual3RootedTree B)
          (xyDual3ChordMatrix (B := B) β) J (familyGain β J)) :=
  branch_integral_eq_gaussian _ (xyDual3ChordMatrix_posDef hβ) K θ (familyGain β J) J hJ
    (family_branchCovariance_posSemidef hβ J hJ hsep)

end Family

/-! ## Current states -/

/-- The lineages of a current state: the index of its Gaussian. -/
abbrev StateIndex (s : CurrentState B) := {l : ExpansionLineage B // l ∈ s}

/-- The current of a lineage of a state, zero if it is not co-closed. -/
noncomputable def stateCurrent (q : Dual3Links B → ℤ) (s : CurrentState B)
    (i : StateIndex s) : Dual3Links B → ℤ := closedCurrent (lineageCurrent q i.1)

/-- The activity of a lineage of a state, zero if its current is not co-closed. -/
noncomputable def stateActivity (q : Dual3Links B → ℤ) (z : ℤ → ℝ) (s : CurrentState B)
    (i : StateIndex s) : ℝ :=
  closedActivity (lineageCoefficient q z i.1) (lineageCurrent q i.1)

/-- The renormalized amplitude of a lineage of a state. -/
noncomputable def stateAmp (β : ℝ) (q : Dual3Links B → ℤ) (z : ℤ → ℝ) (s : CurrentState B)
    (i : StateIndex s) : ℝ :=
  familyAmp β (stateActivity q z s) (stateCurrent q s) i

/-- The covariance of the renormalized angles of a state. -/
noncomputable def stateCovariance (β : ℝ) (q : Dual3Links B → ℤ) (s : CurrentState B) :
    Matrix (StateIndex s) (StateIndex s) ℝ :=
  branchCovariance (xyDual3RootedTree B) (xyDual3ChordMatrix (B := B) β) (stateCurrent q s)
    (familyGain β (stateCurrent q s))

/-- The gauge-averaged integral of the cosine product of a state, with the link field translated
by `shift`. -/
noncomputable def stateIntegral (β : ℝ) (q : Dual3Links B → ℤ) (z : ℤ → ℝ)
    (s : CurrentState B) (shift : Dual3Links B → ℝ) : ℝ :=
  ∫ ω, currentStateProduct q z (fun e => gaugeField (xyDual3RootedTree B) ω e + shift e) s
    ∂gaugeMeasure (xyDual3RootedTree B) (xyDual3ChordMatrix (B := B) β)

theorem stateCurrent_separated {q : Dual3Links B → ℤ} {s : CurrentState B}
    (hs : IsSeparatedCurrentState q s) :
    ∀ i j : StateIndex s, i ≠ j → ∀ e f, stateCurrent q s i e ≠ 0 → stateCurrent q s j f ≠ 0 →
      ¬ Expansion3.currentNear e f := by
  intro i j hij e f he hf
  exact xy3_lineage_currentNear_separated hs i.2 j.2 (fun h => hij (Subtype.ext h)) e f
    (closedCurrent_ne_zero_imp he) (closedCurrent_ne_zero_imp hf)

theorem stateCovariance_posSemidef {β : ℝ} (hβ : 0 < β) {q : Dual3Links B → ℤ}
    {s : CurrentState B} (hs : IsSeparatedCurrentState q s) :
    (stateCovariance β q s).PosSemidef :=
  family_branchCovariance_posSemidef hβ _ (fun _ => closedCurrent_coClosed _)
    (stateCurrent_separated hs)

/-- **The renormalized identity for a separated current state.** -/
theorem stateIntegral_eq_gaussian {β : ℝ} (hβ : 0 < β) (q : Dual3Links B → ℤ) (z : ℤ → ℝ)
    (s : CurrentState B) (hs : IsSeparatedCurrentState q s) (shift : Dual3Links B → ℝ) :
    stateIntegral β q z s shift =
      ∫ y : EuclideanSpace ℝ (StateIndex s),
        ∏ i, (1 + stateAmp β q z s i *
          Real.cos (y i + linkPairing shift (stateCurrent q s i)))
        ∂multivariateGaussian 0 (stateCovariance β q s) := by
  have hraw : ∀ ω : EuclideanSpace ℝ (xyDual3RootedTree B).Chord × (XYDual3GraphVertex B → ℝ),
      currentStateProduct q z (fun e => gaugeField (xyDual3RootedTree B) ω e + shift e) s =
        ∏ i : StateIndex s, (1 + lineageCoefficient q z i.1 *
          Real.cos (linkPairing (gaugeField (xyDual3RootedTree B) ω) (lineageCurrent q i.1) +
            linkPairing shift (lineageCurrent q i.1))) := by
    intro ω
    unfold currentStateProduct currentFactor
    rw [← Finset.prod_coe_sort]
    refine Finset.prod_congr rfl fun i _ => ?_
    congr 3
    unfold currentPhase3 linkPairing
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun e _ => by ring
  unfold stateIntegral
  simp_rw [hraw]
  rw [integral_cosineProduct_eq_closed (xyDual3ChordMatrix_posDef hβ)
    (fun i : StateIndex s => lineageCoefficient q z i.1)
    (fun i : StateIndex s => lineageCurrent q i.1) shift
    (fun i j hij e f he hf => xy3_lineage_currentNear_separated hs i.2 j.2
      (fun h => hij (Subtype.ext h)) e f he hf)]
  exact family_integral_eq_gaussian hβ (stateActivity q z s)
    (fun i => linkPairing shift (stateCurrent q s i)) (stateCurrent q s)
    (fun _ => closedCurrent_coClosed _) (stateCurrent_separated hs)

end FroehlichSpencer.FS82.XY

end
