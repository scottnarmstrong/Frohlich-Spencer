/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.XY.Jensen3
public import FroehlichSpencer.FS82.XY.AssignmentIntegral

/-!
# the lineages that are not co-closed drop out

Under the gauge-averaged
chord Gaussian a current that is not co-closed integrates to zero.

Hence the integral of the
product over a separated state equals the integral of the same product with the activity of every
lineage that is not co-closed set to zero, FS82 (4.32) and the sentence after it.

* `closedCurrent`, `closedActivity`: the current and activity of a lineage, set to zero when the
  lineage current is not co-closed.
* `integral_currentStateProduct_eq_closed`: the reduction.
-/

open MeasureTheory
open scoped BigOperators

@[expose] public section

namespace FroehlichSpencer.FS82.XY

open FroehlichSpencer.FS82.Gaussian
open FroehlichSpencer.FS82.Poisson
open FroehlichSpencer.FS82.Currents
open FroehlichSpencer.FS82.Gaussian.RenormalizedFamily.RenormalizedCharacters
open FroehlichSpencer.FS82.XY.Expansion3
open FroehlichSpencer.FS82.XY.GaugeAverage

variable {B : Dual3Box}

/-! ## Co-closedness: rooted tree and dual complex -/

/-- The real vector of an integer dual-link current. -/
noncomputable def currentVector (j : Dual3Links B → ℤ) : EuclideanSpace ℝ (Dual3Links B) :=
  WithLp.toLp 2 fun e => (j e : ℝ)

theorem currentVector_apply (j : Dual3Links B → ℤ) (e : Dual3Links B) :
    currentVector j e = (j e : ℝ) := rfl

theorem currentVector_mem_coClosed {j : Dual3Links B → ℤ}
    (hj : RootedTreeGauge.CoClosed (xyDual3RootedTree B) j) :
    currentVector j ∈ coClosed (dual3ExactOneComplex B) :=
  (xyDual3IntegerCirculationToCoClosed ⟨j, hj⟩).2

theorem treeCoClosed_of_currentVector_mem {j : Dual3Links B → ℤ}
    (hj : currentVector j ∈ coClosed (dual3ExactOneComplex B)) :
    RootedTreeGauge.CoClosed (xyDual3RootedTree B) j := by
  have hreal := xyDual3CoClosedToRooted ⟨currentVector j, hj⟩
  intro v hv
  have h := hreal v hv
  have hcast : RootedTreeGauge.divergence (xyDual3RootedTree B)
      (fun e => ((currentVector j) e : ℝ)) v =
      ((RootedTreeGauge.divergence (xyDual3RootedTree B) j v : ℤ) : ℝ) := by
    simp [RootedTreeGauge.divergence, currentVector_apply]
  rw [hcast] at h
  exact_mod_cast h

theorem currentVector_signedSum {ι : Type*} [Fintype ι] (J : ι → Dual3Links B → ℤ)
    (σ : ι → Sign) :
    currentVector (signedSum J σ) = ∑ i, signValue (σ i) • currentVector (J i) := by
  ext e
  simp [currentVector, signedSum, signValue_eq_signZ, Finset.sum_apply]

/-- **Separation.** If the signed sum of pairwise separated currents is co-closed, then every
current with a nonzero sign is co-closed. -/
theorem treeCoClosed_of_signedSum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (J : ι → Dual3Links B → ℤ) (σ : ι → Sign)
    (hsep : ∀ i j, i ≠ j → ∀ e f, J i e ≠ 0 → J j f ≠ 0 → ¬ Expansion3.currentNear e f)
    (hsum : RootedTreeGauge.CoClosed (xyDual3RootedTree B) (signedSum J σ))
    (i : ι) (hi : σ i ≠ 0) :
    RootedTreeGauge.CoClosed (xyDual3RootedTree B) (J i) := by
  have hvec := currentVector_mem_coClosed hsum
  rw [currentVector_signedSum] at hvec
  have hall := xy3_each_coClosed_of_currentNearSeparated (B := B) Finset.univ
    (fun i => signValue (σ i) • currentVector (J i)) hvec
    (by
      intro a _ b _ hab e f he hf
      refine hsep a b hab e f ?_ ?_
      · intro h0
        apply he
        simp [currentVector_apply, h0]
      · intro h0
        apply hf
        simp [currentVector_apply, h0])
    i (Finset.mem_univ i)
  have hne : signValue (σ i) ≠ 0 := by
    rw [signValue_eq_signZ]
    exact_mod_cast fun h => hi ((signZ_eq_zero_iff (σ i)).mp h)
  have hmem : currentVector (J i) ∈ coClosed (dual3ExactOneComplex B) := by
    have h := (coClosed (dual3ExactOneComplex B)).smul_mem (signValue (σ i))⁻¹ hall
    rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at h
  exact treeCoClosed_of_currentVector_mem hmem

/-! ## Closed currents and activities -/

/-- The current of a lineage, set to zero when it is not co-closed. -/
noncomputable def closedCurrent (j : Dual3Links B → ℤ) : Dual3Links B → ℤ :=
  open Classical in
  if RootedTreeGauge.CoClosed (xyDual3RootedTree B) j then j else 0

/-- The activity of a lineage, set to zero when its current is not co-closed. -/
noncomputable def closedActivity (K : ℝ) (j : Dual3Links B → ℤ) : ℝ :=
  open Classical in
  if RootedTreeGauge.CoClosed (xyDual3RootedTree B) j then K else 0

theorem closedCurrent_of_coClosed {j : Dual3Links B → ℤ}
    (hj : RootedTreeGauge.CoClosed (xyDual3RootedTree B) j) : closedCurrent j = j := by
  simp [closedCurrent, hj]

theorem closedCurrent_of_not_coClosed {j : Dual3Links B → ℤ}
    (hj : ¬ RootedTreeGauge.CoClosed (xyDual3RootedTree B) j) : closedCurrent j = 0 := by
  simp [closedCurrent, hj]

theorem closedActivity_of_coClosed (K : ℝ) {j : Dual3Links B → ℤ}
    (hj : RootedTreeGauge.CoClosed (xyDual3RootedTree B) j) : closedActivity K j = K := by
  simp [closedActivity, hj]

theorem closedActivity_of_not_coClosed (K : ℝ) {j : Dual3Links B → ℤ}
    (hj : ¬ RootedTreeGauge.CoClosed (xyDual3RootedTree B) j) : closedActivity K j = 0 := by
  simp [closedActivity, hj]

theorem closedCurrent_coClosed (j : Dual3Links B → ℤ) :
    RootedTreeGauge.CoClosed (xyDual3RootedTree B) (closedCurrent j) := by
  by_cases hj : RootedTreeGauge.CoClosed (xyDual3RootedTree B) j
  · rw [closedCurrent_of_coClosed hj]
    exact hj
  · rw [closedCurrent_of_not_coClosed hj]
    intro v _
    simp [RootedTreeGauge.divergence]

theorem closedCurrent_ne_zero_imp {j : Dual3Links B → ℤ} {e : Dual3Links B}
    (h : closedCurrent j e ≠ 0) : j e ≠ 0 := by
  by_cases hj : RootedTreeGauge.CoClosed (xyDual3RootedTree B) j
  · rwa [closedCurrent_of_coClosed hj] at h
  · rw [closedCurrent_of_not_coClosed hj] at h
    exact absurd rfl h

/-! ## The reduction -/

/-- **A family of pairwise separated currents under the gauge average**: the currents that are
not co-closed may be removed. -/
theorem integral_cosineProduct_eq_closed {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix (xyDual3RootedTree B).Chord (xyDual3RootedTree B).Chord ℝ} (hA : A.PosDef)
    (K : ι → ℝ) (J : ι → Dual3Links B → ℤ) (shift : Dual3Links B → ℝ)
    (hsep : ∀ i j, i ≠ j → ∀ e f, J i e ≠ 0 → J j f ≠ 0 → ¬ Expansion3.currentNear e f) :
    ∫ ω, ∏ i, (1 + K i * Real.cos (linkPairing (gaugeField (xyDual3RootedTree B) ω) (J i) +
        linkPairing shift (J i))) ∂gaugeMeasure (xyDual3RootedTree B) A =
      ∫ ω, ∏ i, (1 + closedActivity (K i) (J i) *
        Real.cos (linkPairing (gaugeField (xyDual3RootedTree B) ω) (closedCurrent (J i)) +
          linkPairing shift (closedCurrent (J i)))) ∂gaugeMeasure (xyDual3RootedTree B) A := by
  apply Complex.ofReal_injective
  rw [integral_cosineProduct (xyDual3RootedTree B) hA K (fun i => linkPairing shift (J i)) J,
    integral_cosineProduct (xyDual3RootedTree B) hA (fun i => closedActivity (K i) (J i))
      (fun i => linkPairing shift (closedCurrent (J i))) (fun i => closedCurrent (J i))]
  refine Finset.sum_congr rfl fun σ _ => ?_
  by_cases hP : ∀ i, σ i ≠ 0 → RootedTreeGauge.CoClosed (xyDual3RootedTree B) (J i)
  · have hw : signWeight K (fun i => linkPairing shift (J i)) σ =
        signWeight (fun i => closedActivity (K i) (J i))
          (fun i => linkPairing shift (closedCurrent (J i))) σ := by
      unfold signWeight
      refine Finset.prod_congr rfl fun i _ => ?_
      by_cases hi : σ i = 0
      · simp [hi, signCoeff, signValue]
      · beta_reduce
        rw [closedActivity_of_coClosed _ (hP i hi), closedCurrent_of_coClosed (hP i hi)]
    have hs : signedSum J σ = signedSum (fun i => closedCurrent (J i)) σ := by
      funext e
      unfold signedSum
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hi : σ i = 0
      · simp [hi]
      · beta_reduce
        rw [closedCurrent_of_coClosed (hP i hi)]
    rw [hw, hs]
  · push Not at hP
    obtain ⟨i, hi, hnot⟩ := hP
    have hleft : characterValue (xyDual3RootedTree B) A (signedSum J σ) = 0 :=
      characterValue_of_not_coClosed _ _ fun hsum =>
        hnot (treeCoClosed_of_signedSum J σ hsep hsum i hi)
    have hright : signWeight (fun i => closedActivity (K i) (J i))
        (fun i => linkPairing shift (closedCurrent (J i))) σ = 0 := by
      unfold signWeight
      refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
      beta_reduce
      rw [closedActivity_of_not_coClosed _ hnot, signCoeff_eq]
      simp [hi]
    rw [hleft, hright, mul_zero, zero_mul]

end FroehlichSpencer.FS82.XY

end
