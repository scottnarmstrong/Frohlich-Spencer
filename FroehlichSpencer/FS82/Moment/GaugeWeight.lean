/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Moment.GaugeCharacter

set_option linter.style.haveILetI false

@[expose] public section

open scoped BigOperators InnerProductSpace
open Matrix

namespace FroehlichSpencer.FS82.Moment.GaugeWeight

open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Currents
open FroehlichSpencer.FS82.Gaussian
open FroehlichSpencer.FS82.Moment.GaugeCharacter
open FroehlichSpencer.FS82.Moment.PhysicalGaugeCurrent
open FroehlichSpencer.FS82.Moment.QuotientGaussian
open FroehlichSpencer.FS82.Moment.SourceConstructor
open FroehlichSpencer.FS82.Poisson

variable {B : Box 4}

theorem sourceGaugePhysicalCharacter_eq_dualGaussianWeight
    (β : ℝ) (hβ : 0 < β) (j : SourcePoissonEdge B → ℤ)
    (hj : RootedTreeGauge.CoClosed (sourceRootedTree B) j) :
    sourcePhysicalGaussianCharacter (B := B) β
      (physicalGaugeCurrent (B := B) j)
      (physicalGaugeCurrent_divergence_zero (B := B) j hj) =
    dualGaussianWeight
      (scaledChordMatrix (sourceRootedTree B)
        (sourceFinitePoissonModel (B := B) Cubical.originZero) β)
      ((sourceRootedTree B).restrictChord (fun e => (j e : ℤ))) := by
  classical
  let T := sourceRootedTree B
  let M := sourceFinitePoissonModel (B := B) Cubical.originZero
  let R := reducedChordMatrix T M
  let c := 2 * Real.pi * β
  let A := scaledChordMatrix T M β
  have hc : c ≠ 0 := by
    dsimp [c]
    positivity
  have hRpos : R.PosDef := by
    dsimp [R, T, M]
    exact reducedChordMatrix_posDef (sourceRootedTree B)
      (sourceFinitePoissonModel (B := B) Cubical.originZero)
  have hdet : IsUnit R.det :=
    (Matrix.isUnit_iff_isUnit_det R).mp hRpos.isUnit
  have hAinv : A⁻¹ = c • R⁻¹ := by
    letI : Invertible (c⁻¹) := invertibleOfNonzero (inv_ne_zero hc)
    change ((c⁻¹) • R)⁻¹ = c • R⁻¹
    rw [Matrix.inv_smul R (c⁻¹) hdet]
    simp [c]
  have hquad := sourceGaugeVΛ_pairing_eq_chordInverse (B := B) j hj
  have hquad' :
      inner ℝ (sourceGaugeUnitW (B := B) j hj :
        EuclideanSpace ℝ (SourceDualOneCells B))
        (latticeVΛ (B := B) Cubical.originZero
          (sourceGaugeUnitW (B := B) j hj) :
          EuclideanSpace ℝ (SourceDualOneCells B)) =
      dotProduct ((T.restrictChord (fun e => (j e : ℝ))))
        (R⁻¹ *ᵥ T.restrictChord (fun e => (j e : ℝ))) := by
    simpa [T, M, R] using hquad
  let x := T.restrictChord (fun e => (j e : ℝ))
  have hsum :
      (∑ i, ∑ k, (T.restrictChord (fun e => (j e : ℝ)) i) *
        (A⁻¹ i k) * (T.restrictChord (fun e => (j e : ℝ)) k)) =
      c * inner ℝ (sourceGaugeUnitW (B := B) j hj :
        EuclideanSpace ℝ (SourceDualOneCells B))
        (latticeVΛ (B := B) Cubical.originZero
          (sourceGaugeUnitW (B := B) j hj) :
          EuclideanSpace ℝ (SourceDualOneCells B)) := by
    rw [hAinv, hquad']
    change (∑ i, ∑ k, x i * (c * R⁻¹ i k) * x k) =
      c * dotProduct x (R⁻¹ *ᵥ x)
    calc
      _ = ∑ i, c * (x i * (∑ k, R⁻¹ i k * x k)) := by
        apply Finset.sum_congr rfl
        intro i hi
        calc
          _ = (c * x i) * (∑ k, R⁻¹ i k * x k) := by
            calc
              _ = ∑ k, (c * x i) * (R⁻¹ i k * x k) := by
                apply Finset.sum_congr rfl
                intro k hk
                ring
              _ = (c * x i) * (∑ k, R⁻¹ i k * x k) := by
                exact (Finset.mul_sum Finset.univ
                  (fun k => R⁻¹ i k * x k) (c * x i)).symm
          _ = c * (x i * (∑ k, R⁻¹ i k * x k)) := by ring
      _ = c * dotProduct x (R⁻¹ *ᵥ x) := by
        change (∑ i, c * (x i * (∑ k, R⁻¹ i k * x k))) =
          c * (∑ i, x i * (∑ k, R⁻¹ i k * x k))
        exact (Finset.mul_sum Finset.univ
          (fun i => x i * (∑ k, R⁻¹ i k * x k)) c).symm
  have hphysquad :
      Gaussian.quotientCovarianceQuadratic
        (Gaussian.latticeExactOneComplex (B := B) Cubical.originZero)
        (sourceGaugeW (B := B) j hj) =
      (2 * Real.pi)^2 * inner ℝ
        (sourceGaugeUnitW (B := B) j hj :
          EuclideanSpace ℝ (SourceDualOneCells B))
        (latticeVΛ (B := B) Cubical.originZero
          (sourceGaugeUnitW (B := B) j hj) :
          EuclideanSpace ℝ (SourceDualOneCells B)) := by
    rw [Gaussian.quotientCovarianceQuadratic, sourceGaugeW_eq_scale_unit]
    change inner ℝ
      ((2 * Real.pi) • (sourceGaugeUnitW (B := B) j hj :
        EuclideanSpace ℝ (SourceDualOneCells B)))
      (latticeVΛ (B := B) Cubical.originZero
        ((2 * Real.pi) • sourceGaugeUnitW (B := B) j hj) :
          EuclideanSpace ℝ (SourceDualOneCells B)) = _
    rw [(latticeVΛ (B := B) Cubical.originZero).map_smul]
    change inner ℝ
      ((2 * Real.pi) • (sourceGaugeUnitW (B := B) j hj :
        EuclideanSpace ℝ (SourceDualOneCells B)))
      ((2 * Real.pi) • (latticeVΛ (B := B) Cubical.originZero
        (sourceGaugeUnitW (B := B) j hj) :
        EuclideanSpace ℝ (SourceDualOneCells B))) = _
    rw [real_inner_smul_left, real_inner_smul_right]
    ring
  unfold sourcePhysicalGaussianCharacter
  change Real.exp (-(β / 2) * Gaussian.quotientCovarianceQuadratic
      (Gaussian.latticeExactOneComplex (B := B) Cubical.originZero)
      (sourceGaugeW (B := B) j hj)) = _
  rw [hphysquad]
  unfold dualGaussianWeight
  congr 1
  change -(β / 2) * ((2 * Real.pi)^2 *
      inner ℝ (sourceGaugeUnitW (B := B) j hj :
        EuclideanSpace ℝ (SourceDualOneCells B))
        (latticeVΛ (B := B) Cubical.originZero
          (sourceGaugeUnitW (B := B) j hj) :
          EuclideanSpace ℝ (SourceDualOneCells B))) =
    -Real.pi * (∑ i, ∑ k,
      (T.restrictChord (fun e => (j e : ℝ)) i) *
        (A⁻¹ i k) * (T.restrictChord (fun e => (j e : ℝ)) k))
  rw [hsum]
  dsimp [c]
  ring


end FroehlichSpencer.FS82.Moment.GaugeWeight

end
