/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.XY.AssignmentD
public import FroehlichSpencer.FS82.XY.ActivityD
public import FroehlichSpencer.FS82.XY.SeparationD
public import FroehlichSpencer.FS82.Gaussian.FiniteQuotientGaussian

/-!
# the gauge-averaged Gaussian of the dual complex of a box, `d ≥ 3`

The data of `XY/GaugeFieldD.lean` for the dual complex of a box of dimension `d ≥ 3`:

* `stencilInt`: the matrix of `dualDD₀` has integer entries (`stencilInt_cast`), and an integer
  current on the cells of degree `d − 2` is closed for it exactly when it is co-closed
  (`closedD_stencilInt_iff`);
* `dualCovariance hd B β`: the covariance `4π²β (d₁† d₁)⁻¹` on the co-closed forms, as a positive
  semidefinite matrix on all forms; on a co-closed integer current its quadratic form is
  `4π²β ⟨j, (d₁† d₁)⁻¹ j⟩` (`quadraticD_dualCovariance`), so the character of
  `XY/GaugeFieldD.lean` is `1[j co-closed] · exp(−2π²β ⟨j, (d₁† d₁)⁻¹ j⟩)`;
* `lineageGain d β J = (π²β/d²) ‖J‖²`: the gains, and the positivity of the renormalized
  covariance of a family of co-closed currents with disjoint supports
  (`family_branchCovarianceD_posSemidef`), from `DualD.family_gain_le`.
-/

open scoped BigOperators

@[expose] public section

namespace FroehlichSpencer.FS82.XY.DualD

open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Gaussian
open FroehlichSpencer.FS82.XY.GaugeAverage

variable {d : ℕ} {B : Box d}

/-! ## The integer divergence matrix -/

/-- The integer matrix of `dualDD₀`. -/
noncomputable def stencilInt (v : DualDForm B (d - 3)) (e : DualDForm B (d - 2)) : ℤ :=
  -(sgnCell v.1 * sgnCell e.1) * boundaryBasis (bumpCell e.1) (bumpCell v.1)

theorem stencilInt_cast (v : DualDForm B (d - 3)) (e : DualDForm B (d - 2)) :
    ((stencilInt v e : ℤ) : ℝ) = dualExteriorDifferenceStencilBasis v.1 e.1 := by
  rw [stencilBasis_eq_boundaryBasis]
  unfold stencilInt
  push_cast
  ring

/-- Closed for the integer stencil is co-closed in the dual complex. -/
theorem closedD_stencilInt_iff (hd : 3 ≤ d) (j : DualDForm B (d - 2) → ℤ) :
    ClosedD (stencilInt (B := B)) j ↔
      currentVector j ∈ coClosed (dualDExactOneComplex hd B) := by
  rw [currentVector_mem_coClosed_iff]
  have hcast : ∀ v : DualDForm B (d - 3),
      ∑ e : DualDForm B (d - 2), (j e : ℝ) * dualExteriorDifferenceStencilBasis v.1 e.1 =
        ((divergenceD (stencilInt (B := B)) j v : ℤ) : ℝ) := by
    intro v
    unfold divergenceD
    rw [Int.cast_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [Int.cast_mul, stencilInt_cast]
    ring
  constructor
  · intro h v
    rw [hcast, h v, Int.cast_zero]
  · intro h v
    have := h v
    rw [hcast] at this
    exact_mod_cast this

/-! ## The covariance -/

/-- The covariance `4π²β (d₁† d₁)⁻¹` of the dual field, as a matrix on all forms of degree
`d − 2`. -/
noncomputable def dualCovariance (hd : 3 ≤ d) (B : Box d) (β : ℝ) :
    Matrix (DualDForm B (d - 2)) (DualDForm B (d - 2)) ℝ :=
  finiteComplexCovarianceMatrix (dualDExactOneComplex hd B) (4 * Real.pi ^ 2 * β)

theorem dualCovariance_posSemidef (hd : 3 ≤ d) (B : Box d) {β : ℝ} (hβ : 0 ≤ β) :
    (dualCovariance hd B β).PosSemidef :=
  finiteComplexCovarianceMatrix_posSemidef _ (by positivity)

/-- The quadratic form of the covariance on a co-closed real form. -/
theorem bilinearD_dualCovariance_self (hd : 3 ≤ d) (β : ℝ) (x : DualDForm B (d - 2) → ℝ)
    (hx : (WithLp.toLp 2 x : EuclideanSpace ℝ (DualDForm B (d - 2))) ∈
      coClosed (dualDExactOneComplex hd B)) :
    bilinearD (dualCovariance hd B β) x x =
      4 * Real.pi ^ 2 * β *
        quotientCovarianceQuadratic (dualDExactOneComplex hd B) ⟨WithLp.toLp 2 x, hx⟩ := by
  have h := finiteComplexCovarianceQuadratic (dualDExactOneComplex hd B) (4 * Real.pi ^ 2 * β)
    (WithLp.toLp 2 x)
  unfold bilinearD dualCovariance
  refine Eq.trans h ?_
  simp only [LinearMap.smul_apply]
  rw [real_inner_smul_right]
  have hamb := finiteComplexAmbientCovariance_coClosed_apply (dualDExactOneComplex hd B)
    ⟨WithLp.toLp 2 x, hx⟩
  change _ * inner ℝ (WithLp.toLp 2 x : EuclideanSpace ℝ (DualDForm B (d - 2)))
    (finiteComplexAmbientCovariance (dualDExactOneComplex hd B) (WithLp.toLp 2 x)) = _
  rw [hamb]
  rfl

/-- The quadratic form of the covariance on a co-closed integer current. -/
theorem quadraticD_dualCovariance (hd : 3 ≤ d) (β : ℝ) (j : DualDForm B (d - 2) → ℤ)
    (hj : currentVector j ∈ coClosed (dualDExactOneComplex hd B)) :
    quadraticD (dualCovariance hd B β) j =
      4 * Real.pi ^ 2 * β *
        quotientCovarianceQuadratic (dualDExactOneComplex hd B) ⟨currentVector j, hj⟩ :=
  bilinearD_dualCovariance_self hd β (realCurrent j) hj

/-! ## Gains -/

/-- The gain of a lineage current: `(π²β/d²) ‖J‖²`. -/
noncomputable def lineageGain (d : ℕ) (β : ℝ) {E : Type*} [Fintype E] (J : E → ℤ) : ℝ :=
  Real.pi ^ 2 * β / (d : ℝ) ^ 2 * currentEnergy J


section Family

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem toLp_sum_smul_realCurrent (J : ι → DualDForm B (d - 2) → ℤ) (s : ι → ℝ) :
    (WithLp.toLp 2 (∑ i, s i • realCurrent (J i)) : EuclideanSpace ℝ (DualDForm B (d - 2))) =
      ∑ i, s i • currentVector (J i) := by
  ext e
  rw [WithLp.ofLp_sum]
  simp [realCurrent, currentVector_apply, Finset.sum_apply]

omit [DecidableEq ι] in
/-- **The gains of a family of co-closed currents with disjoint supports.** -/
theorem family_gain_le_bilinearD (hd : 3 ≤ d) {β : ℝ} (hβ : 0 ≤ β)
    (J : ι → DualDForm B (d - 2) → ℤ)
    (hco : ∀ i, currentVector (J i) ∈ coClosed (dualDExactOneComplex hd B))
    (hdisj : ∀ i j, i ≠ j → ∀ e, J i e ≠ 0 → J j e = 0) (s : ι → ℝ) :
    ∑ i, s i ^ 2 * lineageGain d β (J i) ≤
      bilinearD (dualCovariance hd B β) (∑ i, s i • realCurrent (J i))
        (∑ i, s i • realCurrent (J i)) := by
  have hd0 : (0 : ℝ) < (d : ℝ) := by
    have : 0 < d := by omega
    exact_mod_cast this
  have hmem : (WithLp.toLp 2 (∑ i, s i • realCurrent (J i)) :
      EuclideanSpace ℝ (DualDForm B (d - 2))) ∈ coClosed (dualDExactOneComplex hd B) := by
    rw [toLp_sum_smul_realCurrent]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hco i)
  rw [bilinearD_dualCovariance_self hd β _ hmem]
  have hgain := family_gain_le hd J hco hdisj s
  have hQ : quotientCovarianceQuadratic (dualDExactOneComplex hd B)
      ⟨WithLp.toLp 2 (∑ i, s i • realCurrent (J i)), hmem⟩ =
      quotientCovarianceQuadratic (dualDExactOneComplex hd B)
        ⟨∑ i, s i • currentVector (J i),
          Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hco i)⟩ := by
    congr 1
    exact Subtype.ext (toLp_sum_smul_realCurrent J s)
  rw [hQ]
  have hsum : ∑ i, s i ^ 2 * lineageGain d β (J i) =
      Real.pi ^ 2 * β / (d : ℝ) ^ 2 * ∑ i, s i ^ 2 * currentEnergy (J i) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by unfold lineageGain; ring
  rw [hsum]
  have hcoef : 0 ≤ Real.pi ^ 2 * β / (d : ℝ) ^ 2 := by positivity
  calc Real.pi ^ 2 * β / (d : ℝ) ^ 2 * ∑ i, s i ^ 2 * currentEnergy (J i)
      ≤ Real.pi ^ 2 * β / (d : ℝ) ^ 2 * (4 * (d : ℝ) ^ 2 *
          quotientCovarianceQuadratic (dualDExactOneComplex hd B)
            ⟨∑ i, s i • currentVector (J i),
              Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hco i)⟩) :=
        mul_le_mul_of_nonneg_left hgain hcoef
    _ = _ := by
        field_simp

/-- The renormalized covariance of a family of co-closed currents with disjoint supports is
positive semidefinite. -/
theorem family_branchCovarianceD_posSemidef (hd : 3 ≤ d) {β : ℝ} (hβ : 0 ≤ β)
    (J : ι → DualDForm B (d - 2) → ℤ)
    (hco : ∀ i, currentVector (J i) ∈ coClosed (dualDExactOneComplex hd B))
    (hdisj : ∀ i j, i ≠ j → ∀ e, J i e ≠ 0 → J j e = 0) :
    (branchCovarianceD (dualCovariance hd B β) J fun i => lineageGain d β (J i)).PosSemidef :=
  branchCovarianceD_posSemidef (dualCovariance_posSemidef hd B hβ) J _
    (family_gain_le_bilinearD hd hβ J hco hdisj)

end Family

end FroehlichSpencer.FS82.XY.DualD

end
