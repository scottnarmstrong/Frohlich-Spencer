/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.XY.LatticeBridgeD
public import FroehlichSpencer.FS82.XY.SpinCubeRootD

/-!
# the endpoint expectation as a ratio of sums over integer co-closed currents

For every `d ≥ 3`, every box and `β > 0`:

`Re ⟨e^{i(θ_x − θ_y)}⟩ = exp(−‖ε‖²/(2β)) · S(2π τ) / S(0)`,
`S(s) = Re ∑_{j co-closed} e^{i⟨s, j⟩} e^{−2π²β⟨j,(d₁†d₁)⁻¹j⟩}`

(`xyEndpointCharacterExpectation_re_eq`).

This module imports
both `XY/PoissonPhaseD.lean` and `XY/FanFlowD.lean`.
-/

open scoped BigOperators

@[expose] public section

namespace FroehlichSpencer.FS82.XY.DualD

open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Gaussian
open FroehlichSpencer.FS82.Wilson
open FroehlichSpencer.FS82.XY.GaugeAverage

variable {d : ℕ} {B : Box d}


theorem dualDXYPathVector_eq (x y : XYSites B) :
    dualDXYPathVector x y = xyDualDEndpointPathVector x y := by
  unfold dualDXYPathVector xyDualDEndpointPathVector
  have hpath : xyBondModeChain (xyEndpointPathModes x y) = xyEndpointPath x y :=
    xyBondModeChain_restrict (xyEndpointPath x y) (xyEndpointPath_homogeneousSupport x y)
  rw [hpath]
  rfl

theorem dualDXYPathSource_eq (hd : 3 ≤ d) (x y : XYSites B) :
    dualDXYPathSource hd x y = xyDualDEndpointPathSourceCoClosed hd x y := by
  apply Subtype.ext
  change (dualDD₁ (B := B)).adjoint (dualDXYPathVector x y) =
    (dualDExactOneComplex hd B).d₁.adjoint (xyDualDEndpointPathVector x y)
  rw [dualDXYPathVector_eq]
  rfl

theorem dualDXYPathTau_eq (hd : 3 ≤ d) (x y : XYSites B) :
    dualDXYPathTau hd x y = xyDualDEndpointPathTau hd x y := by
  unfold dualDXYPathTau xyDualDEndpointPathTau
  rw [dualDXYPathSource_eq]

theorem dualDXYResidualEnergy_eq (hd : 3 ≤ d) (x y : XYSites B) :
    dualDXYResidualEnergy hd x y = xyDualDEndpointResidualEnergy hd x y := by
  rw [xyDualDEndpointResidualEnergy_eq_sub]
  unfold dualDXYResidualEnergy
  rw [dualDXYPathVector_eq, dualDXYPathSource_eq, dualDXYPathTau_eq]

/-! ## Coincident endpoints -/

theorem xyEndpointPath_self (x : XYSites B) : xyEndpointPath x x = 0 := by
  have hsrc : xyEndpointSource x x = 0 := by simp [xyEndpointSource]
  unfold xyEndpointPath
  rw [hsrc, map_zero]

theorem xyDualDEndpointPathVector_self (x : XYSites B) :
    xyDualDEndpointPathVector x x = 0 := by
  unfold xyDualDEndpointPathVector
  rw [xyEndpointPath_self]
  have h0 : castIntegerChain (0 : Chain d B) = 0 := by
    ext c
    simp [castIntegerChain]
  rw [h0, map_zero]

theorem dualDXYPathTau_self (hd : 3 ≤ d) (x : XYSites B) :
    ((dualDXYPathTau hd x x : DualDCoClosed hd B) : EuclideanSpace ℝ (DualDForm B (d - 2))) =
      0 := by
  have hsrc : dualDXYPathSource hd x x = 0 := by
    apply Subtype.ext
    change (dualDD₁ (B := B)).adjoint (dualDXYPathVector x x) = 0
    rw [dualDXYPathVector_eq, xyDualDEndpointPathVector_self, map_zero]
  unfold dualDXYPathTau
  rw [hsrc, map_zero]
  rfl

theorem dualDXYResidualEnergy_self (hd : 3 ≤ d) (x : XYSites B) :
    dualDXYResidualEnergy hd x x = 0 := by
  unfold dualDXYResidualEnergy
  rw [dualDXYPathVector_eq, xyDualDEndpointPathVector_self, dualDXYPathTau_self]
  simp

theorem pathShift_zero :
    pathShift (0 : EuclideanSpace ℝ (DualDForm B (d - 2))) = 0 := by
  funext e
  simp [pathShift]

/-! ## The two Poisson sums -/

theorem dualDXYPoissonConstant_ne_zero {β : ℝ} (hβ : 0 < β) :
    dualDXYPoissonConstant (B := B) β ≠ 0 := by
  unfold dualDXYPoissonConstant
  have hdet : 0 < (dualDXYCoordinateMatrix (B := B) β).det :=
    (dualDXYCoordinateMatrix_posDef hβ).det_pos
  have hsqrt : 0 < Real.sqrt (dualDXYCoordinateMatrix (B := B) β).det := Real.sqrt_pos.mpr hdet
  exact inv_ne_zero (by exact_mod_cast hsqrt.ne')

/-- The shifted cycle sum over the integer co-closed currents. -/
theorem xyShiftedCycleGaussianSum_eq_closedCharacterSum (hd : 3 ≤ d) {β : ℝ} (hβ : 0 < β)
    (x y : XYSites B) :
    ((xyShiftedCycleGaussianSum β x y : ℝ) : ℂ) =
      dualDXYPoissonConstant (B := B) β *
        Complex.exp (-dualDXYResidualEnergy hd x y / (2 * β)) *
        closedCharacterSum hd β (pathShift (dualDXYPathTau hd x y).1) := by
  rw [xyShiftedCycleGaussianSumD_eq_dualPhase hd hβ x y, tsum_dualDXYCurrentPhase_eq hd hβ x y]

/-- The cycle sum over the integer co-closed currents. -/
theorem xyCycleGaussianSum_eq_closedCharacterSum (hd : 3 ≤ d) {β : ℝ} (hβ : 0 < β)
    (x : XYSites B) :
    ((xyCycleGaussianSum (B := B) β : ℝ) : ℂ) =
      dualDXYPoissonConstant (B := B) β * closedCharacterSum (B := B) hd β 0 := by
  have hfreq : xyEndpointFrequency x x = 0 := by
    funext z
    simp [xyEndpointFrequency, xyEndpointSource]
  have hcycle : xyCycleGaussianSum (B := B) β = xyShiftedCycleGaussianSum β x x := by
    rw [xyCycleGaussianSum_eq_dualPartition, ← xyDualPartition_eq_shiftedCycleGaussianSum β x x,
      hfreq]
  rw [hcycle, xyShiftedCycleGaussianSum_eq_closedCharacterSum hd hβ x x,
    dualDXYResidualEnergy_self, dualDXYPathTau_self, pathShift_zero]
  simp

/-! ## The character sums are real -/

theorem closedCharacterSum_ofReal_re (hd : 3 ≤ d) {β : ℝ} (hβ : 0 < β)
    (shift : DualDForm B (d - 2) → ℝ) :
    (((closedCharacterSum hd β shift).re : ℝ) : ℂ) = closedCharacterSum hd β shift := by
  have hC := assignmentD_hasSum hd hβ shift
  have hRe := Complex.hasSum_re hC
  simp only [Complex.ofReal_re] at hRe
  exact (Complex.hasSum_ofReal.mpr hRe).unique hC

/-- **The endpoint expectation as a ratio of character sums.** -/
theorem xyEndpointCharacterExpectation_re_eq (hd : 3 ≤ d) {β : ℝ} (hβ : 0 < β)
    (x y : XYSites B) :
    (xyEndpointCharacterExpectation β x y).re =
      Real.exp (-(xyDualDEndpointResidualEnergy hd x y / (2 * β))) *
        ((closedCharacterSum hd β (pathShift (xyDualDEndpointPathTau hd x y).1)).re /
          (closedCharacterSum (B := B) hd β 0).re) := by
  have hP := dualDXYPoissonConstant_ne_zero (B := B) hβ
  rw [xyEndpointCharacterExpectation_eq_shiftedGaussianRatio β hβ x y,
    xyShiftedCycleGaussianSum_eq_closedCharacterSum hd hβ x y,
    xyCycleGaussianSum_eq_closedCharacterSum hd hβ x, dualDXYResidualEnergy_eq,
    dualDXYPathTau_eq]
  set N := closedCharacterSum hd β (pathShift (xyDualDEndpointPathTau hd x y).1) with hN
  set Z := closedCharacterSum hd β (0 : DualDForm B (d - 2) → ℝ) with hZ
  have hNre := closedCharacterSum_ofReal_re hd hβ (pathShift (xyDualDEndpointPathTau hd x y).1)
  have hZre := closedCharacterSum_ofReal_re hd hβ (0 : DualDForm B (d - 2) → ℝ)
  rw [← hN] at hNre
  rw [← hZ] at hZre
  have hexp : Complex.exp (-(xyDualDEndpointResidualEnergy hd x y : ℂ) / (2 * (β : ℂ))) =
      ((Real.exp (-(xyDualDEndpointResidualEnergy hd x y / (2 * β))) : ℝ) : ℂ) := by
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  rw [hexp, ← hNre, ← hZre]
  have hquot : dualDXYPoissonConstant (B := B) β *
      ((Real.exp (-(xyDualDEndpointResidualEnergy hd x y / (2 * β))) : ℝ) : ℂ) * ((N.re : ℝ) : ℂ) /
        (dualDXYPoissonConstant (B := B) β * ((Z.re : ℝ) : ℂ)) =
      ((Real.exp (-(xyDualDEndpointResidualEnergy hd x y / (2 * β))) * (N.re / Z.re) : ℝ) : ℂ) := by
    push_cast
    field_simp
  rw [hquot]
  simp only [Complex.ofReal_re]

end FroehlichSpencer.FS82.XY.DualD

end
