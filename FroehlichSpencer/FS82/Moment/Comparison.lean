/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Moment.Packing
public import FroehlichSpencer.FS82.Moment.PositivePacking
public import FroehlichSpencer.FS82.Gaussian.FiniteGaussian
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# upper and joint moment comparison feasibility

Repository-facing abstract comparison built on the FS82 packing and finite Gaussian adapters.

The source box, Hodge inverse, current expansion, and lineage/localization remain named inputs.
-/

@[expose] public section

namespace FroehlichSpencer.FS82.Moment.Comparison

open MeasureTheory ProbabilityTheory
open Filter

/-!
## Exact scalar Gaussian factor from the adapter
-/

def scalarCovariance (v : ℝ) : Matrix Unit Unit ℝ := fun _ _ => v

def scalarVector (s : ℝ) : EuclideanSpace ℝ Unit :=
  WithLp.toLp 2 fun _ => s

theorem scalarCovariance_posSemidef (v : ℝ) (hv : 0 ≤ v) :
    (scalarCovariance v).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  constructor
  · ext i j
    simp [scalarCovariance]
  · intro x
    simp [scalarCovariance, dotProduct, Matrix.mulVec]
    calc
      0 ≤ v * (x ())^2 := mul_nonneg hv (sq_nonneg _)
      _ = x () * (v * x ()) := by ring

theorem scalarGaussian_characteristic (v s : ℝ) (hv : 0 ≤ v) :
    MeasureTheory.charFun
        (ProbabilityTheory.multivariateGaussian (0 : EuclideanSpace ℝ Unit)
          (scalarCovariance v)) (scalarVector s) =
      Complex.exp (Complex.ofReal (-(v * s ^ 2 / 2))) := by
  rw [FroehlichSpencer.FS82.Gaussian.finiteGaussianAdapter_characteristic
    (scalarCovariance v) (scalarCovariance_posSemidef v hv) (scalarVector s)]
  congr 1
  norm_cast
  simp [scalarVector, scalarCovariance, dotProduct, Matrix.mulVec]
  ring_nf

noncomputable def scalarGaussianFactor (v : ℝ) : ℝ :=
  Complex.re (MeasureTheory.charFun
    (ProbabilityTheory.multivariateGaussian (0 : EuclideanSpace ℝ Unit)
      (scalarCovariance v)) (scalarVector 1))

theorem scalarGaussianFactor_eq_exp (v : ℝ) (hv : 0 ≤ v) :
    scalarGaussianFactor v = Real.exp (-v / 2) := by
  unfold scalarGaussianFactor
  rw [scalarGaussian_characteristic v 1 hv]
  rw [Complex.exp_re]
  simp
  ring


/-! ## Positive current expansion: the upper half of (2.93) -/


/-! ## Finite support packing with the localization input exposed -/


/-- The summed Jensen error budget used by the moment comparison. Unlike
`CurrentPacking`, this interface permits the error assigned to a current to
depend on its ensemble. It records only the current family, its error, the
field, and the aggregate estimate needed by (2.93). -/
structure PackingBudget
    (Box Test Ensemble Current Plaquette : Type*)
    [Fintype Plaquette] [DecidableEq Plaquette] where
  currents : Box → Test → Ensemble → Finset Current
  error : Box → Test → ℝ → Ensemble → Current → ℝ
  field : Box → Test → ℝ → Plaquette → ℝ
  coefficient : ℝ
  budget : ∀ b μ t γ,
    (∑ i ∈ currents b μ γ, error b μ t γ i) ≤
      coefficient * ∑ p, (field b μ t p)^2


/-! ## One uniform joint theorem for boxes, tests, and moment parameters -/


/-! ## Exponential packing tail implies `β'' → ∞` -/

def betaDoublePrime (c : ℝ → ℝ) (beta : ℝ) : ℝ :=
  beta * (1 - 2 * beta * c beta)

theorem exponentialPacking_implies_comparison_behavior
    (c : ℝ → ℝ) (K : ℝ) (_hK : 0 < K)
    (hcPos : ∀ᶠ beta : ℝ in Filter.atTop, 0 < c beta)
    (hcBound : ∀ᶠ beta : ℝ in Filter.atTop,
      c beta ≤ K * Real.exp (-(beta / 432))) :
    Tendsto (fun beta => betaDoublePrime c beta) Filter.atTop Filter.atTop ∧
      (∀ᶠ beta : ℝ in Filter.atTop,
        0 < betaDoublePrime c beta ∧ betaDoublePrime c beta < beta) := by
  have hscale : Tendsto (fun beta : ℝ => beta / 432) Filter.atTop Filter.atTop := by
    exact (Filter.tendsto_id.atTop_div_const (by norm_num : (0 : ℝ) < 432))
  have hpoly := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hscale
  have hupper : Tendsto (fun beta : ℝ => beta * (K * Real.exp (-(beta / 432))))
      Filter.atTop (nhds 0) := by
    have h' : Tendsto
        (fun beta : ℝ => (432 * K) * ((beta / 432) * Real.exp (-(beta / 432))))
        Filter.atTop (nhds 0) := by
      simpa using (tendsto_const_nhds.mul hpoly)
    convert h' using 1
    · ext beta
      have hb : beta = 432 * (beta / 432) := by field_simp
      rw [hb]
      ring
  have hbcNonneg : ∀ᶠ beta : ℝ in Filter.atTop, 0 ≤ beta * c beta := by
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ), hcPos] with beta hb hcp
    exact mul_nonneg hb hcp.le
  have hbcUpper : ∀ᶠ beta : ℝ in Filter.atTop,
      beta * c beta ≤ beta * (K * Real.exp (-(beta / 432))) := by
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ), hcBound] with beta hb hcb
    exact mul_le_mul_of_nonneg_left hcb hb
  have hbc : Tendsto (fun beta : ℝ => beta * c beta) Filter.atTop (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
      hbcNonneg hbcUpper
  have hsmall : ∀ᶠ beta : ℝ in Filter.atTop, beta * c beta < 1 / 4 :=
    hbc.eventually (Iio_mem_nhds (by norm_num))
  have hlarge : ∀ᶠ beta : ℝ in Filter.atTop, 0 < beta :=
    Filter.eventually_gt_atTop 0
  have hstrict : ∀ᶠ beta : ℝ in Filter.atTop,
      0 < betaDoublePrime c beta ∧ betaDoublePrime c beta < beta := by
    filter_upwards [hsmall, hlarge, hcPos] with beta hs hb hc
    constructor
    · dsimp [betaDoublePrime]
      nlinarith
    · dsimp [betaDoublePrime]
      have hmul : 0 < beta * c beta := mul_pos hb hc
      nlinarith
  have hlower : ∀ᶠ beta : ℝ in Filter.atTop,
      beta / 2 ≤ betaDoublePrime c beta := by
    filter_upwards [hsmall, hlarge] with beta hs hb
    dsimp [betaDoublePrime]
    nlinarith
  have hid : Tendsto (fun beta : ℝ => beta / 2) Filter.atTop Filter.atTop :=
    Filter.tendsto_id.atTop_div_const (by norm_num : (0 : ℝ) < 2)
  exact ⟨Filter.tendsto_atTop_mono' Filter.atTop hlower hid, hstrict⟩


end FroehlichSpencer.FS82.Moment.Comparison
