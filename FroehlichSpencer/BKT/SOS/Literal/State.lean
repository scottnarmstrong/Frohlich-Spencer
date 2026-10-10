/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.SOS.Literal.Marginal
public import FroehlichSpencer.BKT.SOS.Roughening.Comb
public import FroehlichSpencer.BKT.SOS.Roughening.Variance
public import FroehlichSpencer.BKT.SOS.Tilt.Potential

/-!
# FS81's literal SOS state (7.16) on a finite box (the finite comb construction)

FS81 §7.2 (FS81): `dμ_{I_β,Ω} = N_Ω⁻¹ ∏_{|i−j|=1, i∈Ω} I_β(φ(i) − φ(j)) ∏_{k∈Ω} dφ(k)`
with `φ = 0` off `Ω`, and the state in a finite `A ⊆ Ω` is
`Z_A⁻¹ ∏_{j∈A}[1 + 2Σ_{q≥1} cos(2πqφ(j))] dμ_{I_β,Ω}(φ)` (7.16). The comb is the Dirac comb
`Σ_{n∈ℤ} δ(φ(j) − n)` (Poisson), so the state is the measure on fields `φ : Ω → ℝ`

`Z⁻¹ Σ_{n ∈ ℤ^A} (∏_e I_β(∇φ(e))) dy |_{φ = n ⊕ y}`:

integer heights `n` on `A`, the continuous field `y` on `Ω ∖ A` with Lebesgue measure, the bonds
`|i − j| = 1, i ∈ Ω` being the edges of `squareZero L` (`boxWeight`). The constant `N_Ω` cancels.

* `literalState L β A`: this measure (`literalFiber`, `literalPartition`); for `L > 1` and
  `0 < β ≤ 1` it is a **probability measure** (`isProbabilityMeasure_literalState`), the
  normalization `0 < Z < ∞` being proved from the partial Poisson summation
  (`summable_literalWeight`).
* `literalMomentExt L β A u v ε = ∫⁻ e^{ε(φ(u) − φ(v))}`: the extended moment, an `ℝ≥0∞`-valued
  lintegral, always meaningful.
* `literalVariance L β A u v = ∫ (φ(u) − φ(v))²` with integrability proved
  (`integrable_literal_sq`).
* `lintegral_literalState`: expectations are `Z⁻¹ Σ_n ∫ ρ(n ⊕ y) F(n ⊕ y) dy`.

**The interpolation.** `I_β` is FS81's own Appendix C function (C.1), `Interp.sosInterp`. FS81's
printed condition (d) of §7.2 cannot hold for any interpolation of `e^{−β|n|}`
(`Interp.not_literal_derivative_bound`); (C.1) satisfies (a)–(c) and the corrected (d), so the state
is FS81's for (C.1). The state **depends on that choice**: the continuous sites `Ω ∖ A` see `I_β` at
non-integer arguments.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.SOS.Literal

open MeasureTheory
open FroehlichSpencer.BKT.Generic.PinnedCharges (Site SquareZeroBond)
open FroehlichSpencer.BKT.SOS.Roughening

variable {L : ℕ}

/-! ## The bond weight and the fibers -/

/-- FS81's interpolated bond weight of a field on the box with zero exterior:
`ρ(φ) = ∏_e I_β(∇φ(e))` over the edges of `squareZero L`. -/
def boxWeight (L : ℕ) (β : ℝ) (φ : Site L → ℝ) : ℝ :=
  ∏ e, (Interp.sosInterp β (pinnedGrad L φ e : ℂ)).re

theorem boxWeight_pos {β : ℝ} (hβ : 0 ≤ β) (φ : Site L → ℝ) : 0 < boxWeight L β φ :=
  Finset.prod_pos fun _ _ => (Interp.sosInterp_ofReal_im_eq_zero_and_re_pos hβ _).2

theorem boxWeight_neg {β : ℝ} (hβ : 0 ≤ β) (φ : Site L → ℝ) :
    boxWeight L β (-φ) = boxWeight L β φ := by
  unfold boxWeight
  refine Finset.prod_congr rfl fun e _ => ?_
  rw [map_neg, Pi.neg_apply, Interp.sosInterp_neg_ofReal hβ]

theorem continuous_sosInterp_re {β : ℝ} (hβ : 0 ≤ β) :
    Continuous fun t : ℝ => (Interp.sosInterp β (t : ℂ)).re := by
  refine Complex.continuous_re.comp (continuous_iff_continuousAt.mpr fun t => ?_)
  have hz : β ^ (1 / 3 : ℝ) * |((t : ℂ)).im| < 1 := by simp
  exact (Interp.hasDerivAt_sosInterp hβ hz).continuousAt.comp Complex.continuous_ofReal.continuousAt

theorem continuous_boxWeight {β : ℝ} (hβ : 0 ≤ β) : Continuous (boxWeight L β) := by
  unfold boxWeight
  refine continuous_finsetProd _ fun e _ => ?_
  exact (continuous_sosInterp_re hβ).comp
    ((continuous_apply e).comp (LinearMap.continuous_of_finiteDimensional _))

/-- The field with integer heights `n` on `A` and the continuous field `y` off `A`. -/
abbrev heightField (A : Finset (Site L)) (n : {x // x ∈ A} → ℤ) (y : {x // x ∉ A} → ℝ) :
    Site L → ℝ :=
  mergePi (· ∈ A) (fun i => (n i : ℝ)) y

/-- The fiber of the heights `n`: `ρ(n ⊕ y) dy`, pushed to fields. -/
def literalFiber (L : ℕ) (β : ℝ) (A : Finset (Site L)) (n : {x // x ∈ A} → ℤ) :
    Measure (Site L → ℝ) :=
  ((volume : Measure ({x // x ∉ A} → ℝ)).withDensity fun y =>
    ENNReal.ofReal (boxWeight L β (heightField A n y))).map (heightField A n)

/-- The partition function `Z = Σ_n ∫ ρ(n ⊕ y) dy`. -/
def literalPartition (L : ℕ) (β : ℝ) (A : Finset (Site L)) : ENNReal :=
  ∑' n, literalFiber L β A n Set.univ

/-- **FS81's state (7.16) on the box** `Ω = Site L`, the comb on `A`: `Z⁻¹ Σ_n ρ(n ⊕ y) dy`. -/
def literalState (L : ℕ) (β : ℝ) (A : Finset (Site L)) : Measure (Site L → ℝ) :=
  (literalPartition L β A)⁻¹ • Measure.sum (literalFiber L β A)

/-- **The extended moment** `⟨e^{ε[φ(u) − φ(v)]}⟩ ∈ [0, ∞]`. -/
def literalMomentExt (L : ℕ) (β : ℝ) (A : Finset (Site L)) (u v : Site L) (ε : ℝ) : ENNReal :=
  ∫⁻ φ, ENNReal.ofReal (Real.exp (ε * (φ u - φ v))) ∂literalState L β A

/-- **The variance** `⟨[φ(u) − φ(v)]²⟩`. -/
def literalVariance (L : ℕ) (β : ℝ) (A : Finset (Site L)) (u v : Site L) : ℝ :=
  ∫ φ, (φ u - φ v) ^ 2 ∂literalState L β A

/-- The marginal weight `W(n) = ∫ ρ(n ⊕ y) dy` of the heights `n`. -/
def literalWeight (L : ℕ) (β : ℝ) (A : Finset (Site L)) (n : {x // x ∈ A} → ℤ) : ℝ :=
  ∫ y, boxWeight L β (heightField A n y)

theorem measurable_heightField (A : Finset (Site L)) (n : {x // x ∈ A} → ℤ) :
    Measurable (heightField A n) :=
  (continuous_mergePi_right (· ∈ A) _).measurable

/-- **Expectations under the literal state**: `∫⁻ F = Z⁻¹ Σ_n ∫⁻ ρ(n ⊕ y) F(n ⊕ y) dy`. -/
theorem lintegral_literalState {β : ℝ} (hβ : 0 ≤ β) (A : Finset (Site L)) {F : (Site L → ℝ) → ENNReal}
    (hF : Measurable F) :
    ∫⁻ φ, F φ ∂literalState L β A = (literalPartition L β A)⁻¹ *
      ∑' n, ∫⁻ y, ENNReal.ofReal (boxWeight L β (heightField A n y)) * F (heightField A n y) := by
  unfold literalState
  rw [lintegral_smul_measure, lintegral_sum_measure, smul_eq_mul]
  congr 1
  refine tsum_congr fun n => ?_
  unfold literalFiber
  rw [lintegral_map hF (measurable_heightField A n)]
  exact lintegral_withDensity_eq_lintegral_mul _
    (ENNReal.measurable_ofReal.comp
      ((continuous_boxWeight hβ).measurable.comp (measurable_heightField A n)))
    (hF.comp (measurable_heightField A n))

/-! ## The tilted density and the marginal weights -/

section Analytic

open FroehlichSpencer.BKT.SOS.Tilt

variable {β : ℝ}

theorem sosInterp_ofReal_eq_re {β : ℝ} (hβ : 0 ≤ β) (t : ℝ) :
    Interp.sosInterp β (t : ℂ) = ((Interp.sosInterp β (t : ℂ)).re : ℂ) :=
  Complex.ext rfl (by simp [(Interp.sosInterp_ofReal_im_eq_zero_and_re_pos hβ t).1])

theorem prod_sosInterp_eq_boxWeight (hβ : 0 ≤ β) (y : Site L → ℝ) :
    ∏ e, Interp.sosInterp β (pinnedGrad L y e : ℂ) = ((boxWeight L β y : ℝ) : ℂ) := by
  unfold boxWeight
  rw [Complex.ofReal_prod]
  exact Finset.prod_congr rfl fun e _ => sosInterp_ofReal_eq_re hβ _

/-- The untilted height density is the bond weight. -/
theorem sosDensityCoords_zero_eq (hβ : 0 ≤ β) (y : Site L → ℝ) :
    sosDensityCoords L β 0 y = ((boxWeight L β y : ℝ) : ℂ) := by
  unfold sosDensityCoords sosTiltFactor
  simp only [Pi.zero_apply, Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_mul]
  exact prod_sosInterp_eq_boxWeight hβ y

/-- The wired box is connected, as a `Multigraph.Connected` proof. -/
theorem squareZero_connected' (hL : 1 < L) : (squareZero L).Connected := squareZero_connected L hL

/-- The tilt along the dipole potential of `u, v`: `c(e) = ε ∇g(e)`. -/
def dipoleTilt (hL : 1 < L) (u v : Site L) (ε : ℝ) : SquareZeroBond L → ℝ := fun e =>
  ε * (squareZero L).grad (dipolePotential (squareZero L) (squareZero_connected' hL)
    (some u) (some v)) e

theorem abs_dipoleTilt_le (hL : 1 < L) (u v : Site L) (ε : ℝ) (e : SquareZeroBond L) :
    |dipoleTilt hL u v ε e| ≤ |ε| := by
  unfold dipoleTilt
  rw [abs_mul]
  calc |ε| * |(squareZero L).grad _ e| ≤ |ε| * 1 :=
        mul_le_mul_of_nonneg_left (abs_grad_dipolePotential_le_one _ _ _ _ e) (abs_nonneg _)
    _ = |ε| := mul_one _

/-- **The tilted density** is `e^{ε(y(u) − y(v))} ρ(y)` for every field `y`. -/
theorem sosDensityCoords_dipoleTilt (hL : 1 < L) (hβ : 0 ≤ β) (u v : Site L) (ε : ℝ)
    (y : Site L → ℝ) :
    sosDensityCoords L β (dipoleTilt hL u v ε) y =
      ((Real.exp (ε * (y u - y v)) * boxWeight L β y : ℝ) : ℂ) := by
  unfold sosDensityCoords sosTiltFactor
  rw [Finset.prod_mul_distrib, prod_sosInterp_eq_boxWeight hβ, ← Complex.exp_sum,
    Complex.ofReal_mul, Complex.ofReal_exp]
  congr 2
  have h : ∑ e, (squareZero L).grad (pinnedField y) e *
      (squareZero L).grad (dipolePotential (squareZero L) (squareZero_connected' hL)
        (some u) (some v)) e = y u - y v :=
    sum_grad_mul_grad_dipolePotential (squareZero L) (squareZero_connected' hL)
      (some u) (some v) (pinnedField y)
  rw [← h, Finset.mul_sum]
  push_cast
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [pinnedGrad_apply, show dipoleTilt hL u v ε e = ε * (squareZero L).grad
    (dipolePotential (squareZero L) (squareZero_connected' hL) (some u) (some v)) e from rfl]
  push_cast
  ring

theorem heightField_apply_mem (A : Finset (Site L)) (n : {x // x ∈ A} → ℤ)
    (y : {x // x ∉ A} → ℝ) {u : Site L} (hu : u ∈ A) : heightField A n y u = n ⟨u, hu⟩ := by
  simp only [heightField, mergePi, dite_eq_left hu]

/-- The slices of the bond weight are integrable. -/
theorem integrable_boxWeight_slice (hL : 1 < L) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (A : Finset (Site L)) (x : {i // i ∈ A} → ℝ) :
    Integrable fun y => boxWeight L β (mergePi (· ∈ A) x y) := by
  obtain ⟨f, hf⟩ := exists_sosDensityCoords_schwartz hL hβ hβ1
    (c := 0) (fun e => by simp only [Pi.zero_apply, abs_zero]; positivity)
  have h := (integrable_slice (· ∈ A) f x).re
  refine h.congr (Filter.Eventually.of_forall fun y => ?_)
  simp only [hf, sosDensityCoords_zero_eq hβ.le]
  exact Complex.ofReal_re _

theorem literalWeight_pos (hL : 1 < L) (hβ : 0 < β) (hβ1 : β ≤ 1) (A : Finset (Site L))
    (n : {x // x ∈ A} → ℤ) : 0 < literalWeight L β A n := by
  unfold literalWeight
  rw [integral_pos_iff_support_of_nonneg (fun y => (boxWeight_pos hβ.le _).le)
    (integrable_boxWeight_slice hL hβ hβ1 A _)]
  have hsupp : Function.support (fun y => boxWeight L β (heightField A n y)) = Set.univ :=
    Set.eq_univ_of_forall fun y => (boxWeight_pos hβ.le _).ne'
  rw [hsupp]
  exact isOpen_univ.measure_pos volume Set.univ_nonempty

/-- The marginal of the tilted density at integer heights. -/
theorem marginal_dipoleTilt (hL : 1 < L) (hβ : 0 ≤ β) {A : Finset (Site L)} {u v : Site L}
    (hu : u ∈ A) (hv : v ∈ A) (ε : ℝ) (n : {x // x ∈ A} → ℤ) :
    marginalPi (· ∈ A) (sosDensityCoords L β (dipoleTilt hL u v ε)) (fun i => (n i : ℝ)) =
      ((Real.exp (ε * ((n ⟨u, hu⟩ : ℝ) - n ⟨v, hv⟩)) * literalWeight L β A n : ℝ) : ℂ) := by
  unfold marginalPi literalWeight
  simp_rw [sosDensityCoords_dipoleTilt hL hβ]
  have hfield : ∀ y, mergePi (· ∈ A) (fun i => (n i : ℝ)) y = heightField A n y := fun y => rfl
  simp_rw [hfield, heightField_apply_mem A n _ hu, heightField_apply_mem A n _ hv]
  rw [integral_complex_ofReal, integral_const_mul]

theorem marginal_zero (hβ : 0 ≤ β) (A : Finset (Site L)) (n : {x // x ∈ A} → ℤ) :
    marginalPi (· ∈ A) (sosDensityCoords L β 0) (fun i => (n i : ℝ)) =
      ((literalWeight L β A n : ℝ) : ℂ) := by
  unfold marginalPi literalWeight
  simp_rw [sosDensityCoords_zero_eq hβ]
  exact integral_complex_ofReal

/-- The marginal samples of the tilted density are summable (partial Poisson). -/
theorem summable_marginal (hL : 1 < L) (hβ : 0 < β) (hβ1 : β ≤ 1) {c : SquareZeroBond L → ℝ}
    (hc : ∀ e, |c e| ≤ β / 2) (A : Finset (Site L)) :
    Summable fun n : {x // x ∈ A} → ℤ =>
      marginalPi (· ∈ A) (sosDensityCoords L β c) (fun i => (n i : ℝ)) := by
  obtain ⟨f, hf⟩ := exists_sosDensityCoords_schwartz hL hβ hβ1 hc
  have hfun : (f : (Site L → ℝ) → ℂ) = sosDensityCoords L β c := funext hf
  have h := (tsum_fourier_extZero_eq_tsum_marginal (· ∈ A) f).2.2
  rw [hfun] at h
  exact h

theorem summable_literalWeight (hL : 1 < L) (hβ : 0 < β) (hβ1 : β ≤ 1) (A : Finset (Site L)) :
    Summable (literalWeight L β A) := by
  have h := summable_marginal hL hβ hβ1 (c := 0)
    (fun e => by simp only [Pi.zero_apply, abs_zero]; positivity) A
  simp_rw [marginal_zero hβ.le] at h
  exact Complex.summable_ofReal.mp h

theorem summable_exp_mul_literalWeight (hL : 1 < L) (hβ : 0 < β) (hβ1 : β ≤ 1)
    {A : Finset (Site L)} {u v : Site L} (hu : u ∈ A) (hv : v ∈ A) {ε : ℝ} (hε : |ε| ≤ β / 2) :
    Summable fun n : {x // x ∈ A} → ℤ =>
      Real.exp (ε * ((n ⟨u, hu⟩ : ℝ) - n ⟨v, hv⟩)) * literalWeight L β A n := by
  have h := summable_marginal hL hβ hβ1
    (c := dipoleTilt hL u v ε) (fun e => (abs_dipoleTilt_le hL u v ε e).trans hε) A
  simp_rw [marginal_dipoleTilt hL hβ.le hu hv] at h
  exact Complex.summable_ofReal.mp h

/-! ## The probability measure -/

theorem literalFiber_univ (hL : 1 < L) (hβ : 0 < β) (hβ1 : β ≤ 1) (A : Finset (Site L))
    (n : {x // x ∈ A} → ℤ) :
    literalFiber L β A n Set.univ = ENNReal.ofReal (literalWeight L β A n) := by
  unfold literalFiber literalWeight
  rw [Measure.map_apply (measurable_heightField A n) MeasurableSet.univ, Set.preimage_univ,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ofReal_integral_eq_lintegral_ofReal (integrable_boxWeight_slice hL hβ hβ1 A _)
      (Filter.Eventually.of_forall fun y => (boxWeight_pos hβ.le _).le)]

theorem literalPartition_eq (hL : 1 < L) (hβ : 0 < β) (hβ1 : β ≤ 1) (A : Finset (Site L)) :
    literalPartition L β A = ENNReal.ofReal (∑' n, literalWeight L β A n) := by
  unfold literalPartition
  simp_rw [literalFiber_univ hL hβ hβ1 A]
  exact (ENNReal.ofReal_tsum_of_nonneg (fun n => (literalWeight_pos hL hβ hβ1 A n).le)
    (summable_literalWeight hL hβ hβ1 A)).symm

theorem tsum_literalWeight_pos (hL : 1 < L) (hβ : 0 < β) (hβ1 : β ≤ 1) (A : Finset (Site L)) :
    0 < ∑' n, literalWeight L β A n :=
  (summable_literalWeight hL hβ hβ1 A).tsum_pos (fun n => (literalWeight_pos hL hβ hβ1 A n).le)
    0 (literalWeight_pos hL hβ hβ1 A 0)

/-- **The literal state is a probability measure** (`0 < Z < ∞`). -/
theorem isProbabilityMeasure_literalState (hL : 1 < L) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (A : Finset (Site L)) : IsProbabilityMeasure (literalState L β A) := by
  constructor
  unfold literalState
  rw [Measure.smul_apply, Measure.sum_apply _ MeasurableSet.univ, smul_eq_mul]
  have hZ : ∑' n, literalFiber L β A n Set.univ = literalPartition L β A := rfl
  rw [hZ, literalPartition_eq hL hβ hβ1 A]
  exact ENNReal.inv_mul_cancel (by simpa using tsum_literalWeight_pos hL hβ hβ1 A)
    ENNReal.ofReal_ne_top

/-! ## The moment and the variance -/

/-- Expectations of functions of `φ(u) − φ(v)`, `u, v ∈ A`. -/
theorem lintegral_literalState_diff (hL : 1 < L) (hβ : 0 < β) (hβ1 : β ≤ 1)
    {A : Finset (Site L)} {u v : Site L} (hu : u ∈ A) (hv : v ∈ A) {h : ℝ → ℝ}
    (hh : Continuous h) (hh0 : ∀ t, 0 ≤ h t)
    (hsum : Summable fun n : {x // x ∈ A} → ℤ =>
      h ((n ⟨u, hu⟩ : ℝ) - n ⟨v, hv⟩) * literalWeight L β A n) :
    ∫⁻ φ, ENNReal.ofReal (h (φ u - φ v)) ∂literalState L β A =
      ENNReal.ofReal ((∑' n, h ((n ⟨u, hu⟩ : ℝ) - n ⟨v, hv⟩) * literalWeight L β A n) /
        ∑' n, literalWeight L β A n) := by
  have hmeas : Measurable fun φ : Site L → ℝ => ENNReal.ofReal (h (φ u - φ v)) :=
    ENNReal.measurable_ofReal.comp ((hh.comp ((continuous_apply u).sub
      (continuous_apply v))).measurable)
  rw [lintegral_literalState hβ.le A hmeas, literalPartition_eq hL hβ hβ1 A]
  have hinner : ∀ n : {x // x ∈ A} → ℤ,
      ∫⁻ y, ENNReal.ofReal (boxWeight L β (heightField A n y)) *
        ENNReal.ofReal (h (heightField A n y u - heightField A n y v)) =
      ENNReal.ofReal (h ((n ⟨u, hu⟩ : ℝ) - n ⟨v, hv⟩) * literalWeight L β A n) := by
    intro n
    simp_rw [heightField_apply_mem A n _ hu, heightField_apply_mem A n _ hv]
    rw [lintegral_mul_const (f := fun y => ENNReal.ofReal (boxWeight L β (heightField A n y))) _
      (ENNReal.measurable_ofReal.comp
        ((continuous_boxWeight hβ.le).measurable.comp (measurable_heightField A n))),
      ← ofReal_integral_eq_lintegral_ofReal (integrable_boxWeight_slice hL hβ hβ1 A _)
        (Filter.Eventually.of_forall fun y => (boxWeight_pos hβ.le _).le)]
    change ENNReal.ofReal (literalWeight L β A n) * _ = _
    rw [← ENNReal.ofReal_mul (literalWeight_pos hL hβ hβ1 A n).le, mul_comm]
  simp_rw [hinner]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => mul_nonneg (hh0 _)
    (literalWeight_pos hL hβ hβ1 A n).le) hsum,
    ENNReal.ofReal_div_of_pos (tsum_literalWeight_pos hL hβ hβ1 A), ENNReal.div_eq_inv_mul]

/-- **The extended moment on the summable range.** -/
theorem literalMomentExt_eq (hL : 1 < L) (hβ : 0 < β) (hβ1 : β ≤ 1) {A : Finset (Site L)}
    {u v : Site L} (hu : u ∈ A) (hv : v ∈ A) {ε : ℝ} (hε : |ε| ≤ β / 2) :
    literalMomentExt L β A u v ε = ENNReal.ofReal
      ((∑' n, Real.exp (ε * ((n ⟨u, hu⟩ : ℝ) - n ⟨v, hv⟩)) * literalWeight L β A n) /
        ∑' n, literalWeight L β A n) :=
  lintegral_literalState_diff hL hβ hβ1 hu hv (h := fun t => Real.exp (ε * t))
    (by fun_prop) (fun t => (Real.exp_pos _).le) (summable_exp_mul_literalWeight hL hβ hβ1 hu hv hε)

/-- The squared height differences have summable weights. -/
theorem summable_sq_mul_literalWeight (hL : 1 < L) (hβ : 0 < β) (hβ1 : β ≤ 1)
    {A : Finset (Site L)} {u v : Site L} (hu : u ∈ A) (hv : v ∈ A) :
    Summable fun n : {x // x ∈ A} → ℤ =>
      ((n ⟨u, hu⟩ : ℝ) - n ⟨v, hv⟩) ^ 2 * literalWeight L β A n := by
  set δ₀ := β / 4 with hδ₀
  have hδ₀p : 0 < δ₀ := by positivity
  have h1 := summable_exp_mul_literalWeight hL hβ hβ1 hu hv (ε := 2 * δ₀)
    (by rw [abs_of_pos (by positivity)]; linarith)
  have h2 := summable_exp_mul_literalWeight hL hβ hβ1 hu hv (ε := -(2 * δ₀))
    (by rw [abs_neg, abs_of_pos (by positivity)]; linarith)
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (sq_nonneg _)
    (literalWeight_pos hL hβ hβ1 A n).le) (fun n => ?_) ((h1.add h2).mul_left (2 / δ₀ ^ 2))
  set x : ℝ := (n ⟨u, hu⟩ : ℝ) - n ⟨v, hv⟩
  have hb := Roughening.sq_mul_exp_abs_le hδ₀p x
  have hx : x ^ 2 ≤ x ^ 2 * Real.exp (δ₀ * |x|) :=
    le_mul_of_one_le_right (sq_nonneg _) (Real.one_le_exp (by positivity))
  have hW := (literalWeight_pos hL hβ hβ1 A n).le
  calc x ^ 2 * literalWeight L β A n
      ≤ 2 / δ₀ ^ 2 * (Real.exp (2 * δ₀ * x) + Real.exp (-(2 * δ₀) * x)) *
          literalWeight L β A n := mul_le_mul_of_nonneg_right (hx.trans hb) hW
    _ = 2 / δ₀ ^ 2 * (Real.exp (2 * δ₀ * x) * literalWeight L β A n +
          Real.exp (-(2 * δ₀) * x) * literalWeight L β A n) := by ring

/-- **The variance is a genuine integral**: `(φ(u) − φ(v))²` is integrable. -/
theorem integrable_literal_sq (hL : 1 < L) (hβ : 0 < β) (hβ1 : β ≤ 1) {A : Finset (Site L)}
    {u v : Site L} (hu : u ∈ A) (hv : v ∈ A) :
    Integrable (fun φ : Site L → ℝ => (φ u - φ v) ^ 2) (literalState L β A) := by
  refine ⟨(Continuous.aestronglyMeasurable (by fun_prop)), ?_⟩
  unfold HasFiniteIntegral
  have h := lintegral_literalState_diff hL hβ hβ1 hu hv (h := fun t => t ^ 2) (by fun_prop)
    (fun t => sq_nonneg t) (summable_sq_mul_literalWeight hL hβ hβ1 hu hv)
  have heq : ∀ φ : Site L → ℝ, ‖(φ u - φ v) ^ 2‖ₑ = ENNReal.ofReal ((φ u - φ v) ^ 2) :=
    fun φ => Real.enorm_of_nonneg (sq_nonneg _)
  simp_rw [heq, h]
  exact ENNReal.ofReal_lt_top

/-- **The variance on the summable range.** -/
theorem literalVariance_eq (hL : 1 < L) (hβ : 0 < β) (hβ1 : β ≤ 1) {A : Finset (Site L)}
    {u v : Site L} (hu : u ∈ A) (hv : v ∈ A) :
    literalVariance L β A u v =
      (∑' n, ((n ⟨u, hu⟩ : ℝ) - n ⟨v, hv⟩) ^ 2 * literalWeight L β A n) /
        ∑' n, literalWeight L β A n := by
  unfold literalVariance
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun φ => sq_nonneg _)
    (Continuous.aestronglyMeasurable (by fun_prop)),
    lintegral_literalState_diff hL hβ hβ1 hu hv (h := fun t => t ^ 2) (by fun_prop)
      (fun t => sq_nonneg t) (summable_sq_mul_literalWeight hL hβ hβ1 hu hv),
    ENNReal.toReal_ofReal (div_nonneg (tsum_nonneg fun n => mul_nonneg (sq_nonneg _)
      (literalWeight_pos hL hβ hβ1 A n).le) (tsum_literalWeight_pos hL hβ hβ1 A).le)]

end Analytic

end FroehlichSpencer.BKT.SOS.Literal

end
