/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Clock.Disorder.GridFejer
public import FroehlichSpencer.BKT.Clock.Disorder.GridTorus
public import FroehlichSpencer.BKT.Clock.Disorder.GridSeam
public import FroehlichSpencer.BKT.Clock.Disorder.CompactExponent
import Mathlib.Tactic

/-!
The clock disorder operator at `ξ = k/N` has a power-law lower bound, on the finite free comb law
and at every limit point.

The threshold `n₁(β) = gridThreshold β` tends to infinity with `β`, and
`β''' = 2π (2β + 2εN²) C₀` is shared over `k`.

Here `ε = gridPackingEps` and `C₀` is the
box-uniform seam constant.

The proof uses the compact clock expansion.
1.

The seam twist decomposes as `t = ∇σ + θ`, with `∑ θ² ≤ N² ξ² C₀ (1 + log(1 + r))`
   (`exists_uniform_clockDisorderSeamProfile`).
2.

The twisted Fejér numerator is the bond product with offset `θ` at `φ + σ`
   (`clockDensity_mul_clockDisorderField_eq_twistedBondProduct`,
   `compactClockBondProduct_twist_eq_shiftedOffset`).

A torus translation moves `σ` onto the Fejér
   multiplier (`integral_gridBoxMeasure_add_periodic`).
3.

The compact T1.5 (`gridFejer_shift_ge`) bounds the ratio below by
   `exp(−(2β/N²) ∑ θ² − ε ∑ ([∇σ]²_{2π} + θ²))`.

On the grid the twist lies in `2πℤ`, so
   `[∇σ]²_{2π} ≤ θ²` (`sq_toIcoMod_grad_neg_le`).

The packing loss is therefore logarithmic.
4.

`compactBranch_lower_to_power` turns the logarithmic energy into the power law.

Fejér limits,
   then limits along the exhaustion, preserve the bound.

Main statements: `clockDisorderFejerRatio_grid_ge`, `clockDisorderExpectation_grid_ge`,
`clockDisorderLimitPoint_grid_ge` and `clock_disorder_lowerBound_grid`.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Clock.Disorder

open Filter Topology MeasureTheory
open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Rotator
open FroehlichSpencer.BKT.Clock.Periodic
open FroehlichSpencer.BKT.Clock.Compact

/-! ### The grid twist and periodicity -/

/-- On the grid the rescaled seam twist takes values in `2πℤ`. -/
theorem clockDisorderSeamTwist_grid {r L : ℕ} (hL : 0 < L) (hr : r ≤ L) {N : ℕ} (hN : 0 < N)
    (k : ℕ) (e : RotatorInternalBond (2 * L)) :
    ∃ m : ℤ, clockDisorderSeamTwist hL hr N ((k : ℝ) / N) e = 2 * Real.pi * m := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  unfold clockDisorderSeamTwist
  split_ifs
  · refine ⟨-(k : ℤ), ?_⟩
    rw [show -2 * Real.pi * (N : ℝ) * ((k : ℝ) / N) = -2 * Real.pi * ((N : ℝ) * ((k : ℝ) / N))
      by ring, mul_div_cancel₀ _ hN']
    push_cast
    ring
  · exact ⟨0, by simp⟩

/-- The compact bond product is periodic under integer multiples of the box period. -/
theorem compactClockBondProduct_add_period {V E : Type} [Fintype E] (G : Multigraph V E) (β : ℝ)
    {N : ℕ} (hN : 0 < N) (φ : V → ℝ) (m : V → ℤ) (θ : E → ℝ) :
    compactClockBondProduct G β N (φ + fun v => (m v : ℝ) * clockAnglePeriod N) θ =
      compactClockBondProduct G β N φ θ := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  unfold compactClockBondProduct
  refine Finset.prod_congr rfl fun e _ => ?_
  have harg : (G.grad (φ + fun v => (m v : ℝ) * clockAnglePeriod N) e + θ e) / N =
      (G.grad φ e + θ e) / N + ((m (G.src e) - m (G.tgt e) : ℤ) : ℝ) * (2 * Real.pi) := by
    simp only [Multigraph.grad, Pi.add_apply, clockAnglePeriod]
    push_cast
    field_simp
    ring
  rw [harg, Real.cos_add_int_mul_two_pi]

/-- The Fejér clock multiplier is periodic under integer multiples of the box period. -/
theorem fejerClockMultiplier_add_period (N M : ℕ) (x s : ℝ) (m : ℤ) :
    fejerClockMultiplier N M (x + (m : ℝ) * clockAnglePeriod N + s) =
      fejerClockMultiplier N M (x + s) := by
  unfold fejerClockMultiplier clockAnglePeriod
  rw [← fejerPolynomial_add_two_pi_mul M (x + s - clockOffset N) (m * N)]
  congr 1
  push_cast
  ring

/-- A clock-law integral as a box integral against the unnormalized density. -/
theorem integral_clockLaw_eq_gridBox {V E : Type} [Fintype V] [Fintype E] {β : ℝ} (hβ : 0 ≤ β)
    (n : ℝ) (G : Multigraph V E) (f : (V → ℝ) → ℝ) :
    ∫ φ, f φ ∂clockLaw β n G =
      ((clockBoxMass β n (relabelGraph G (siteEquiv V)))⁻¹).toReal *
        ∫ φ, clockDensity β n G φ * f φ ∂gridBoxMeasure n V := by
  rw [integral_clockLaw_eq_base hβ G f, integral_gridBoxMeasure]

/-! ### The partition-ratio estimate -/

/-- The grid curvature-plus-packing coefficient `κ = 2β/N² + 2ε`. -/
def gridKappa (β : ℝ) (N : ℕ) : ℝ := 2 * β / (N : ℝ) ^ 2 + 2 * gridPackingEps

theorem gridKappa_nonneg {β : ℝ} (hβ : 0 ≤ β) (N : ℕ) : 0 ≤ gridKappa β N := by
  unfold gridKappa
  have := gridPackingEps_nonneg
  positivity

/-- **The shifted box inequality.** For `N ≥ n₁(β)` and a grid twist decomposed as
`t = ∇σ + θ`, the twisted Fejér numerator dominates `exp(−κ ∑ θ²)` times the Fejér denominator. -/
theorem gridSeam_integral_ge {L r N M k : ℕ} (hbuf : 2 * r + 1 ≤ L) (hL : 0 < L) (hM : 1 ≤ M)
    {β : ℝ} (hβ : 0 ≤ β) (hN : gridThreshold β ≤ N) (hNpos : 0 < N)
    (σ : RotatorSpinSite (2 * L) → ℝ) (θ : RotatorInternalBond (2 * L) → ℝ)
    (hdecomp : ∀ e, clockDisorderSeamTwist (r := r) hL (show r ≤ L by omega) N ((k : ℝ) / N) e =
      (rotatorFreeGraph (2 * L)).grad σ e + θ e) :
    Real.exp (-(gridKappa β N * ∑ e, θ e ^ 2)) *
        ∫ φ, clockDensity β N (squareFree (2 * L + 1)) φ *
          ∏ v, fejerPolynomial M (φ v - clockOffset N) ∂gridBoxMeasure N (RotatorSpinSite (2 * L)) ≤
      ∫ φ, clockDensity β N (squareFree (2 * L + 1)) φ *
          (clockDisorderField (r := r) N β ((k : ℝ) / N) φ hL (show r ≤ L by omega) *
            ∏ v, fejerPolynomial M (φ v - clockOffset N))
          ∂gridBoxMeasure N (RotatorSpinSite (2 * L)) := by
  have hr : r ≤ L := by omega
  have hL1 : 1 < 2 * L + 1 := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  set ξ : ℝ := (k : ℝ) / N with hξ
  set θs := gridTransport (2 * L + 1) θ with hθs
  -- the free-square density is the untwisted bond product
  have hdens : ∀ φ : RotatorSpinSite (2 * L) → ℝ,
      clockDensity β N (squareFree (2 * L + 1)) φ =
        compactClockBondProduct (squareFree (2 * L + 1)) β N φ 0 := by
    intro φ
    unfold clockDensity compactClockBondProduct
    simp only [Pi.zero_apply, add_zero]
  have hrot : ∀ φ : RotatorSpinSite (2 * L) → ℝ,
      clockDensity β N (squareFree (2 * L + 1)) φ =
        clockDensity β N (rotatorFreeGraph (2 * L)) φ := by
    intro φ
    rw [hdens, ← gridTransport_zero, compactClockBondProduct_gridTransport]
    unfold clockDensity compactClockBondProduct
    simp only [Pi.zero_apply, add_zero]
    rfl
  -- the twisted numerator is the shifted offset bond product
  have hnum : ∀ φ : RotatorSpinSite (2 * L) → ℝ,
      clockDensity β N (squareFree (2 * L + 1)) φ *
          (clockDisorderField (r := r) N β ξ φ hL hr *
            ∏ v, fejerPolynomial M (φ v - clockOffset N)) =
        compactClockBondProduct (squareFree (2 * L + 1)) β N (φ + σ) θs *
          ∏ v, fejerClockMultiplier N M (φ v) := by
    intro φ
    rw [← mul_assoc, hrot,
      clockDensity_mul_clockDisorderField_eq_twistedBondProduct N β ξ hNpos hL hr φ,
      compactClockBondProduct_twist_eq_shiftedOffset _ β N φ σ _ θ hdecomp]
    exact congrArg₂ (· * ·)
      (compactClockBondProduct_gridTransport (2 * L + 1) β N (φ + σ) θ).symm rfl
  -- the torus translation
  let g : (RotatorSpinSite (2 * L) → ℝ) → ℝ := fun φ =>
    compactClockBondProduct (squareFree (2 * L + 1)) β N φ θs *
      ∏ v, fejerClockMultiplier N M (φ v + (-σ) v)
  have hpoly : Continuous (fejerPolynomial M) := by
    unfold fejerPolynomial fejerCosineCoefficient
    fun_prop
  have hg : Continuous g := by
    refine (continuous_compactClockBondProduct _ β N θs).mul ?_
    refine continuous_finsetProd _ fun v _ => ?_
    unfold fejerClockMultiplier
    exact hpoly.comp (((continuous_apply v).add continuous_const).sub continuous_const)
  have hper : ∀ (φ : RotatorSpinSite (2 * L) → ℝ) (m : RotatorSpinSite (2 * L) → ℤ),
      g (φ + fun v => (m v : ℝ) * clockAnglePeriod N) = g φ := by
    intro φ m
    simp only [g]
    rw [compactClockBondProduct_add_period _ β hNpos φ m θs]
    congr 1
    refine Finset.prod_congr rfl fun v _ => ?_
    simp only [Pi.add_apply]
    exact fejerClockMultiplier_add_period N M (φ v) ((-σ) v) (m v)
  have htorus := integral_gridBoxMeasure_add_periodic hNr g hg hper σ
  have hgshift : ∀ φ : RotatorSpinSite (2 * L) → ℝ, g (φ + σ) =
      compactClockBondProduct (squareFree (2 * L + 1)) β N (φ + σ) θs *
        ∏ v, fejerClockMultiplier N M (φ v) := by
    intro φ
    simp only [g, Pi.add_apply, Pi.neg_apply, add_neg_cancel_right]
  -- the compact T1.5
  have hT := gridFejer_shift_ge (L := 2 * L + 1) hL1 hM hβ hN (-σ) θs
  -- the grid packing loss
  have hint : ∀ e, ∃ m : ℤ,
      clockDisorderSeamTwist (r := r) hL hr N ξ e = 2 * Real.pi * m :=
    fun e => clockDisorderSeamTwist_grid hL hr hNpos k e
  have hloss : (∑ e, toIcoMod Real.two_pi_pos (-Real.pi)
      ((squareFree (2 * L + 1)).grad (-σ) e) ^ 2) ≤ ∑ e, θ e ^ 2 := by
    rw [← sum_sq_gridTransport (2 * L + 1) θ]
    exact Finset.sum_le_sum fun e _ =>
      sq_toIcoMod_grad_neg_le σ θ _ hdecomp hint e
  have hexp : Real.exp (-(gridKappa β N * ∑ e, θ e ^ 2)) ≤
      Real.exp (-(2 * β / (N : ℝ) ^ 2 * ∑ e, θs e ^ 2) -
        gridPackingEps * ∑ e, (toIcoMod Real.two_pi_pos (-Real.pi)
          ((squareFree (2 * L + 1)).grad (-σ) e) ^ 2 + θs e ^ 2)) := by
    apply Real.exp_le_exp.mpr
    rw [Finset.sum_add_distrib, hθs, sum_sq_gridTransport]
    have hε := gridPackingEps_nonneg
    have hmul := mul_le_mul_of_nonneg_left hloss hε
    have hsplit : -(gridKappa β N * ∑ e, θ e ^ 2) =
        -(2 * β / (N : ℝ) ^ 2 * ∑ e, θ e ^ 2) - gridPackingEps * ∑ e, θ e ^ 2 -
          gridPackingEps * ∑ e, θ e ^ 2 := by
      unfold gridKappa
      ring
    rw [hsplit, mul_add]
    linarith
  -- nonnegativity of the Fejér denominator
  have hB : 0 ≤ ∫ φ, compactClockBondProduct (squareFree (2 * L + 1)) β N φ 0 *
      ∏ j, fejerClockMultiplier N M (φ j) ∂gridBoxMeasure N (RotatorSpinSite (2 * L)) := by
    refine integral_nonneg fun φ => mul_nonneg (compactClockBondProduct_pos _ β N φ 0).le ?_
    exact Finset.prod_nonneg fun j _ => fejerPolynomial_nonneg M hM _
  calc
    Real.exp (-(gridKappa β N * ∑ e, θ e ^ 2)) *
        ∫ φ, clockDensity β N (squareFree (2 * L + 1)) φ *
          ∏ v, fejerPolynomial M (φ v - clockOffset N) ∂gridBoxMeasure N (RotatorSpinSite (2 * L))
        = Real.exp (-(gridKappa β N * ∑ e, θ e ^ 2)) *
          ∫ φ, compactClockBondProduct (squareFree (2 * L + 1)) β N φ 0 *
            ∏ j, fejerClockMultiplier N M (φ j)
            ∂gridBoxMeasure N (RotatorSpinSite (2 * L)) := by
      congr 1
      exact integral_congr_ae (Filter.Eventually.of_forall fun φ =>
        congrArg₂ (· * ·) (hdens φ) rfl)
    _ ≤ Real.exp (-(2 * β / (N : ℝ) ^ 2 * ∑ e, θs e ^ 2) -
          gridPackingEps * ∑ e, (toIcoMod Real.two_pi_pos (-Real.pi)
            ((squareFree (2 * L + 1)).grad (-σ) e) ^ 2 + θs e ^ 2)) *
          ∫ φ, compactClockBondProduct (squareFree (2 * L + 1)) β N φ 0 *
            ∏ j, fejerClockMultiplier N M (φ j)
            ∂gridBoxMeasure N (RotatorSpinSite (2 * L)) :=
      mul_le_mul_of_nonneg_right hexp hB
    _ ≤ ∫ φ, g φ ∂gridBoxMeasure N (RotatorSpinSite (2 * L)) := hT
    _ = ∫ φ, g (φ + σ) ∂gridBoxMeasure N (RotatorSpinSite (2 * L)) := htorus.symm
    _ = _ := integral_congr_ae (Filter.Eventually.of_forall fun φ =>
      (hgshift φ).trans (hnum φ).symm)

/-- **The partition-ratio estimate on the grid.** For all large Fejér cutoffs, the Fejér ratio of
the seam observable at `ξ = k/N` is at least `exp(−κ ∑ θ²)`. -/
theorem clockDisorderFejerRatio_grid_ge {L r N k : ℕ} (hbuf : 2 * r + 1 ≤ L) (hL : 0 < L)
    {β : ℝ} (hβ : 0 ≤ β) (hN : gridThreshold β ≤ N) (hNpos : 0 < N)
    (σ : RotatorSpinSite (2 * L) → ℝ) (θ : RotatorInternalBond (2 * L) → ℝ)
    (hdecomp : ∀ e, clockDisorderSeamTwist (r := r) hL (show r ≤ L by omega) N ((k : ℝ) / N) e =
      (rotatorFreeGraph (2 * L)).grad σ e + θ e) :
    ∀ᶠ M : ℕ in atTop, Real.exp (-(gridKappa β N * ∑ e, θ e ^ 2)) ≤
      clockDisorderFejerRatio N β ((k : ℝ) / N) hNpos hL (show r ≤ L by omega) M := by
  classical
  let V := RotatorSpinSite (2 * L)
  let G := squareFree (2 * L + 1)
  set c := ((clockBoxMass β N (relabelGraph G (siteEquiv V)))⁻¹).toReal with hcdef
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hc : 0 < c := by
    have h0 := clockBoxMass_pos (relabelGraph G (siteEquiv V)) hβ hNr
    have h1 := clockBoxMass_ne_top (n := (N : ℝ)) (relabelGraph G (siteEquiv V)) hβ
    exact ENNReal.toReal_pos (ENNReal.inv_ne_zero.2 h1) (ENNReal.inv_ne_top.2 h0.ne')
  -- the Fejér denominator is eventually positive
  have hlim := tendsto_integral_clockLaw_fejer (V := V) hβ (n := N) G (fun _ => (1 : ℝ))
    continuous_const (C := 1) (fun _ => by simp)
  have hNe : Nonempty (Fin N) := ⟨⟨0, hNpos⟩⟩
  have hpos : 0 < c * ((2 * Real.pi) ^ Fintype.card V * ∑ k : V → Fin N,
      clockDensity β N G (fun v => cellCenter N (k v)) * 1) := by
    refine mul_pos hc (mul_pos (pow_pos Real.two_pi_pos _) ?_)
    exact Finset.sum_pos (fun k _ => mul_pos (clockDensity_pos _ _ _ _) one_pos)
      Finset.univ_nonempty
  have hev := hlim.eventually (lt_mem_nhds hpos)
  filter_upwards [hev, eventually_ge_atTop 1] with M hMpos hM
  simp only [one_mul] at hMpos
  unfold clockDisorderFejerRatio
  rw [le_div_iff₀ hMpos, integral_clockLaw_eq_gridBox hβ, integral_clockLaw_eq_gridBox hβ]
  have hbox := gridSeam_integral_ge hbuf hL hM hβ hN hNpos σ θ hdecomp
  calc
    Real.exp (-(gridKappa β N * ∑ e, θ e ^ 2)) *
        (c * ∫ φ, clockDensity β N G φ * ∏ v, fejerPolynomial M (φ v - clockOffset N)
          ∂gridBoxMeasure N V) =
      c * (Real.exp (-(gridKappa β N * ∑ e, θ e ^ 2)) *
        ∫ φ, clockDensity β N G φ * ∏ v, fejerPolynomial M (φ v - clockOffset N)
          ∂gridBoxMeasure N V) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hbox hc.le

/-! ### The power law, finite volume and limit points -/

/-- The effective exponent coefficient `β''' = 2π κ N² C₀ = 2π (2β + 2εN²) C₀`. -/
def gridBeta''' (β : ℝ) (N : ℕ) (C₀ : ℝ) : ℝ :=
  clockDisorderEffectiveBeta (gridKappa β N) ((N : ℝ) ^ 2 * C₀)

/-- **(7.5) on the finite free comb law, at `ξ = k/N`.** One constant `C₀` serves every box,
seam length, `β`, `N` and `k`. -/
theorem clockDisorderExpectation_grid_ge :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ {β : ℝ}, 0 ≤ β → ∀ {N : ℕ} (hN : 0 < N), gridThreshold β ≤ N →
      ∀ (k L r : ℕ) (hbuf : 2 * r + 1 ≤ L) (hL : 0 < L),
        0 ≤ ((k : ℝ) / N) ^ 2 * gridBeta''' β N C₀ / (2 * Real.pi) ∧
        Real.exp (-(gridKappa β N * ((N : ℝ) ^ 2 * C₀) * ((k : ℝ) / N) ^ 2)) *
            (1 + (r : ℝ)) ^ (-(((k : ℝ) / N) ^ 2 * gridBeta''' β N C₀ / (2 * Real.pi))) ≤
          clockDisorderExpectation N β ((k : ℝ) / N) hN hL (show r ≤ L by omega) := by
  obtain ⟨C₀, hC₀, hprofile⟩ := exists_uniform_clockDisorderSeamProfile
  refine ⟨C₀, hC₀, ?_⟩
  intro β hβ N hN hNt k L r hbuf hL
  have hr : r ≤ L := by omega
  set ξ : ℝ := (k : ℝ) / N with hξ
  obtain ⟨σ, θ, hdecomp, henergy⟩ := hprofile L r hbuf hL N ξ
  have hκ := gridKappa_nonneg hβ N
  have hC : 0 ≤ (N : ℝ) ^ 2 * C₀ := by positivity
  have henergy' : (∑ e, θ e ^ 2) ≤ ξ ^ 2 * ((N : ℝ) ^ 2 * C₀) * (1 + Real.log (1 + (r : ℝ))) := by
    calc
      (∑ e, θ e ^ 2) ≤ (N : ℝ) ^ 2 * ξ ^ 2 * C₀ * (1 + Real.log (1 + (r : ℝ))) := henergy
      _ = ξ ^ 2 * ((N : ℝ) ^ 2 * C₀) * (1 + Real.log (1 + (r : ℝ))) := by ring
  have hratio := clockDisorderFejerRatio_grid_ge hbuf hL hβ hNt hN σ θ hdecomp
  have hpower : ∀ R : ℝ, Real.exp (-(gridKappa β N * ∑ e, θ e ^ 2)) ≤ R →
      0 ≤ ξ ^ 2 * gridBeta''' β N C₀ / (2 * Real.pi) ∧
        Real.exp (-0 - gridKappa β N * ((N : ℝ) ^ 2 * C₀) * ξ ^ 2) *
          (1 + (r : ℝ)) ^ (-(ξ ^ 2 * gridBeta''' β N C₀ / (2 * Real.pi))) ≤ R := by
    intro R hR
    exact compactBranch_lower_to_power r ξ (gridKappa β N) ((N : ℝ) ^ 2 * C₀) 0
      (∑ e, θ e ^ 2) R (gridBeta''' β N C₀) hκ hC henergy' (by rwa [add_zero]) rfl
  have hle : 0 ≤ ξ ^ 2 * gridBeta''' β N C₀ / (2 * Real.pi) :=
    (hpower _ le_rfl).1
  refine ⟨hle, ?_⟩
  have hb := clockDisorderExpectation_ge_of_fejerEventually (r := r) (L := L) N β ξ
    (Real.exp (-0 - gridKappa β N * ((N : ℝ) ^ 2 * C₀) * ξ ^ 2) *
      (1 + (r : ℝ)) ^ (-(ξ ^ 2 * gridBeta''' β N C₀ / (2 * Real.pi)))) hN hβ hL hr
    (hratio.mono fun M hM => (hpower _ hM).2)
  rwa [neg_zero, zero_sub] at hb

/-- **(7.5) at every limit point, at `ξ = k/N`.** -/
theorem clockDisorderLimitPoint_grid_ge :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ {β : ℝ}, 0 ≤ β → ∀ {N : ℕ} (hN : 0 < N), gridThreshold β ≤ N →
      ∀ (k r : ℕ) (hr : 0 < r) (c : ℝ),
        IsClockDisorderLimitPoint N r β ((k : ℝ) / N) c hN hr →
        Real.exp (-(gridKappa β N * ((N : ℝ) ^ 2 * C₀) * ((k : ℝ) / N) ^ 2)) *
            (1 + (r : ℝ)) ^ (-(((k : ℝ) / N) ^ 2 * gridBeta''' β N C₀ / (2 * Real.pi))) ≤ c := by
  obtain ⟨C₀, hC₀, hfinite⟩ := clockDisorderExpectation_grid_ge
  refine ⟨C₀, hC₀, ?_⟩
  intro β hβ N hN hNt k r hr c hc
  rcases hc with ⟨s, hs, htend⟩
  apply ge_of_tendsto htend
  rw [eventually_atTop]
  refine ⟨r + 1, fun t ht => ?_⟩
  have hst : t ≤ s t := hs.id_le t
  exact (hfinite hβ hN hNt k (r + s t) r (by omega) (by omega)).2

/--
There is a threshold `n₁(β) → ∞` such that for
every `β ≥ 0` and every clock order `N ≥ n₁(β)` there are `β''' ≥ 0` and `const > 0`, both shared
over `k = 1, …, N − 1`, with: every limit point `c` of the seam disorder expectation at `ξ = k/N` and
seam length `r ≥ 1` satisfies `const · (1 + r)^{−ξ² β'''/(2π)} ≤ c`.
-/
theorem clock_disorder_lowerBound_grid :
    ∃ n₁ : ℝ → ℕ, Tendsto n₁ atTop atTop ∧
      ∀ β : ℝ, 0 ≤ β → ∀ (N : ℕ) (hN : 0 < N), n₁ β ≤ N →
        ∃ β''' : ℝ, 0 ≤ β''' ∧ ∃ C : ℝ, 0 < C ∧
          ∀ k : ℕ, 1 ≤ k → k < N →
            ∀ (r : ℕ) (hr : 0 < r) (c : ℝ),
              IsClockDisorderLimitPoint N r β ((k : ℝ) / N) c hN hr →
                C * (1 + (r : ℝ)) ^ (-(((k : ℝ) / N) ^ 2 * β''' / (2 * Real.pi))) ≤ c := by
  obtain ⟨C₀, hC₀, hlimit⟩ := clockDisorderLimitPoint_grid_ge
  refine ⟨gridThreshold, tendsto_gridThreshold, ?_⟩
  intro β hβ N hN hNt
  have hκ := gridKappa_nonneg hβ N
  have hKC : 0 ≤ gridKappa β N * ((N : ℝ) ^ 2 * C₀) := by positivity
  refine ⟨gridBeta''' β N C₀, ?_, Real.exp (-(gridKappa β N * ((N : ℝ) ^ 2 * C₀))),
    Real.exp_pos _, ?_⟩
  · unfold gridBeta''' clockDisorderEffectiveBeta
    positivity
  intro k _ hkN r hr c hc
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hξ1 : ((k : ℝ) / N) ^ 2 ≤ 1 := by
    have hk0 : 0 ≤ (k : ℝ) / N := by positivity
    have hk1 : (k : ℝ) / N ≤ 1 := by
      rw [div_le_one hNr]
      exact_mod_cast hkN.le
    nlinarith
  have hC : Real.exp (-(gridKappa β N * ((N : ℝ) ^ 2 * C₀))) ≤
      Real.exp (-(gridKappa β N * ((N : ℝ) ^ 2 * C₀) * ((k : ℝ) / N) ^ 2)) := by
    apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_left hξ1 hKC
    linarith
  calc
    Real.exp (-(gridKappa β N * ((N : ℝ) ^ 2 * C₀))) *
        (1 + (r : ℝ)) ^ (-(((k : ℝ) / N) ^ 2 * gridBeta''' β N C₀ / (2 * Real.pi))) ≤
      Real.exp (-(gridKappa β N * ((N : ℝ) ^ 2 * C₀) * ((k : ℝ) / N) ^ 2)) *
        (1 + (r : ℝ)) ^ (-(((k : ℝ) / N) ^ 2 * gridBeta''' β N C₀ / (2 * Real.pi))) :=
      mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg (by positivity) _)
    _ ≤ c := hlimit hβ hN hNt k r hr c hc

end FroehlichSpencer.BKT.Clock.Disorder

end
