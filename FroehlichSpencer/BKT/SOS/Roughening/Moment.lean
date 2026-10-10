/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.SOS.Tilt.Ratio
public import FroehlichSpencer.BKT.SOS.Roughening.Weight
public import FroehlichSpencer.BKT.SOS.Roughening.Comb
public import FroehlichSpencer.BKT.Rotator.TheoremC.MainD

/-!
# The pinned SOS moment bound in a finite box (the dipole tilt construction: FS81 (7.17) at fixed scale)

The pinned SOS state on the box `{0,…,L−1}²` (FS81 §7.2 with the zero-exterior measures,
Dirichlet boundary conditions) has the moment generating function

`⟨e^{ε[φ(u) − φ(v)]}⟩ = Σ_n e^{ε(n(u) − n(v))} ∏_e e^{−β|∇n(e)|} / Σ_n ∏_e e^{−β|∇n(e)|}`

(`sosMoment`), and the variance `⟨[φ(u) − φ(v)]²⟩` (`sosVariance`).

`sosMoment_ge_of_layer`: given the Appendix D pinned charge layers of the comb for every cutoff
and admissible numbers at `β` (the hypotheses of `Tilt.integral_tilt_dipole_ge` for the SOS weight
`w_β = I_β(·/2π)`), for `|ε| ≤ β/2`

`⟨e^{ε[φ(u) − φ(v)]}⟩ ≥ exp((ε/2π)² R(u, v) (1/(4C₁) − 16ε_end))`.

Proof: for every cutoff `N` the generic tilted ratio bound along the dipole potential, read on
`squareZero L` in the angle variable, is `(2π)^{L²+1}` times the comb pairings of the tilted and
untilted SOS densities (`integral_tiltDensity_pinnedComb`); as `N → ∞` these converge to the
tilted and untilted height sums (`sosCombPairing_tendsto`), and the tilt `⟨c, ∇n⟩` with
`c = ε∇g` is `ε(n(u) − n(v))` by the dipole identity.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.SOS.Roughening

open MeasureTheory Filter Topology Complex
open FroehlichSpencer.BKT.Generic
open FroehlichSpencer.BKT.Generic.PinnedCharges (SquareZeroBond Site)
open FroehlichSpencer.BKT.Rotator
open FroehlichSpencer.BKT.Rotator.TheoremC
open FroehlichSpencer.BKT.SOS.Tilt
open FroehlichSpencer.BKT.SOS.Star (interpolationCostConstant interpolationCostConstant_spec)

variable {L : ℕ}

/-- FS81's tilted SOS sum on the pinned box: `Σ_n e^{ε(n(u) − n(v))} ∏_e e^{−β|∇n(e)|}`. -/
def sosTiltedSum (L : ℕ) (β ε : ℝ) (u v : Site L) : ℝ :=
  ∑' n : Site L → ℤ, Real.exp (ε * ((n u : ℝ) - n v)) * sosHeightWeight L β n

/-- The pinned SOS partition function `Σ_n ∏_e e^{−β|∇n(e)|}`. -/
def sosPartition (L : ℕ) (β : ℝ) : ℝ := ∑' n : Site L → ℤ, sosHeightWeight L β n

/-- FS81's `⟨e^{ε[φ(u) − φ(v)]}⟩` in the pinned SOS state on the box. -/
def sosMoment (L : ℕ) (β : ℝ) (u v : Site L) (ε : ℝ) : ℝ :=
  sosTiltedSum L β ε u v / sosPartition L β

/-- FS81's `⟨[φ(u) − φ(v)]²⟩` in the pinned SOS state on the box. -/
def sosVariance (L : ℕ) (β : ℝ) (u v : Site L) : ℝ :=
  (∑' n : Site L → ℤ, ((n u : ℝ) - n v) ^ 2 * sosHeightWeight L β n) / sosPartition L β

theorem tiltDensity_zero_zero {V E : Type} [Fintype V] [Fintype E] (G : Multigraph V E)
    (w : ℂ → ℂ) (v : V) : tiltDensity G w 0 0 v = edgeDensity G w v := by
  funext φ
  unfold tiltDensity tiltExponent
  simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, Real.exp_zero, one_mul]
  exact congrFun (offsetEdgeDensity_zero G w v) φ

/-- The dipole tilt of integer heights: `⟨ε∇g, ∇n⟩ = ε(n(u) − n(v))`. -/
theorem sum_dipole_mul_pinnedGrad (hL : 1 < L) (u v : Site L) (ε : ℝ) (n : Site L → ℤ) :
    ∑ e, 2 * Real.pi * (ε / (2 * Real.pi) *
        (squareZero L).grad (dipolePotential (squareZero L) (squareZero_connected L hL)
          (some u) (some v)) e) * pinnedGrad L (fun x => (n x : ℝ)) e =
      ε * ((n u : ℝ) - n v) := by
  have h := sum_grad_mul_grad_dipolePotential (squareZero L) (squareZero_connected L hL)
    (some u) (some v) (pinnedField fun x => (n x : ℝ))
  simp only [pinnedField, Option.elim] at h
  have hπ : (2 * Real.pi) ≠ 0 := by positivity
  rw [← h, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [pinnedGrad_apply]
  field_simp

/-- The real lattice sum of the tilted density at integer heights. -/
theorem re_tsum_sosDensityCoords {β : ℝ} (hβ : 0 ≤ β) (c : SquareZeroBond L → ℝ) :
    (∑' n : Site L → ℤ, sosDensityCoords L β c (fun x => (n x : ℝ))).re =
      ∑' n : Site L → ℤ, Real.exp (∑ e, c e * pinnedGrad L (fun x => (n x : ℝ)) e) *
        sosHeightWeight L β n := by
  rw [tsum_congr (sosDensityCoords_intCast hβ c), ← Complex.ofReal_tsum, Complex.ofReal_re]

/-- **The pinned SOS moment bound at fixed scale.** See the module docstring. -/
theorem sosMoment_ge_of_layer {D₁ D₂ α K₀ K₁ Kv a₁ a₂ : ℝ} {Kov : ℕ} (hK₀ : 0 < K₀)
    (hK₁ : 0 < K₁) (hD₁ : 0 < D₁) (hKv : 0 ≤ Kv) {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1)
    {M : ℝ → ℝ} (hlog : HasLogDerivBounds (sosWeightψ β) (sosWidthψ β) M) {κc : ℝ}
    (hcurv : HasCurvatureBound (sosWeightψ β) κc) {amp : ℝ} (hamp : 0 ≤ amp)
    (hampW : amp * K₁ ≤ sosWidthψ β) {k₀ : ℕ} (hk₀ : 1 ≤ k₀)
    (hexp : 100 * 4 ^ k₀ * costMajorant (interpolationCostConstant * β ^ (2 / 3 : ℝ))
      (interpolationCostConstant * β ^ (2 / 3 : ℝ)) (amp * K₁) ≤ amp / 2)
    (hquad₁ : amp ≤ 1 / (2 * (interpolationCostConstant * β ^ (2 / 3 : ℝ)) * K₀))
    (hquad₂ : amp ≤ (2 : ℝ) ^ (gradExponent α * k₀) / K₁)
    (hM : ∀ u : ℝ, |u| ≤ max (amp * K₁) 1 → M u ≤ 1) {b : ℝ}
    (hb8 : Real.log 8 / 2 ≤ b) (hb₁ : b ≤ amp / 8 - a₁) (hb₂ : b ≤ amp / (8 * D₁) - D₂ - a₂)
    {εp : ℝ} (hthr : ∀ d u : ℝ, 1 ≤ d → 2 ≤ u →
      (Kov : ℝ) * (8 * (Kv + 2 * Kv ^ 2)) * (d + 1) ^ (4 + 1) * u ^ 4 *
        Real.exp (-b * (u + Real.logb 2 (d + 1))) ≤ εp)
    {εe : ℝ} (hthrE : ∀ d u : ℝ, 1 ≤ d → 2 ≤ u →
      (Kov : ℝ) * (Kv * max (amp * K₁) 1 ^ 2) * (d + 1) ^ (2 + 1) * u ^ 0 *
        Real.exp (-b * (u + Real.logb 2 (d + 1))) ≤ εe)
    (hC₁ : 0 < κc + 4 * εp) (hL : 1 < L)
    (hwit : ∀ N : ℕ, 1 ≤ N → Nonempty (PinnedLayerWitnessD L N D₁ D₂ α K₀ K₁ Kv a₁ a₂ Kov))
    (u v : Site L) (ε : ℝ) (hε : |ε| ≤ β / 2) :
    Real.exp ((ε / (2 * Real.pi)) ^ 2 *
        dipoleResistance (squareZero L) (squareZero_connected L hL) (some u) (some v) *
        (1 / (4 * (κc + 4 * εp)) - 16 * εe)) ≤ sosMoment L β u v ε := by
  classical
  have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
  have hw := sosWeightψ_isStripWeight hβ hβ1
  have hc := sosCostψ_isCostEnvelope hβ.le (sosWidthψ β)
  have hκ : 0 < interpolationCostConstant * β ^ (2 / 3 : ℝ) :=
    mul_pos (lt_of_lt_of_le zero_lt_one (by
      have := interpolationCostConstant_spec.1
      unfold interpolationCostConstant at this ⊢
      linarith [(Classical.choose_spec
        FroehlichSpencer.BKT.Generic.exists_isStripWeight_sosInterp).1]))
      (Real.rpow_pos_of_pos hβ _)
  have hW1 : 1 ≤ sosWidthψ β := by
    unfold sosWidthψ
    have h1 : 1 ≤ β ^ (-(1 / 3 : ℝ)) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hβ hβ1
      (by norm_num)
    nlinarith [Real.two_le_pi]
  obtain ⟨K, hwexp⟩ := exists_sosWeightψ_hasExpMajorant hβ hβ1
  have hη : 0 < β / (2 * Real.pi) := div_pos hβ hπ
  have hτ : |ε / (2 * Real.pi)| ≤ β / (2 * Real.pi) / 2 := by
    calc |ε / (2 * Real.pi)| = |ε| / (2 * Real.pi) := by rw [abs_div, abs_of_pos hπ]
      _ ≤ (β / 2) / (2 * Real.pi) := div_le_div_of_nonneg_right hε hπ.le
      _ = β / (2 * Real.pi) / 2 := by ring
  set hG := squareZero_connected L hL
  set g := dipolePotential (squareZero L) hG (some u) (some v) with hg
  set X := (ε / (2 * Real.pi)) ^ 2 * dipoleResistance (squareZero L) hG (some u) (some v) *
    (1 / (4 * (κc + 4 * εp)) - 16 * εe) with hX
  set c₁ : SquareZeroBond L → ℝ := fun e => 2 * Real.pi * (ε / (2 * Real.pi) *
    (squareZero L).grad g e) with hc₁
  set P : (SquareZeroBond L → ℝ) → ℕ → ℝ := fun c N =>
    (∫ y, faceCombCutoff (ι := Site L) N y * sosDensityCoords L β c y).re with hP
  -- every cutoff
  have hcut : ∀ N : ℕ, 1 ≤ N → Real.exp X * P 0 N ≤ P c₁ N := by
    intro N hN
    obtain ⟨Wt⟩ := hwit N hN
    have h := integral_tilt_dipole_ge hG none Wt.layer Wt.isLocal hKv hw
      (fun z _ => sosWeightψ_ne_zero β z) hlog hcurv hc hκ hK₀ hK₁ hD₁ hamp hampW hW1 hk₀ hexp
      hquad₁ hquad₂ zero_le_one le_rfl hM Wt.entropy_exp hb8 hb₁ hb₂ hthr hthrE hC₁ hη hwexp
      (some u) (some v) (ε / (2 * Real.pi)) hτ
    rw [← tiltDensity_zero_zero, integral_tiltDensity_pinnedComb N hβ.le,
      integral_tiltDensity_pinnedComb N hβ.le] at h
    have h0 : (fun e : SquareZeroBond L => 2 * Real.pi * (0 : SquareZeroBond L → ℝ) e) = 0 := by
      funext e; simp
    rw [h0, mul_left_comm] at h
    exact le_of_mul_le_mul_left h (pow_pos hπ _)
  -- the comb limits
  have hc0 : ∀ e : SquareZeroBond L, |(0 : SquareZeroBond L → ℝ) e| ≤ β / 2 := fun e => by
    simp only [Pi.zero_apply, abs_zero]; positivity
  have hc1 : ∀ e : SquareZeroBond L, |c₁ e| ≤ β / 2 := fun e => by
    have hge := abs_grad_dipolePotential_le_one (squareZero L) hG (some u) (some v) e
    have heq : c₁ e = ε * (squareZero L).grad g e := by rw [hc₁]; field_simp
    rw [heq, abs_mul]
    calc |ε| * |(squareZero L).grad g e| ≤ |ε| * 1 := mul_le_mul_of_nonneg_left hge (abs_nonneg _)
      _ ≤ β / 2 := by rw [mul_one]; exact hε
  obtain ⟨hlim0, hsum0⟩ := sosCombPairing_tendsto hL hβ hβ1 hc0
  obtain ⟨hlim1, -⟩ := sosCombPairing_tendsto hL hβ hβ1 hc1
  have hre0 := (Complex.continuous_re.tendsto _).comp hlim0
  have hre1 := (Complex.continuous_re.tendsto _).comp hlim1
  have hlimit : Real.exp X *
      (∑' n : Site L → ℤ, sosDensityCoords L β 0 (fun x => (n x : ℝ))).re ≤
      (∑' n : Site L → ℤ, sosDensityCoords L β c₁ (fun x => (n x : ℝ))).re :=
    le_of_tendsto_of_tendsto (hre0.const_mul _) hre1
      (eventually_atTop.mpr ⟨1, fun N hN => hcut N hN⟩)
  -- the height sums
  rw [re_tsum_sosDensityCoords hβ.le, re_tsum_sosDensityCoords hβ.le] at hlimit
  have hZ : ∑' n : Site L → ℤ, Real.exp (∑ e, (0 : SquareZeroBond L → ℝ) e *
      pinnedGrad L (fun x => (n x : ℝ)) e) * sosHeightWeight L β n = sosPartition L β := by
    unfold sosPartition
    refine tsum_congr fun n => ?_
    simp
  have hT : ∑' n : Site L → ℤ, Real.exp (∑ e, c₁ e * pinnedGrad L (fun x => (n x : ℝ)) e) *
      sosHeightWeight L β n = sosTiltedSum L β ε u v := by
    unfold sosTiltedSum
    refine tsum_congr fun n => ?_
    rw [hc₁, sum_dipole_mul_pinnedGrad hL u v ε n]
  rw [hZ, hT] at hlimit
  -- the partition function is positive
  have hsumZ : Summable fun n : Site L → ℤ => sosHeightWeight L β n := by
    have h := Complex.summable_ofReal.mp ((summable_congr fun n =>
      sosDensityCoords_intCast hβ.le 0 n).mp hsum0)
    refine h.congr fun n => ?_
    simp
  have hZpos : 0 < sosPartition L β :=
    hsumZ.tsum_pos (fun n => (sosHeightWeight_pos L β n).le) 0 (sosHeightWeight_pos L β 0)
  unfold sosMoment
  rw [le_div_iff₀ hZpos]
  linarith

end FroehlichSpencer.BKT.SOS.Roughening

end
