/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.SOS.Literal.Rooted
public import FroehlichSpencer.BKT.SOS.Literal.State
public import FroehlichSpencer.BKT.SOS.Roughening.Moment

/-!
# The moment bound in FS81's literal state at fixed scale (the finite comb construction)

`literalMoment_ge_of_layer`: given the pinned comb layers on the region `A` for every cutoff
(`CombOnWitness`) and admissible numbers at `β` (the hypotheses of `Tilt.integral_tilt_dipole_ge`
for the SOS weight `w_β = I_β(·/2π)`), for `u, v ∈ A` and `|ε| ≤ β/2`

`⟨e^{ε[φ(u) − φ(v)]}⟩_{Ω,A} ≥ exp((ε/2π)² R(u, v) (1/(4C₁) − 16 ε_end))`

in the literal state (7.16) on the box `Ω`, with `R(u, v)` the effective resistance of the whole
box. Proof: for every cutoff `N` the generic tilted ratio bound along the dipole potential, read on
`squareZero L`, is `(2π)^{L²+1}` times the mixed comb pairings (`integral_tiltDensity_combOnLam`);
as `N → ∞` these converge to the lattice sums of the marginals (`tendsto_mixedCombPairing`), which
are the tilted and untilted literal sums (`marginal_dipoleTilt`, `marginal_zero`).
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.SOS.Literal

open MeasureTheory Filter Topology Complex
open FroehlichSpencer.BKT.Generic
open FroehlichSpencer.BKT.Generic.PinnedCharges (SquareZeroBond Site)
open FroehlichSpencer.BKT.Rotator
open FroehlichSpencer.BKT.Rotator.TheoremC
open FroehlichSpencer.BKT.SOS.Tilt
open FroehlichSpencer.BKT.SOS.Roughening
open FroehlichSpencer.BKT.SOS.Star (interpolationCostConstant interpolationCostConstant_spec)

variable {L : ℕ}

/-- The limit of the mixed comb pairings of a tilted density, as a real sum. -/
theorem tendsto_re_mixedCombPairing (hL : 1 < L) {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1)
    (A : Finset (Site L)) {c : SquareZeroBond L → ℝ} (hc : ∀ e, |c e| ≤ β / 2) :
    Tendsto (fun N : ℕ => (∫ y, mixedComb A N y * sosDensityCoords L β c y).re) atTop
      (𝓝 (∑' n : {x // x ∈ A} → ℤ,
        marginalPi (· ∈ A) (sosDensityCoords L β c) (fun i => (n i : ℝ))).re) := by
  obtain ⟨f, hf⟩ := exists_sosDensityCoords_schwartz hL hβ hβ1 hc
  have hfun : (f : (Site L → ℝ) → ℂ) = sosDensityCoords L β c := funext hf
  have h := tendsto_mixedCombPairing A f
  rw [hfun] at h
  exact (Complex.continuous_re.tendsto _).comp h

/-- **The literal moment bound at fixed scale.** See the module docstring. -/
theorem literalMoment_ge_of_layer {D₁ D₂ α K₀ K₁ Kv a₁ a₂ : ℝ} {Kov : ℕ} (hK₀ : 0 < K₀)
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
    (hC₁ : 0 < κc + 4 * εp) (hL : 1 < L) {A : Finset (Site L)}
    (hwit : ∀ N : ℕ, 1 ≤ N → Nonempty (CombOnWitness L N A D₁ D₂ α K₀ K₁ Kv a₁ a₂ Kov))
    {u v : Site L} (hu : u ∈ A) (hv : v ∈ A) (ε : ℝ) (hε : |ε| ≤ β / 2) :
    ENNReal.ofReal (Real.exp ((ε / (2 * Real.pi)) ^ 2 *
        dipoleResistance (squareZero L) (squareZero_connected L hL) (some u) (some v) *
        (1 / (4 * (κc + 4 * εp)) - 16 * εe))) ≤ literalMomentExt L β A u v ε := by
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
  set X := (ε / (2 * Real.pi)) ^ 2 * dipoleResistance (squareZero L) hG (some u) (some v) *
    (1 / (4 * (κc + 4 * εp)) - 16 * εe) with hX
  have hc₁ : (fun e : SquareZeroBond L => 2 * Real.pi * (ε / (2 * Real.pi) *
      (squareZero L).grad (dipolePotential (squareZero L) hG (some u) (some v)) e)) =
      dipoleTilt hL u v ε := by
    funext e
    unfold dipoleTilt
    field_simp
  set P : (SquareZeroBond L → ℝ) → ℕ → ℝ := fun c N =>
    (∫ y, mixedComb A N y * sosDensityCoords L β c y).re with hP
  -- every cutoff
  have hcut : ∀ N : ℕ, 1 ≤ N → Real.exp X * P 0 N ≤ P (dipoleTilt hL u v ε) N := by
    intro N hN
    obtain ⟨Wt⟩ := hwit N hN
    have h := integral_tilt_dipole_ge hG none Wt.layer Wt.isLocal hKv hw
      (fun z _ => sosWeightψ_ne_zero β z) hlog hcurv hc hκ hK₀ hK₁ hD₁ hamp hampW hW1 hk₀ hexp
      hquad₁ hquad₂ zero_le_one le_rfl hM Wt.entropy_exp hb8 hb₁ hb₂ hthr hthrE hC₁ hη hwexp
      (some u) (some v) (ε / (2 * Real.pi)) hτ
    rw [← tiltDensity_zero_zero, integral_tiltDensity_combOnLam N A hβ.le,
      integral_tiltDensity_combOnLam N A hβ.le, hc₁] at h
    have h0 : (fun e : SquareZeroBond L => 2 * Real.pi * (0 : SquareZeroBond L → ℝ) e) = 0 := by
      funext e; simp
    rw [h0, mul_left_comm] at h
    exact le_of_mul_le_mul_left h (pow_pos hπ _)
  -- the comb limits
  have hc0 : ∀ e : SquareZeroBond L, |(0 : SquareZeroBond L → ℝ) e| ≤ β / 2 := fun e => by
    simp only [Pi.zero_apply, abs_zero]; positivity
  have hct : ∀ e, |dipoleTilt hL u v ε e| ≤ β / 2 := fun e =>
    (abs_dipoleTilt_le hL u v ε e).trans hε
  have hlimit := le_of_tendsto_of_tendsto
    ((tendsto_re_mixedCombPairing hL hβ hβ1 A hc0).const_mul (Real.exp X))
    (tendsto_re_mixedCombPairing hL hβ hβ1 A hct) (eventually_atTop.mpr ⟨1, hcut⟩)
  simp_rw [marginal_zero hβ.le, marginal_dipoleTilt hL hβ.le hu hv] at hlimit
  rw [← Complex.ofReal_tsum, ← Complex.ofReal_tsum, Complex.ofReal_re, Complex.ofReal_re]
    at hlimit
  rw [literalMomentExt_eq hL hβ hβ1 hu hv hε]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [le_div_iff₀ (tsum_literalWeight_pos hL hβ hβ1 A)]
  exact hlimit

end FroehlichSpencer.BKT.SOS.Literal

end
