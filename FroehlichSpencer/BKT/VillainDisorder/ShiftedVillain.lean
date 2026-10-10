/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Villain.CosineExpectation
public import FroehlichSpencer.BKT.Villain.GraphSymmetry
import Mathlib.Tactic

/-!
# The Villain model with shifted bond angles

This file gives the current (Fourier) expansion of the Villain partition function
(`Villain/CosineExpectation`), with a constant shift `s_e` of each bond angle. Each weight
`v_β(dθ_e + s_e)` is expanded in Fourier series. Integrating out the angles leaves the currents
`q` that are neutral away from the root, each with its Gaussian weight and the phase of
`∑_e q_e s_e`. This is the finite-graph form of the derivation of FS81 (1.38) (Appendix A).

* `villain_shifted_partition_current_expansion`:
  `∫ ∏_e v_β(dθ_e + s_e) dθ = ((2πβ)^{-1/2})^{|E|} (2π)^{|V∖{z}|} ∑_q W_β(q) cos(∑_e q_e s_e)`.
  The sum is over the neutral currents `q`, and `W_β` is the current Gaussian weight.
* `villainShiftRatio`: `∏_e v_β(dθ_e + s_e)/v_β(dθ_e)`.
* **`integral_villainShiftRatio`**: the Villain expectation of the shift ratio is
  `∑_q W_β(q) cos(∑_e q_e s_e) / ∑_q W_β(q)`.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace FroehlichSpencer.BKT.Villain

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]

/-! ### The Villain model with shifted bond angles -/

/-- The current Fourier term with the constant phase `e^{-i ∑_e q_e s_e}` of the bond shifts. -/
def shiftedCurrentFourierTerm (G : Multigraph V E) (z : V) (β : ℝ) (s : E → ℝ) (q : E → ℤ)
    (θ : FreeAngles V z) : ℂ :=
  currentFourierTerm G z β q θ * Complex.exp (-Complex.I * ((∑ e, (q e : ℝ) * s e : ℝ) : ℂ))

theorem shiftedCurrentFourierTerm_norm (G : Multigraph V E) (z : V) (β : ℝ) (s : E → ℝ)
    (q : E → ℤ) (θ : FreeAngles V z) :
    ‖shiftedCurrentFourierTerm G z β s q θ‖ = currentGaussianWeight β q := by
  unfold shiftedCurrentFourierTerm
  rw [norm_mul, currentFourierTerm_norm, Complex.norm_exp]
  have : (-Complex.I * ((∑ e, (q e : ℝ) * s e : ℝ) : ℂ)).re = 0 := by simp [Complex.mul_re]
  rw [this, Real.exp_zero, mul_one]

/-- The product of shifted one-edge Fourier series is the single series over integer currents,
each current carrying the phase `e^{-i ∑_e q_e s_e}`. -/
theorem villain_shifted_product_fourier_pointwise (G : Multigraph V E) (z : V) (β : ℝ)
    (hβ : 0 < β) (s : E → ℝ) (θ : FreeAngles V z) :
    (∏ e, (villainWeight β
        (pinnedAngle z θ (G.src e) - pinnedAngle z θ (G.tgt e) + s e) : ℂ)) =
      (((2 * Real.pi * β) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) ^ Fintype.card E *
        ∑' q : E → ℤ, shiftedCurrentFourierTerm G z β s q θ := by
  classical
  let coeff (e : E) (m : ℤ) : ℂ :=
    (Real.exp (-((m : ℝ) ^ 2) / (2 * β)) : ℂ) * edgeFourierPhase G z θ e m *
      Complex.exp (-Complex.I * (m : ℂ) * (s e : ℂ))
  have hcoeff : ∀ e, Summable (fun m : ℤ => ‖coeff e m‖) := by
    intro e
    have hseries := FroehlichSpencer.BKT.VillainWeight.villainWeight_fourier_coeff_summable hβ
    have hphase (m : ℤ) : ‖edgeFourierPhase G z θ e m‖ = 1 := by
      rw [edgeFourierPhase, Complex.norm_exp]
      have hreal :
          (-Complex.I * (m : ℂ) *
            (((pinnedAngle z θ (G.src e) - pinnedAngle z θ (G.tgt e)) : ℝ) : ℂ)).re = 0 := by
        simp [Complex.mul_re]
      rw [hreal, Real.exp_zero]
    have hshift (m : ℤ) : ‖Complex.exp (-Complex.I * (m : ℂ) * (s e : ℂ))‖ = 1 := by
      rw [Complex.norm_exp]
      have hreal : (-Complex.I * (m : ℂ) * (s e : ℂ)).re = 0 := by simp [Complex.mul_re]
      rw [hreal, Real.exp_zero]
    apply hseries.congr
    intro m
    symm
    simp only [coeff]
    rw [norm_mul, norm_mul, Complex.norm_real, hphase, hshift]
    simp [abs_of_pos (Real.exp_pos _)]
  have hseries := Villain.tsum_prod_currents coeff hcoeff
  have hscalar (e : E) :
      (villainWeight β
          (pinnedAngle z θ (G.src e) - pinnedAngle z θ (G.tgt e) + s e) : ℂ) =
        (((2 * Real.pi * β) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * ∑' m : ℤ, coeff e m := by
    rw [FroehlichSpencer.BKT.VillainWeight.villainWeight_fourier_complex_normalized_neg hβ]
    congr 1
    refine tsum_congr fun m => ?_
    simp only [coeff, edgeFourierPhase, mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  calc ∏ e, (villainWeight β
        (pinnedAngle z θ (G.src e) - pinnedAngle z θ (G.tgt e) + s e) : ℂ)
      = ∏ e, ((((2 * Real.pi * β) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * ∑' m : ℤ, coeff e m) :=
        Finset.prod_congr rfl fun e _ => hscalar e
    _ = (((2 * Real.pi * β) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) ^ Fintype.card E *
          ∏ e, ∑' m : ℤ, coeff e m := by
        rw [Finset.prod_mul_distrib, Finset.prod_const]
        rfl
    _ = (((2 * Real.pi * β) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) ^ Fintype.card E *
          ∑' q : E → ℤ, ∏ e, coeff e (q e) := by rw [hseries]
    _ = _ := by
        congr 1
        refine tsum_congr fun q => ?_
        simp only [coeff, shiftedCurrentFourierTerm, currentFourierTerm]
        rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
        change (∏ e, (Real.exp (-((q e : ℝ) ^ 2) / (2 * β)) : ℂ)) *
            (∏ e, edgeCurrentPhase G z q θ e) *
            (∏ e, Complex.exp (-Complex.I * ((q e : ℤ) : ℂ) * (s e : ℂ))) = _
        have hph : ∏ e, Complex.exp (-Complex.I * ((q e : ℤ) : ℂ) * (s e : ℂ)) =
            Complex.exp (-Complex.I * ((∑ e, (q e : ℝ) * s e : ℝ) : ℂ)) := by
          rw [← Complex.exp_sum]
          congr 1
          push_cast
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun e _ => by ring
        rw [edgeCurrentPhase_prod_eq_vertexCharacter, hph]
        simp only [currentGaussianWeight, Complex.ofReal_prod]

/-- **The shifted Villain partition function as a current sum** (KP §6.1, p. 33, with the bond
shifts of FS81's disorder operator (1.32)): `∫ ∏_e v_β(dθ_e + s_e) dθ` is the volume factor times
`∑_q w(q) cos(∑_e q_e s_e)` over the currents neutral away from the root. -/
theorem villain_shifted_partition_current_expansion (G : Multigraph V E) (z : V) (β : ℝ)
    (hβ : 0 < β) (s : E → ℝ) :
    (∫ θ : FreeAngles V z,
      ∏ e, villainWeight β (pinnedAngle z θ (G.src e) - pinnedAngle z θ (G.tgt e) + s e)
        ∂rootedAngleMeasure z) =
      ((2 * Real.pi * β) ^ (-(1 / 2 : ℝ))) ^ Fintype.card E *
        (2 * Real.pi) ^ Fintype.card (FreeVertices V z) *
          ∑' q : E → ℤ, neutralCurrentGaussianWeight G z β q *
            Real.cos (∑ e, (q e : ℝ) * s e) := by
  classical
  let μ := rootedAngleMeasure (V := V) z
  have hfinite : IsFiniteMeasure μ := by
    dsimp [μ, rootedAngleMeasure]
    infer_instance
  set c : ℂ := (((2 * Real.pi * β) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) ^ Fintype.card E with hc
  set P : ℂ := ((2 * Real.pi : ℝ) ^ Fintype.card (FreeVertices V z) : ℂ) with hP
  -- termwise integration
  have hint : (∫ θ, ∑' q : E → ℤ, shiftedCurrentFourierTerm G z β s q θ ∂μ) =
      ∑' q : E → ℤ, ∫ θ, shiftedCurrentFourierTerm G z β s q θ ∂μ := by
    apply integral_tsum
    · intro q
      unfold shiftedCurrentFourierTerm
      exact ((continuous_currentFourierTerm G z β q).mul continuous_const).aestronglyMeasurable
    · have hweight := currentGaussianWeight_summable (E := E) β hβ
      have hsum : (∑' q : E → ℤ, ENNReal.ofReal (currentGaussianWeight β q)) ≠ ⊤ :=
        hweight.tsum_ofReal_ne_top
      have hμ : μ Set.univ ≠ ⊤ := ne_of_lt hfinite.measure_univ_lt_top
      have hconst (q : E → ℤ) : (∫⁻ θ, ‖shiftedCurrentFourierTerm G z β s q θ‖ₑ ∂μ) =
          ENNReal.ofReal (currentGaussianWeight β q) * μ Set.univ := by
        have hpoint (θ : FreeAngles V z) : ‖shiftedCurrentFourierTerm G z β s q θ‖ₑ =
            ENNReal.ofReal (currentGaussianWeight β q) := by
          rw [← ofReal_norm, shiftedCurrentFourierTerm_norm]
        rw [show (fun θ : FreeAngles V z => ‖shiftedCurrentFourierTerm G z β s q θ‖ₑ) =
            fun _ => ENNReal.ofReal (currentGaussianWeight β q) from funext hpoint]
        simp [lintegral_const]
      calc (∑' q : E → ℤ, ∫⁻ θ, ‖shiftedCurrentFourierTerm G z β s q θ‖ₑ ∂μ)
          = ∑' q : E → ℤ, ENNReal.ofReal (currentGaussianWeight β q) * μ Set.univ :=
            tsum_congr hconst
        _ = (∑' q : E → ℤ, ENNReal.ofReal (currentGaussianWeight β q)) * μ Set.univ := by
            rw [ENNReal.tsum_mul_right]
        _ ≠ ⊤ := ENNReal.mul_ne_top hsum hμ
  have hterm (q : E → ℤ) : (∫ θ, shiftedCurrentFourierTerm G z β s q θ ∂μ) =
      P * ((neutralCurrentGaussianWeight G z β q : ℝ) : ℂ) *
        Complex.exp (-Complex.I * ((∑ e, (q e : ℝ) * s e : ℝ) : ℂ)) := by
    unfold shiftedCurrentFourierTerm
    rw [integral_mul_const, integral_currentFourierTerm G z β q]
    by_cases hn : neutralAwayFrom G z q
    · simp only [hn, ↓reduceIte, neutralCurrentGaussianWeight, hP]
      push_cast
      ring
    · simp [hn, neutralCurrentGaussianWeight]
  -- the complex identity
  have hC : (∫ θ : FreeAngles V z,
      ∏ e, (villainWeight β
        (pinnedAngle z θ (G.src e) - pinnedAngle z θ (G.tgt e) + s e) : ℂ) ∂μ) =
      c * P * ∑' q : E → ℤ, ((neutralCurrentGaussianWeight G z β q : ℝ) : ℂ) *
        Complex.exp (-Complex.I * ((∑ e, (q e : ℝ) * s e : ℝ) : ℂ)) := by
    have hpoint : (fun θ : FreeAngles V z =>
        ∏ e, (villainWeight β
          (pinnedAngle z θ (G.src e) - pinnedAngle z θ (G.tgt e) + s e) : ℂ)) =
        fun θ => c * ∑' q : E → ℤ, shiftedCurrentFourierTerm G z β s q θ := by
      funext θ
      exact villain_shifted_product_fourier_pointwise G z β hβ s θ
    rw [hpoint, integral_const_mul, hint, tsum_congr hterm]
    rw [show (∑' q : E → ℤ, P * ((neutralCurrentGaussianWeight G z β q : ℝ) : ℂ) *
        Complex.exp (-Complex.I * ((∑ e, (q e : ℝ) * s e : ℝ) : ℂ))) =
        P * ∑' q : E → ℤ, ((neutralCurrentGaussianWeight G z β q : ℝ) : ℂ) *
          Complex.exp (-Complex.I * ((∑ e, (q e : ℝ) * s e : ℝ) : ℂ)) by
      rw [← tsum_mul_left]
      exact tsum_congr fun q => by ring]
    ring
  -- summability of the complex series
  have hsum : Summable fun q : E → ℤ => ((neutralCurrentGaussianWeight G z β q : ℝ) : ℂ) *
      Complex.exp (-Complex.I * ((∑ e, (q e : ℝ) * s e : ℝ) : ℂ)) := by
    refine Summable.of_norm_bounded (neutralCurrentGaussianWeight_summable G z β hβ) fun q => ?_
    rw [norm_mul, Complex.norm_real, Complex.norm_exp]
    have : (-Complex.I * ((∑ e, (q e : ℝ) * s e : ℝ) : ℂ)).re = 0 := by simp [Complex.mul_re]
    rw [this, Real.exp_zero, mul_one, Real.norm_eq_abs]
    exact le_of_eq (abs_of_nonneg (by
      unfold neutralCurrentGaussianWeight
      split_ifs
      · exact (currentGaussianWeight_pos β q).le
      · exact le_rfl))
  -- real parts
  have hcast : (∫ θ : FreeAngles V z,
      ∏ e, (villainWeight β
        (pinnedAngle z θ (G.src e) - pinnedAngle z θ (G.tgt e) + s e) : ℂ) ∂μ) =
      ((∫ θ : FreeAngles V z, ∏ e, villainWeight β
        (pinnedAngle z θ (G.src e) - pinnedAngle z θ (G.tgt e) + s e) ∂μ : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    exact integral_congr_ae (ae_of_all _ fun θ => by simp only [Complex.ofReal_prod])
  rw [hcast] at hC
  have hreal := congrArg Complex.re hC
  rw [Complex.ofReal_re] at hreal
  change _ = _ at hreal
  rw [show (∫ θ : FreeAngles V z, ∏ e, villainWeight β
      (pinnedAngle z θ (G.src e) - pinnedAngle z θ (G.tgt e) + s e) ∂rootedAngleMeasure z) =
      (∫ θ : FreeAngles V z, ∏ e, villainWeight β
      (pinnedAngle z θ (G.src e) - pinnedAngle z θ (G.tgt e) + s e) ∂μ) from rfl, hreal,
    hc, hP, ← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_mul,
    Complex.re_ofReal_mul, Complex.re_tsum hsum]
  congr 1
  refine tsum_congr fun q => ?_
  rw [Complex.re_ofReal_mul, show -Complex.I * ((∑ e, (q e : ℝ) * s e : ℝ) : ℂ) =
    ((-(∑ e, (q e : ℝ) * s e) : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.exp_ofReal_mul_I_re, Real.cos_neg]

/-- The bond-shift ratio `∏_e v_β(dθ_e + s_e)/v_β(dθ_e)` on the root-pinned angles: for
`s = 2πξ 𝟙_S` it is FS81's disorder operator (1.32) along the bonds `S`. -/
def villainShiftRatio (G : Multigraph V E) (z : V) (β : ℝ) (s : E → ℝ)
    (θ : FreeAngles V z) : ℝ :=
  ∏ e, villainWeight β (pinnedAngle z θ (G.src e) - pinnedAngle z θ (G.tgt e) + s e) /
    villainWeight β (pinnedAngle z θ (G.src e) - pinnedAngle z θ (G.tgt e))

/-- **The shifted Villain expectation as a current ratio** (FS81 (1.38), Appendix A, on a finite
rooted graph): `⟨∏_e v_β(dθ_e + s_e)/v_β(dθ_e)⟩ = ∑_q w(q) cos(∑_e q_e s_e) / ∑_q w(q)`, the sums
over the integer currents neutral away from the root. -/
theorem integral_villainShiftRatio (G : Multigraph V E) (z : V) (β : ℝ) (hβ : 0 < β)
    (s : E → ℝ) :
    (∫ θ, villainShiftRatio G z β s θ ∂rootedVillainMeasure G z β hβ) =
      (∑' q : E → ℤ, neutralCurrentGaussianWeight G z β q * Real.cos (∑ e, (q e : ℝ) * s e)) /
        ∑' q : E → ℤ, neutralCurrentGaussianWeight G z β q := by
  classical
  let ρ : FreeAngles V z → ENNReal := fun θ => ENNReal.ofReal (villainRealDensity G z β θ)
  have hρ : Measurable ρ := by
    dsimp [ρ]
    exact ENNReal.measurable_ofReal.comp (continuous_villainRealDensity G z β hβ).measurable
  have hρtop : ∀ᵐ θ ∂rootedAngleMeasure z, ρ θ < ⊤ :=
    Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  have hZ : 0 < villainPartitionFunction G z β := villain_partition_integral_pos G z β hβ
  have hscale : ((ENNReal.ofReal (villainPartitionFunction G z β))⁻¹).toReal =
      (villainPartitionFunction G z β)⁻¹ := by
    rw [ENNReal.toReal_inv, ENNReal.toReal_ofReal hZ.le]
  have hinner : (∫ θ, (ρ θ).toReal * villainShiftRatio G z β s θ ∂rootedAngleMeasure z) =
      ∫ θ, ∏ e, villainWeight β
        (pinnedAngle z θ (G.src e) - pinnedAngle z θ (G.tgt e) + s e) ∂rootedAngleMeasure z := by
    refine integral_congr_ae (ae_of_all _ fun θ => ?_)
    simp only [ρ]
    rw [ENNReal.toReal_ofReal (villainRealDensity_nonneg_le G z β hβ θ).1]
    simp only [villainRealDensity, villainShiftRatio]
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun e _ => ?_
    have hpos := VillainWeight.villainWeight_pos hβ
      (pinnedAngle z θ (G.src e) - pinnedAngle z θ (G.tgt e))
    field_simp
  rw [rootedVillainMeasure, MeasureTheory.integral_smul_measure, rootedVillainDensityMeasure,
    integral_withDensity_eq_integral_toReal_smul hρ hρtop, hscale]
  simp only [smul_eq_mul]
  rw [hinner, villain_shifted_partition_current_expansion G z β hβ s]
  have hZexp := villain_partition_current_expansion G z β hβ
  unfold villainPartitionFunction
  rw [hZexp]
  have hC : 0 < ((2 * Real.pi * β) ^ (-(1 / 2 : ℝ))) ^ Fintype.card E *
      (2 * Real.pi) ^ Fintype.card (FreeVertices V z) :=
    mul_pos (pow_pos (Real.rpow_pos_of_pos (by positivity) _) _) (pow_pos (by positivity) _)
  have hS := neutralCurrentGaussianWeight_tsum_pos G z β hβ
  field_simp

end FroehlichSpencer.BKT.Villain
