/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Villain.Expansion

/-!
# Integrating finite-graph Villain current terms

The summability majorant and the termwise integral exchange are the finite-dimensional analytic
step in the Villain current expansion (KP §6.1, p. 33).
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace FroehlichSpencer.BKT.Villain

variable {E : Type*} [Fintype E]

/-- The Gaussian current weights are summable on every finite edge type. -/
theorem currentGaussianWeight_summable (β : ℝ) (hβ : 0 < β) :
    Summable (fun q : E → ℤ => currentGaussianWeight β q) := by
  classical
  let a : E → ℤ → ℂ := fun _ m => (Real.exp (-((m : ℝ) ^ 2) / (2 * β)) : ℂ)
  have ha : ∀ e, Summable (fun m : ℤ => ‖a e m‖) := by
    intro e
    have h := FroehlichSpencer.BKT.VillainWeight.villainWeight_fourier_coeff_summable hβ
    apply h.congr
    intro m
    change Real.exp (-((m : ℝ) ^ 2) / (2 * β)) =
      ‖(Real.exp (-((m : ℝ) ^ 2) / (2 * β)) : ℂ)‖
    symm
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hprod := summable_norm_prod_currents a ha
  apply hprod.congr
  intro q
  change ‖∏ e, (Real.exp (-((q e : ℝ) ^ 2) / (2 * β)) : ℂ)‖ =
    currentGaussianWeight β q
  rw [Complex.norm_prod, currentGaussianWeight]
  apply Finset.prod_congr rfl
  intro e he
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]

/-- The current Fourier character has norm one. -/
theorem currentFourierTerm_norm (G : Multigraph V E) (z : V) (β : ℝ) (q : E → ℤ)
    (θ : FreeAngles V z) :
    ‖currentFourierTerm G z β q θ‖ = currentGaussianWeight β q := by
  classical
  have hweight : 0 < currentGaussianWeight β q := by
    unfold currentGaussianWeight
    exact Finset.prod_pos fun e he => Real.exp_pos _
  rw [currentFourierTerm, Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hweight, Complex.norm_prod]
  have hphase (j : FreeVertices V z) :
      ‖Complex.exp (Complex.I * (-(currentDivergence G q j.1) : ℂ) * (θ j : ℂ))‖ = 1 := by
    rw [Complex.norm_exp]
    have hre :
        (Complex.I * (-(currentDivergence G q j.1) : ℂ) * (θ j : ℂ)).re = 0 := by
      simp [Complex.mul_re]
    rw [hre, Real.exp_zero]
  rw [show ∏ j : FreeVertices V z,
      ‖Complex.exp (Complex.I * (-(currentDivergence G q j.1) : ℂ) * (θ j : ℂ))‖ = 1 by
        apply Finset.prod_eq_one
        intro j hj
        exact hphase j]
  simp

/-- Every current term is continuous in the free vertex angles. -/
theorem continuous_currentFourierTerm (G : Multigraph V E) (z : V) (β : ℝ) (q : E → ℤ) :
    Continuous (fun θ : FreeAngles V z => currentFourierTerm G z β q θ) := by
  unfold currentFourierTerm
  fun_prop

/-- Integrating the Fourier series may be done term by term. The absolute-integrability condition
is supplied by the summable Gaussian current weights. -/
theorem integral_currentFourierTerm_tsum (G : Multigraph V E) (z : V) (β : ℝ)
    (hβ : 0 < β) :
    (∫ θ, ∑' q : E → ℤ, currentFourierTerm G z β q θ ∂rootedAngleMeasure z) =
      ∑' q : E → ℤ, ∫ θ, currentFourierTerm G z β q θ ∂rootedAngleMeasure z := by
  classical
  let μ := rootedAngleMeasure z
  have hfinite : IsFiniteMeasure μ := by
    dsimp [μ, rootedAngleMeasure]
    infer_instance
  change (∫ θ, ∑' q : E → ℤ, currentFourierTerm G z β q θ ∂μ) = _
  apply integral_tsum
  · intro q
    exact (continuous_currentFourierTerm G z β q).aestronglyMeasurable
  · have hweight := currentGaussianWeight_summable (E := E) β hβ
    have hsum :
        (∑' q : E → ℤ, ENNReal.ofReal (currentGaussianWeight β q)) ≠ ⊤ :=
      hweight.tsum_ofReal_ne_top
    have hμ : μ Set.univ ≠ ⊤ := ne_of_lt hfinite.measure_univ_lt_top
    have hconst (q : E → ℤ) :
        (∫⁻ θ, ‖currentFourierTerm G z β q θ‖ₑ ∂μ) =
          ENNReal.ofReal (currentGaussianWeight β q) * μ Set.univ := by
      have hpoint (θ : FreeAngles V z) :
          ‖currentFourierTerm G z β q θ‖ₑ =
            ENNReal.ofReal (currentGaussianWeight β q) := by
        calc
          ‖currentFourierTerm G z β q θ‖ₑ =
              ENNReal.ofReal ‖currentFourierTerm G z β q θ‖ :=
            (ofReal_norm (currentFourierTerm G z β q θ)).symm
          _ = ENNReal.ofReal (currentGaussianWeight β q) := by
            rw [currentFourierTerm_norm G z β q θ]
      rw [show (fun θ : FreeAngles V z => ‖currentFourierTerm G z β q θ‖ₑ) =
          fun _ => ENNReal.ofReal (currentGaussianWeight β q) from funext hpoint]
      simp [lintegral_const]
    calc
      (∑' q : E → ℤ, ∫⁻ θ, ‖currentFourierTerm G z β q θ‖ₑ ∂μ) =
          ∑' q : E → ℤ,
            ENNReal.ofReal (currentGaussianWeight β q) * μ Set.univ := by
        apply tsum_congr
        exact hconst
      _ = (∑' q : E → ℤ, ENNReal.ofReal (currentGaussianWeight β q)) * μ Set.univ := by
        rw [ENNReal.tsum_mul_right]
      _ ≠ ⊤ := ENNReal.mul_ne_top hsum hμ

end FroehlichSpencer.BKT.Villain

end
