/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Rotator.BesselInterp.DebyeLog
public import FroehlichSpencer.BKT.Rotator.BesselInterp.Kernel
public import FroehlichSpencer.BKT.Rotator.BesselInterp.Asymptotic
public import Mathlib.Analysis.Calculus.LogDeriv
import FroehlichSpencer.BKT.Rotator.BesselInterp.Vertical
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# The defect series and the logarithm of the interpolation

For `β > 0` the coefficients `ln I_β(n) − ln L_β(n)` are bounded (`exists_abs_logDefect_le`), so the
exponent `S_β` of (B.14) is entire and can be differentiated termwise twice. On the strip
`|Im z| < β`, `I_β = exp (ℓ_β + S_β)` with the explicit logarithm `ℓ_β` of `L_β`; hence the
logarithmic derivative of `I_β` is `ℓ_β' + S_β'` and its derivative is `ℓ_β'' + S_β''`.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Rotator.BesselInterp

open Complex Metric Filter Topology
open scoped Real

/-- The first derivative of the defect series, `Σₙ cₙ K'(z - n)`. -/
def defectSeriesDeriv (β : ℝ) (z : ℂ) : ℂ :=
  ∑' n : ℤ, (logDefect β n : ℂ) * deriv sincSq (z - n)

/-- The second derivative of the defect series, `Σₙ cₙ K''(z - n)`. -/
def defectSeriesDeriv2 (β : ℝ) (z : ℂ) : ℂ :=
  ∑' n : ℤ, (logDefect β n : ℂ) * deriv (deriv sincSq) (z - n)

/-- The majorant constant of `K'`. -/
def kernelConst1 : ℝ := 3 * Real.exp (2 * π) * 2

/-- The majorant constant of `K''`. -/
def kernelConst2 : ℝ := 3 * Real.exp (2 * π) * kernelConst1

lemma kernelConst1_nonneg : 0 ≤ kernelConst1 := by unfold kernelConst1; positivity

lemma kernelConst2_nonneg : 0 ≤ kernelConst2 := by
  unfold kernelConst2; have := kernelConst1_nonneg; positivity

lemma differentiable_deriv_sincSq : Differentiable ℂ (deriv sincSq) :=
  differentiableOn_univ.mp (differentiable_sincSq.differentiableOn.deriv isOpen_univ)

lemma differentiable_deriv_deriv_sincSq : Differentiable ℂ (deriv (deriv sincSq)) :=
  differentiableOn_univ.mp (differentiable_deriv_sincSq.differentiableOn.deriv isOpen_univ)

lemma norm_deriv_sincSq_le_majorant (ζ : ℂ) :
    ‖deriv sincSq ζ‖ ≤ kernelConst1 * Real.exp (2 * π * |ζ.im|) / (1 + ζ.re ^ 2) :=
  norm_deriv_le_majorant differentiable_sincSq norm_sincSq_le_majorant ζ

lemma norm_deriv_deriv_sincSq_le_majorant (ζ : ℂ) :
    ‖deriv (deriv sincSq) ζ‖ ≤ kernelConst2 * Real.exp (2 * π * |ζ.im|) / (1 + ζ.re ^ 2) :=
  norm_deriv_le_majorant differentiable_deriv_sincSq norm_deriv_sincSq_le_majorant ζ

section Bounded

variable {β M : ℝ} (hM : ∀ n : ℤ, |logDefect β n| ≤ M)
include hM

lemma norm_logDefect_le (n : ℤ) : ‖(logDefect β n : ℂ)‖ ≤ M := by
  rw [Complex.norm_real, Real.norm_eq_abs]; exact hM n

theorem differentiable_defectSeries : Differentiable ℂ (defectSeries β) :=
  differentiable_tsum_shift differentiable_sincSq norm_sincSq_le_majorant (norm_logDefect_le hM)

theorem differentiable_defectSeriesDeriv : Differentiable ℂ (defectSeriesDeriv β) :=
  differentiable_tsum_shift differentiable_deriv_sincSq norm_deriv_sincSq_le_majorant
    (norm_logDefect_le hM)

theorem hasDerivAt_defectSeries (z : ℂ) :
    HasDerivAt (defectSeries β) (defectSeriesDeriv β z) z := by
  have h := (differentiable_defectSeries hM z).hasDerivAt
  have hd := deriv_tsum_shift differentiable_sincSq norm_sincSq_le_majorant (norm_logDefect_le hM)
  unfold defectSeries at h ⊢
  rw [hd] at h
  exact h

theorem hasDerivAt_defectSeriesDeriv (z : ℂ) :
    HasDerivAt (defectSeriesDeriv β) (defectSeriesDeriv2 β z) z := by
  have h := (differentiable_defectSeriesDeriv hM z).hasDerivAt
  have hd := deriv_tsum_shift differentiable_deriv_sincSq norm_deriv_sincSq_le_majorant
    (norm_logDefect_le hM)
  unfold defectSeriesDeriv at h ⊢
  rw [hd] at h
  exact h

theorem norm_defectSeries_le (z : ℂ) :
    ‖defectSeries β z‖ ≤ M * 2 * Real.exp (2 * π * |z.im|) * (3 * latticeSum) :=
  norm_tsum_shift_le norm_sincSq_le_majorant (norm_logDefect_le hM) z

theorem norm_defectSeriesDeriv_le (z : ℂ) :
    ‖defectSeriesDeriv β z‖ ≤ M * kernelConst1 * Real.exp (2 * π * |z.im|) * (3 * latticeSum) :=
  norm_tsum_shift_le norm_deriv_sincSq_le_majorant (norm_logDefect_le hM) z

theorem norm_defectSeriesDeriv2_le (z : ℂ) :
    ‖defectSeriesDeriv2 β z‖ ≤ M * kernelConst2 * Real.exp (2 * π * |z.im|) * (3 * latticeSum) :=
  norm_tsum_shift_le norm_deriv_deriv_sincSq_le_majorant (norm_logDefect_le hM) z

end Bounded

/-- The defect series is real on the real axis. -/
theorem defectSeries_ofReal (β t : ℝ) :
    defectSeries β t = ((∑' n : ℤ, logDefect β n * Real.sinc (π * (t - n)) ^ 2 : ℝ) : ℂ) := by
  unfold defectSeries
  rw [Complex.ofReal_tsum]
  refine tsum_congr fun n => ?_
  have : ((t : ℂ) - n) = ((t - n : ℝ) : ℂ) := by push_cast; ring
  rw [this, sincSq_ofReal]
  push_cast; ring

theorem defectSeriesDeriv_ofReal_im {β : ℝ} (hβ : 0 < β) (x : ℝ) :
    (defectSeriesDeriv β x).im = 0 := by
  obtain ⟨M, -, hM⟩ := exists_abs_logDefect_le hβ
  exact im_eq_zero_of_hasDerivAt_of_real (hasDerivAt_defectSeries hM x)
    fun t => by rw [defectSeries_ofReal, ofReal_im]

/-! ### The logarithm of the interpolation on the strip -/

/-- The holomorphic logarithm `ℓ_β + S_β` of `I_β` on the strip `|Im z| < β`. -/
def interpLog (β : ℝ) (z : ℂ) : ℂ := debyeLog β z + defectSeries β z

/-- Its derivative `ℓ_β' + S_β'`. -/
def interpLogDeriv (β : ℝ) (z : ℂ) : ℂ := debyeLogDeriv β z + defectSeriesDeriv β z

/-- Its second derivative `ℓ_β'' + S_β''`. -/
def interpLogDeriv2 (β : ℝ) (z : ℂ) : ℂ := debyeLogDeriv2 β z + defectSeriesDeriv2 β z

lemma isOpen_strip (β : ℝ) : IsOpen {z : ℂ | |z.im| < β} :=
  isOpen_lt (continuous_abs.comp continuous_im) continuous_const

theorem besselInterp_eq_exp_interpLog {β : ℝ} (hβ : 0 < β) {z : ℂ} (hz : |z.im| < β) :
    besselInterp β z = Complex.exp (interpLog β z) := by
  unfold besselInterp defectFactor interpLog
  rw [debye_eq_exp_debyeLog hβ hz, Complex.exp_add]

theorem besselInterp_eventuallyEq {β : ℝ} (hβ : 0 < β) {z : ℂ} (hz : |z.im| < β) :
    besselInterp β =ᶠ[𝓝 z] fun w => Complex.exp (interpLog β w) :=
  Filter.eventually_of_mem ((isOpen_strip β).mem_nhds hz)
    fun _ hw => besselInterp_eq_exp_interpLog hβ hw

theorem hasDerivAt_interpLog {β : ℝ} (hβ : 0 < β) {z : ℂ} (hz : |z.im| < β) :
    HasDerivAt (interpLog β) (interpLogDeriv β z) z := by
  obtain ⟨M, -, hM⟩ := exists_abs_logDefect_le hβ
  exact (hasDerivAt_debyeLog hβ hz).add (hasDerivAt_defectSeries hM z)

theorem hasDerivAt_interpLogDeriv {β : ℝ} (hβ : 0 < β) {z : ℂ} (hz : |z.im| < β) :
    HasDerivAt (interpLogDeriv β) (interpLogDeriv2 β z) z := by
  obtain ⟨M, -, hM⟩ := exists_abs_logDefect_le hβ
  exact (hasDerivAt_debyeLogDeriv hβ hz).add (hasDerivAt_defectSeriesDeriv hM z)

theorem hasDerivAt_besselInterp {β : ℝ} (hβ : 0 < β) {z : ℂ} (hz : |z.im| < β) :
    HasDerivAt (besselInterp β) (Complex.exp (interpLog β z) * interpLogDeriv β z) z :=
  ((hasDerivAt_interpLog hβ hz).cexp).congr_of_eventuallyEq (besselInterp_eventuallyEq hβ hz)

/-- The logarithmic derivative of `I_β` on the strip. -/
theorem logDeriv_besselInterp {β : ℝ} (hβ : 0 < β) {z : ℂ} (hz : |z.im| < β) :
    logDeriv (besselInterp β) z = interpLogDeriv β z := by
  rw [logDeriv_apply, (hasDerivAt_besselInterp hβ hz).deriv, besselInterp_eq_exp_interpLog hβ hz]
  field_simp [Complex.exp_ne_zero]

/-- The derivative of the logarithmic derivative of `I_β` on the strip. -/
theorem deriv_logDeriv_besselInterp {β : ℝ} (hβ : 0 < β) {z : ℂ} (hz : |z.im| < β) :
    deriv (logDeriv (besselInterp β)) z = interpLogDeriv2 β z := by
  have heq : logDeriv (besselInterp β) =ᶠ[𝓝 z] interpLogDeriv β :=
    Filter.eventually_of_mem ((isOpen_strip β).mem_nhds hz) fun _ hw => logDeriv_besselInterp hβ hw
  rw [heq.deriv_eq]
  exact (hasDerivAt_interpLogDeriv hβ hz).deriv

end FroehlichSpencer.BKT.Rotator.BesselInterp
