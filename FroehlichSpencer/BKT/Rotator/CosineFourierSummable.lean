/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Rotator.CosineFourier
public import FroehlichSpencer.BKT.Rotator.BesselInterp.CoeffBound

/-!
# Absolute summability of the cosine-bond Fourier coefficients

The plane-rotator coefficient `rotatorI b m = (2π)⁻¹ ∫₀^{2π} e^{b cos t} e^{imt} dt` of FS81 (1.34)
equals the Appendix B coefficient `besselCoeff b m`. From the exponential-series representation it
is real, nonnegative for `b ≥ 0` (positive for `b > 0`), and obeys the factorial bound
`‖rotatorI b m‖ ≤ |b|^{|m|} e^{|b|} / |m|!`. Hence it is absolutely summable, and the pointwise
Fourier expansion `e^{b cos t} = Σ_m rotatorI b m e^{imt}` holds unconditionally, with absolute
convergence.
-/

public section

noncomputable section

namespace FroehlichSpencer.BKT.Rotator

open Complex
open scoped Real
open FroehlichSpencer.BKT.Rotator.BesselInterp

local instance : Fact (0 < rotatorPeriod) := ⟨by
  dsimp [rotatorPeriod]
  positivity⟩

/-- The rotator coefficient of FS81 (1.34) is the Appendix B coefficient (B.1). -/
theorem rotatorI_eq_besselCoeff (b : ℝ) (m : ℤ) : rotatorI b m = besselCoeff b m := by
  unfold rotatorI besselCoeff rotatorBondReal
  congr 1
  refine intervalIntegral.integral_congr fun t _ => ?_
  ring_nf

/-- The rotator coefficient is real. -/
theorem rotatorI_eq_ofReal (b : ℝ) (m : ℤ) : rotatorI b m = (besselCoeffRe b m : ℂ) := by
  rw [rotatorI_eq_besselCoeff, besselCoeff_eq]

theorem rotatorI_im (b : ℝ) (m : ℤ) : (rotatorI b m).im = 0 := by
  rw [rotatorI_eq_ofReal, ofReal_im]

theorem rotatorI_re_nonneg {b : ℝ} (hb : 0 ≤ b) (m : ℤ) : 0 ≤ (rotatorI b m).re := by
  rw [rotatorI_eq_ofReal, ofReal_re]; exact besselCoeffRe_nonneg hb m

theorem rotatorI_re_pos {b : ℝ} (hb : 0 < b) (m : ℤ) : 0 < (rotatorI b m).re := by
  rw [rotatorI_eq_ofReal, ofReal_re]; exact besselCoeffRe_pos hb m

/-- The explicit factorial bound `‖rotatorI b m‖ ≤ |b|^{|m|} e^{|b|} / |m|!`. -/
theorem norm_rotatorI_le (b : ℝ) (m : ℤ) :
    ‖rotatorI b m‖ ≤ |b| ^ m.natAbs / (Nat.factorial m.natAbs) * Real.exp |b| := by
  rw [rotatorI_eq_ofReal, Complex.norm_real, Real.norm_eq_abs]
  exact abs_besselCoeffRe_le b m

lemma summable_factorial_majorant (b : ℝ) :
    Summable fun m : ℤ => |b| ^ m.natAbs / (Nat.factorial m.natAbs) * Real.exp |b| := by
  have hs := (NormedSpace.expSeries_div_summable (𝔸 := ℝ) |b|).mul_right (Real.exp |b|)
  refine Summable.of_nat_of_neg ?_ ?_
  · simpa using hs
  · simpa using hs

/-- The coefficients are absolutely summable. -/
theorem summable_norm_rotatorI (b : ℝ) : Summable fun m : ℤ => ‖rotatorI b m‖ :=
  (summable_factorial_majorant b).of_nonneg_of_le (fun _ => norm_nonneg _) (norm_rotatorI_le b)

theorem summable_rotatorI (b : ℝ) : Summable (rotatorI b) :=
  (summable_norm_rotatorI b).of_norm

/-- The pointwise Fourier expansion of the cosine bond on the circle, unconditionally. -/
theorem rotatorI_hasSum_fourier (b : ℝ) (x : AddCircle rotatorPeriod) :
    HasSum (fun m : ℤ => rotatorI b m * fourier m x) (rotatorBondCircle b x) :=
  rotatorI_hasPointwiseFourier b (summable_rotatorI b) x

/-- The expansion `e^{b cos t} = Σ_m rotatorI b m e^{imt}` for every real `t`; the series converges
absolutely by `summable_norm_rotatorI`, since `‖e^{imt}‖ = 1`. -/
theorem hasSum_rotatorI_mul_exp (b t : ℝ) :
    HasSum (fun m : ℤ => rotatorI b m * Complex.exp (Complex.I * m * t))
      (Complex.exp (b * Real.cos t)) := by
  have hp : (0 : ℝ) < rotatorPeriod := by unfold rotatorPeriod; positivity
  set t' := toIcoMod hp 0 t with ht'
  have hcoe : ((t' : ℝ) : AddCircle rotatorPeriod) = (t : AddCircle rotatorPeriod) := by
    rw [ht', ← self_sub_toIcoDiv_zsmul, QuotientAddGroup.mk_sub, QuotientAddGroup.mk_zsmul,
      AddCircle.coe_period, smul_zero, sub_zero]
  have hmem : t' ∈ Set.Ico 0 (0 + rotatorPeriod) := toIcoMod_mem_Ico hp 0 t
  have hval : rotatorBondCircle b (t : AddCircle rotatorPeriod) = Complex.exp (b * Real.cos t) := by
    rw [← hcoe]
    change AddCircle.liftIco rotatorPeriod 0 (rotatorBondReal b) _ = _
    rw [AddCircle.liftIco_coe_apply hmem]
    unfold rotatorBondReal
    rw [ht', ← self_sub_toIcoDiv_zsmul, zsmul_eq_mul]
    unfold rotatorPeriod
    rw [Real.cos_sub_int_mul_two_pi]
  have h := rotatorI_hasSum_fourier b (t : AddCircle rotatorPeriod)
  rw [hval] at h
  refine h.congr_fun fun m => ?_
  rw [fourier_coe_apply]
  congr 2
  unfold rotatorPeriod
  push_cast
  field_simp

end FroehlichSpencer.BKT.Rotator
