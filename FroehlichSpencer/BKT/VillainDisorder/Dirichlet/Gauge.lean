/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.VillainDisorder.Dirichlet.TheoremD
public import FroehlichSpencer.BKT.Ginibre.Models
public import FroehlichSpencer.BKT.Villain.TheoremC.FiniteBox
import Mathlib.Tactic

/-! # Gauge fixing for the fractional Villain disorder observable

The shifted-bond ratio is invariant under a global rotation. Fourier expansion makes the gauge
quotient exact: the full product-circle integral imposes zero divergence at every vertex, and
current conservation makes this equivalent to the rooted constraints. The resulting full free-box
expectation agrees with the root-pinned expectation and therefore with the centered Dirichlet
cosine expectation.
-/

@[expose] public section

open MeasureTheory
open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Ginibre
open FroehlichSpencer.BKT.Villain
open FroehlichSpencer.BKT.Villain.TheoremC
open FroehlichSpencer.BKT.VillainDisorder.Dirichlet
open FroehlichSpencer.BKT.Rotator
open FroehlichSpencer.BKT.Rotator.Ginibre

noncomputable section
namespace FroehlichSpencer.BKT.VillainDisorder.Dirichlet

private theorem currentFourierTerm_fullAnglePinned_eq_character
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : Multigraph V E) (z : V) (β : ℝ) (q : E → ℤ) (θ : V → ℝ) :
    currentFourierTerm G z β q (fullAnglePinned z θ) =
      (currentGaussianWeight β q : ℂ) *
        character (fun v => -currentDivergence G q v) θ := by
  classical
  unfold currentFourierTerm character
  have hsum : (∑ j : FreeVertices V z,
      (-(currentDivergence G q j.1) : ℂ) * (θ j.1 - θ z : ℝ)) =
      ∑ v : V, (-(currentDivergence G q v) : ℂ) * (θ v : ℂ) := by
    have htotal : (∑ v : V, (-(currentDivergence G q v) : ℂ)) = 0 := by
      have h := sum_currentDivergence_eq_zero G q
      have hcast : (∑ v : V, (currentDivergence G q v : ℂ)) = 0 := by
        exact_mod_cast h
      simpa only [Int.cast_neg, Finset.sum_neg_distrib, neg_zero] using
        congrArg (fun x : ℂ => -x) hcast
    rw [Fintype.sum_eq_add_sum_subtype_ne
      (fun v : V => (-(currentDivergence G q v) : ℂ) * (θ v : ℂ)) z]
    have hcoeff : (-(currentDivergence G q z) : ℂ) =
        -∑ j : FreeVertices V z, (-(currentDivergence G q j.1) : ℂ) := by
      have hsplit := Fintype.sum_eq_add_sum_subtype_ne
        (fun v : V => (-(currentDivergence G q v) : ℂ)) z
      rw [hsplit] at htotal
      linear_combination htotal
    have hleft : (∑ j : FreeVertices V z,
        (-(currentDivergence G q j.1) : ℂ) * (θ j.1 - θ z : ℝ)) =
        (∑ j : FreeVertices V z,
          (-(currentDivergence G q j.1) : ℂ) * (θ j.1 : ℂ)) -
          (∑ j : FreeVertices V z, (-(currentDivergence G q j.1) : ℂ)) * (θ z : ℂ) := by
      simp only [Complex.ofReal_sub, mul_sub, Finset.sum_sub_distrib, Finset.sum_mul]
    rw [hleft, hcoeff]
    ring
  have hexp : (∑ j : FreeVertices V z,
      Complex.I * (-(currentDivergence G q j.1) : ℂ) *
        (((fullAnglePinned z θ) j : ℝ) : ℂ)) =
      ∑ v : V, Complex.I * (-(currentDivergence G q v) : ℂ) * (θ v : ℂ) := by
    change (∑ j : FreeVertices V z,
      Complex.I * (-(currentDivergence G q j.1) : ℂ) *
        ((θ j.1 - θ z : ℝ) : ℂ)) = _
    calc
      _ = Complex.I * ∑ j : FreeVertices V z,
          (-(currentDivergence G q j.1) : ℂ) * ((θ j.1 - θ z : ℝ) : ℂ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring_nf
      _ = Complex.I * ∑ v : V,
          (-(currentDivergence G q v) : ℂ) * (θ v : ℂ) := by rw [hsum]
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro v hv
        ring
  simp only [fullAnglePinned]
  rw [← Complex.exp_sum, ← Complex.exp_sum]
  have hexp' := hexp
  simp only [fullAnglePinned] at hexp'
  rw [hexp']
  simp only [Int.cast_neg]

private theorem neutralAwayFrom_iff_all_divergences_zero
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : Multigraph V E) (z : V) (q : E → ℤ) :
    neutralAwayFrom G z q ↔ ∀ v, currentDivergence G q v = 0 := by
  constructor
  · intro h v
    by_cases hv : v = z
    · subst v
      have hsum := sum_currentDivergence_eq_zero G q
      rw [← Finset.add_sum_erase (s := Finset.univ)
        (f := currentDivergence G q) (Finset.mem_univ z)] at hsum
      have hrest : ∑ w ∈ Finset.univ.erase z, currentDivergence G q w = 0 := by
        apply Finset.sum_eq_zero
        intro w hw
        exact h w (Finset.ne_of_mem_erase hw)
      rw [hrest, add_zero] at hsum
      exact hsum
    · exact h v hv
  · intro h v hv
    exact h v

private theorem integral_character_siteProduct_circle
    {V : Type*} [Fintype V] (n : V → ℤ) :
    (∫ θ : V → ℝ, character n θ ∂siteProduct circleMeasure V) =
      if n = 0 then ((2 * Real.pi : ℝ) ^ Fintype.card V : ℂ) else 0 := by
  rw [integral_character_siteProduct hasRealFourier_circle]
  by_cases hn : n = 0
  · simp [hn, circleFourier]
  · have hnot : ∃ v, n v ≠ 0 := by
      by_contra h
      apply hn
      funext v
      exact not_not.mp (not_exists.mp h v)
    obtain ⟨v, hv⟩ := hnot
    have hzero : circleFourier (n v) = 0 := by simp [circleFourier, hv]
    rw [ite_eq_right (fun h => hn h), Finset.prod_eq_zero (Finset.mem_univ v) hzero]
    simp

private theorem currentFourierTerm_fullAnglePinned_integral
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : Multigraph V E) (z : V) (β : ℝ) (q : E → ℤ)
    [Decidable (neutralAwayFrom G z q)] :
    (∫ θ : V → ℝ,
      currentFourierTerm G z β q (fullAnglePinned z θ) ∂siteProduct circleMeasure V) =
      if neutralAwayFrom G z q then
        (currentGaussianWeight β q : ℂ) * (2 * Real.pi : ℂ) ^ Fintype.card V else 0 := by
  classical
  have hpoint : (fun θ : V → ℝ => currentFourierTerm G z β q
      (fullAnglePinned z θ)) = fun θ =>
        (currentGaussianWeight β q : ℂ) *
          character (fun v => -currentDivergence G q v) θ := by
    funext θ
    exact currentFourierTerm_fullAnglePinned_eq_character G z β q θ
  rw [hpoint]
  rw [integral_const_mul, integral_character_siteProduct_circle]
  by_cases hn : neutralAwayFrom G z q
  · have hfreq : (fun v => -currentDivergence G q v) = 0 := by
      funext v
      exact neg_eq_zero.mpr
        ((neutralAwayFrom_iff_all_divergences_zero G z q).mp hn v)
    simp [hn, hfreq]
  · have hfreq : (fun v => -currentDivergence G q v) ≠ 0 := by
      intro hzero
      apply hn
      apply (neutralAwayFrom_iff_all_divergences_zero G z q).mpr
      intro v
      have hv := congrFun hzero v
      exact neg_eq_zero.mp hv
    simp [hn, hfreq]

private theorem shiftedCurrentFourierTerm_fullAnglePinned_integral
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : Multigraph V E) (z : V) (β : ℝ) (s : E → ℝ) (q : E → ℤ)
    [Decidable (neutralAwayFrom G z q)] :
    (∫ θ : V → ℝ,
      shiftedCurrentFourierTerm G z β s q (fullAnglePinned z θ)
        ∂siteProduct circleMeasure V) =
      if neutralAwayFrom G z q then
        (currentGaussianWeight β q : ℂ) * (2 * Real.pi : ℂ) ^ Fintype.card V *
          Complex.exp (-Complex.I * ((∑ e, (q e : ℝ) * s e : ℝ) : ℂ)) else 0 := by
  classical
  unfold shiftedCurrentFourierTerm
  rw [integral_mul_const, currentFourierTerm_fullAnglePinned_integral]
  by_cases hn : neutralAwayFrom G z q
  · simp only [hn, ↓reduceIte]
  · simp only [hn, ↓reduceIte]
    simp

private theorem villain_shifted_partition_full_complex
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : Multigraph V E) (z : V) (β : ℝ) (hβ : 0 < β) (s : E → ℝ) :
    (∫ θ : V → ℝ,
      ∏ e, (villainWeight β (θ (G.src e) - θ (G.tgt e) + s e) : ℂ)
        ∂siteProduct circleMeasure V) =
      (((2 * Real.pi * β) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) ^ Fintype.card E *
        ((2 * Real.pi : ℝ) ^ Fintype.card V : ℂ) *
          ∑' q : E → ℤ,
            (neutralCurrentGaussianWeight G z β q : ℂ) *
              Complex.exp (-Complex.I * ((∑ e, (q e : ℝ) * s e : ℝ) : ℂ)) := by
  classical
  let μ := siteProduct circleMeasure V
  have hfinite : IsFiniteMeasure μ := by
    dsimp [μ, siteProduct]
    infer_instance
  have hpinned (θ : V → ℝ) (j : V) :
      pinnedAngle z (fullAnglePinned z θ) j = θ j - θ z := by
    by_cases hj : j = z
    · subst j
      simp [pinnedAngle]
    · simp [pinnedAngle, fullAnglePinned, hj]
  have hpoint : (fun θ : V → ℝ =>
      ∏ e, (villainWeight β (θ (G.src e) - θ (G.tgt e) + s e) : ℂ)) =
      fun θ => (((2 * Real.pi * β) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) ^ Fintype.card E *
        ∑' q : E → ℤ, shiftedCurrentFourierTerm G z β s q (fullAnglePinned z θ) := by
    funext θ
    calc
      _ = ∏ e, (villainWeight β
          (pinnedAngle z (fullAnglePinned z θ) (G.src e) -
            pinnedAngle z (fullAnglePinned z θ) (G.tgt e) + s e) : ℂ) := by
        apply Finset.prod_congr rfl
        intro e he
        rw [hpinned θ (G.src e), hpinned θ (G.tgt e)]
        congr 1
        ring_nf
      _ = _ := villain_shifted_product_fourier_pointwise G z β hβ s
        (fullAnglePinned z θ)
  have hmajorant (q : E → ℤ) :
      (∫⁻ θ, ‖shiftedCurrentFourierTerm G z β s q (fullAnglePinned z θ)‖ₑ ∂μ) =
        ENNReal.ofReal (currentGaussianWeight β q) * μ Set.univ := by
    have hpointwise (θ : V → ℝ) :
        ‖shiftedCurrentFourierTerm G z β s q (fullAnglePinned z θ)‖ₑ =
          ENNReal.ofReal (currentGaussianWeight β q) := by
      rw [← ofReal_norm, shiftedCurrentFourierTerm_norm]
    rw [show (fun θ : V → ℝ =>
        ‖shiftedCurrentFourierTerm G z β s q (fullAnglePinned z θ)‖ₑ) =
        fun _ => ENNReal.ofReal (currentGaussianWeight β q) from funext hpointwise]
    simp [lintegral_const]
  have hint :
      (∫ θ, ∑' q : E → ℤ,
        shiftedCurrentFourierTerm G z β s q (fullAnglePinned z θ) ∂μ) =
      ∑' q : E → ℤ,
        ∫ θ, shiftedCurrentFourierTerm G z β s q (fullAnglePinned z θ) ∂μ := by
    apply integral_tsum
    · intro q
      have hcont : Continuous (fun θ : V → ℝ =>
          shiftedCurrentFourierTerm G z β s q (fullAnglePinned z θ)) := by
        have hfull : Continuous (fullAnglePinned z : (V → ℝ) → FreeAngles V z) := by
          unfold fullAnglePinned
          fun_prop
        exact (continuous_currentFourierTerm G z β q |>.mul continuous_const).comp hfull
      exact hcont.aestronglyMeasurable
    · have hweight := currentGaussianWeight_summable (E := E) β hβ
      have hsum :
          (∑' q : E → ℤ, ENNReal.ofReal (currentGaussianWeight β q)) ≠ ⊤ :=
        hweight.tsum_ofReal_ne_top
      have hμ : μ Set.univ ≠ ⊤ := ne_of_lt hfinite.measure_univ_lt_top
      calc
        (∑' q : E → ℤ,
            ∫⁻ θ, ‖shiftedCurrentFourierTerm G z β s q (fullAnglePinned z θ)‖ₑ ∂μ) =
          ∑' q : E → ℤ, ENNReal.ofReal (currentGaussianWeight β q) * μ Set.univ := by
            exact tsum_congr hmajorant
        _ = (∑' q : E → ℤ, ENNReal.ofReal (currentGaussianWeight β q)) * μ Set.univ :=
          ENNReal.tsum_mul_right
        _ ≠ ⊤ := ENNReal.mul_ne_top hsum hμ
  have hsum : Summable (fun q : E → ℤ =>
      (neutralCurrentGaussianWeight G z β q : ℂ) *
        Complex.exp (-Complex.I * ((∑ e, (q e : ℝ) * s e : ℝ) : ℂ))) := by
    refine Summable.of_norm_bounded
      (neutralCurrentGaussianWeight_summable G z β hβ) fun q => ?_
    rw [norm_mul, Complex.norm_real, Complex.norm_exp]
    have hre : (-Complex.I * ((∑ e, (q e : ℝ) * s e : ℝ) : ℂ)).re = 0 := by
      simp [Complex.mul_re]
    rw [hre, Real.exp_zero, mul_one, Real.norm_eq_abs]
    have hnonneg : 0 ≤ neutralCurrentGaussianWeight G z β q := by
      unfold neutralCurrentGaussianWeight
      split_ifs
      · exact (currentGaussianWeight_pos β q).le
      · exact le_rfl
    rw [abs_of_nonneg hnonneg]
  have hsumterm :
      (∑' q : E → ℤ,
        if neutralAwayFrom G z q then
          (currentGaussianWeight β q : ℂ) * (2 * Real.pi : ℂ) ^ Fintype.card V *
            Complex.exp (-Complex.I * ((∑ e, (q e : ℝ) * s e : ℝ) : ℂ)) else 0) =
      (2 * Real.pi : ℂ) ^ Fintype.card V *
        ∑' q : E → ℤ,
          (neutralCurrentGaussianWeight G z β q : ℂ) *
            Complex.exp (-Complex.I * ((∑ e, (q e : ℝ) * s e : ℝ) : ℂ)) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro q
    by_cases hn : neutralAwayFrom G z q
    · simp [neutralCurrentGaussianWeight, hn]
      ring_nf
    · simp [neutralCurrentGaussianWeight, hn]
  calc
    _ = ∫ θ : V → ℝ,
        (((2 * Real.pi * β) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) ^ Fintype.card E *
          ∑' q : E → ℤ, shiftedCurrentFourierTerm G z β s q (fullAnglePinned z θ) ∂μ := by
      rw [show (fun θ : V → ℝ =>
          ∏ e, (villainWeight β (θ (G.src e) - θ (G.tgt e) + s e) : ℂ)) =
          fun θ => (((2 * Real.pi * β) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) ^ Fintype.card E *
            ∑' q : E → ℤ, shiftedCurrentFourierTerm G z β s q (fullAnglePinned z θ)
          from hpoint]
    _ = (((2 * Real.pi * β) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) ^ Fintype.card E *
          ∫ θ, ∑' q : E → ℤ,
            shiftedCurrentFourierTerm G z β s q (fullAnglePinned z θ) ∂μ :=
      integral_const_mul _ _
    _ = (((2 * Real.pi * β) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) ^ Fintype.card E *
          ∑' q : E → ℤ,
            ∫ θ, shiftedCurrentFourierTerm G z β s q (fullAnglePinned z θ) ∂μ := by rw [hint]
    _ = (((2 * Real.pi * β) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) ^ Fintype.card E *
          ∑' q : E → ℤ,
            (if neutralAwayFrom G z q then
              (currentGaussianWeight β q : ℂ) * (2 * Real.pi : ℂ) ^ Fintype.card V *
                Complex.exp (-Complex.I * ((∑ e, (q e : ℝ) * s e : ℝ) : ℂ)) else 0) := by
      congr 1
      apply tsum_congr
      intro q
      exact shiftedCurrentFourierTerm_fullAnglePinned_integral G z β s q
    _ = _ := by
      rw [hsumterm, ← mul_assoc, Complex.ofReal_mul]
      simp only [Complex.ofReal_ofNat]

private theorem villain_shifted_partition_full_real
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : Multigraph V E) (z : V) (β : ℝ) (hβ : 0 < β) (s : E → ℝ) :
    (∫ θ : V → ℝ,
      ∏ e, villainWeight β (θ (G.src e) - θ (G.tgt e) + s e)
        ∂siteProduct circleMeasure V) =
      ((2 * Real.pi * β) ^ (-(1 / 2 : ℝ))) ^ Fintype.card E *
        (2 * Real.pi) ^ Fintype.card V *
          ∑' q : E → ℤ,
            neutralCurrentGaussianWeight G z β q *
              Real.cos (∑ e, (q e : ℝ) * s e) := by
  classical
  let c : ℝ := (2 * Real.pi * β) ^ (-(1 / 2 : ℝ))
  let m : ℝ := (2 * Real.pi) ^ Fintype.card V
  have hweightCos : Summable (fun q : E → ℤ =>
      neutralCurrentGaussianWeight G z β q *
        Real.cos (∑ e, (q e : ℝ) * s e)) := by
    refine Summable.of_norm_bounded
      (neutralCurrentGaussianWeight_summable G z β hβ) fun q => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg]
    · exact mul_le_of_le_one_right
        (by
          unfold neutralCurrentGaussianWeight
          split_ifs
          · exact (currentGaussianWeight_pos β q).le
          · exact le_rfl)
        (Real.abs_cos_le_one _)
    · unfold neutralCurrentGaussianWeight
      split_ifs
      · exact (currentGaussianWeight_pos β q).le
      · exact le_rfl
  have hcomplexSummable : Summable (fun q : E → ℤ =>
      (neutralCurrentGaussianWeight G z β q : ℂ) *
        Complex.exp (-Complex.I * ((∑ e, (q e : ℝ) * s e : ℝ) : ℂ))) := by
    refine Summable.of_norm_bounded
      (neutralCurrentGaussianWeight_summable G z β hβ) fun q => ?_
    rw [norm_mul, Complex.norm_real, Complex.norm_exp]
    have hre : (-Complex.I * ((∑ e, (q e : ℝ) * s e : ℝ) : ℂ)).re = 0 := by
      simp [Complex.mul_re]
    rw [hre, Real.exp_zero, mul_one, Real.norm_eq_abs]
    have hnonneg : 0 ≤ neutralCurrentGaussianWeight G z β q := by
      unfold neutralCurrentGaussianWeight
      split_ifs
      · exact (currentGaussianWeight_pos β q).le
      · exact le_rfl
    rw [abs_of_nonneg hnonneg]
  have hrealSeries :
      Complex.re (∑' q : E → ℤ,
        (neutralCurrentGaussianWeight G z β q : ℂ) *
          Complex.exp (-Complex.I * ((∑ e, (q e : ℝ) * s e : ℝ) : ℂ))) =
        ∑' q : E → ℤ,
          neutralCurrentGaussianWeight G z β q *
            Real.cos (∑ e, (q e : ℝ) * s e) := by
    rw [Complex.re_tsum hcomplexSummable]
    apply tsum_congr
    intro q
    have hphase :
        (Complex.exp (-Complex.I * ((∑ e, (q e : ℝ) * s e : ℝ) : ℂ))).re =
          Real.cos (∑ e, (q e : ℝ) * s e) := by
      rw [show -Complex.I * ((∑ e, (q e : ℝ) * s e : ℝ) : ℂ) =
          ((-(∑ e, (q e : ℝ) * s e) : ℝ) : ℂ) * Complex.I by push_cast; ring,
        Complex.exp_ofReal_mul_I_re, Real.cos_neg]
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, hphase]
    ring
  have hcast :
      ((∫ θ : V → ℝ,
        ∏ e, villainWeight β (θ (G.src e) - θ (G.tgt e) + s e)
          ∂siteProduct circleMeasure V : ℝ) : ℂ) =
        ∫ θ : V → ℝ,
          ∏ e, (villainWeight β (θ (G.src e) - θ (G.tgt e) + s e) : ℂ)
            ∂siteProduct circleMeasure V := by
    calc
      _ = ∫ θ : V → ℝ,
          ((∏ e, villainWeight β (θ (G.src e) - θ (G.tgt e) + s e) : ℝ) : ℂ)
            ∂siteProduct circleMeasure V :=
        (integral_ofReal (f := fun θ : V → ℝ =>
          ∏ e, villainWeight β (θ (G.src e) - θ (G.tgt e) + s e))).symm
      _ = _ := by
        apply integral_congr_ae
        filter_upwards with θ
        simp only [Complex.ofReal_prod]
  have hcoef :
      (((2 * Real.pi * β) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) ^ Fintype.card E *
          ((2 * Real.pi : ℝ) ^ Fintype.card V : ℂ) =
        ((c ^ Fintype.card E * m : ℝ) : ℂ) := by
    simp [c, m, Complex.ofReal_mul, Complex.ofReal_pow]
  have h := congrArg Complex.re
    (hcast.trans (villain_shifted_partition_full_complex G z β hβ s))
  rw [Complex.ofReal_re, hcoef, Complex.re_ofReal_mul, hrealSeries] at h
  simpa [c, m] using h

def fullVillainShiftRatio {V E : Type*} [Fintype V] [Fintype E]
    (G : Multigraph V E) (β : ℝ) (s : E → ℝ) (θ : V → ℝ) : ℝ :=
  ∏ e, villainWeight β (θ (G.src e) - θ (G.tgt e) + s e) /
    villainWeight β (θ (G.src e) - θ (G.tgt e))

theorem fullVillainShiftRatio_integral_eq_rooted
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : Multigraph V E) (z : V) (β : ℝ) (hβ : 0 < β) (s : E → ℝ) :
    (∫ θ : V → ℝ, fullVillainShiftRatio G β s θ ∂villainGraphGibbs G β) =
      ∫ θ : FreeAngles V z, villainShiftRatio G z β s θ ∂rootedVillainMeasure G z β hβ := by
  classical
  let d : E → Frequency V := multigraphFrequency G
  let w : E → ℝ → ℝ := fun _ => villainWeight β
  have hw : ∀ e, IsBondWeight (w e) := by
    intro e
    simpa [w] using isBondWeight_villain hβ
  have hdenRaw : pairPartition circleMeasure d w =
      ∫ θ : V → ℝ,
        ∏ e, villainWeight β (θ (G.src e) - θ (G.tgt e))
          ∂siteProduct circleMeasure V := by
    rw [pairPartition]
    apply integral_congr_ae
    filter_upwards with θ
    simp [pairWeight, d, w, phase_multigraphFrequency]
  have hnumRaw : ∫ θ : V → ℝ, fullVillainShiftRatio G β s θ
      ∂villainGraphGibbs G β =
      (∫ θ : V → ℝ,
        ∏ e, villainWeight β (θ (G.src e) - θ (G.tgt e) + s e)
          ∂siteProduct circleMeasure V) / pairPartition circleMeasure d w := by
    rw [show villainGraphGibbs G β = pairGibbs circleMeasure d w from rfl,
      integral_pairGibbs circleMeasure_univ_ne_zero hw]
    congr 1
    apply integral_congr_ae
    filter_upwards with θ
    have hweight : pairWeight d w θ =
        ∏ e, villainWeight β (θ (G.src e) - θ (G.tgt e)) := by
      simp [pairWeight, d, w, phase_multigraphFrequency]
    rw [fullVillainShiftRatio, hweight]
    calc
      (∏ e, villainWeight β
          (θ (G.src e) - θ (G.tgt e) + s e) /
            villainWeight β (θ (G.src e) - θ (G.tgt e))) *
          ∏ e, villainWeight β (θ (G.src e) - θ (G.tgt e)) =
        ∏ e, (villainWeight β (θ (G.src e) - θ (G.tgt e) + s e) /
            villainWeight β (θ (G.src e) - θ (G.tgt e)) *
              villainWeight β (θ (G.src e) - θ (G.tgt e))) := by
            rw [Finset.prod_mul_distrib]
      _ = ∏ e, villainWeight β (θ (G.src e) - θ (G.tgt e) + s e) := by
        apply Finset.prod_congr rfl
        intro e he
        exact div_mul_cancel₀ _ (VillainWeight.villainWeight_pos hβ _).ne'
  let C : ℝ := ((2 * Real.pi * β) ^ (-(1 / 2 : ℝ))) ^ Fintype.card E
  let M : ℝ := (2 * Real.pi) ^ Fintype.card V
  let Z : ℝ := ∑' q : E → ℤ, neutralCurrentGaussianWeight G z β q
  let N : ℝ := ∑' q : E → ℤ,
    neutralCurrentGaussianWeight G z β q * Real.cos (∑ e, (q e : ℝ) * s e)
  have hN : ∫ θ : V → ℝ,
      ∏ e, villainWeight β (θ (G.src e) - θ (G.tgt e) + s e)
        ∂siteProduct circleMeasure V = C * M * N := by
    simpa [C, M, N] using villain_shifted_partition_full_real G z β hβ s
  have hZ : pairPartition circleMeasure d w = C * M * Z := by
    rw [hdenRaw]
    simpa [C, M, Z] using
      (villain_shifted_partition_full_real G z β hβ (fun _ => 0))
  have hposZ : 0 < Z := by
    simpa [Z] using neutralCurrentGaussianWeight_tsum_pos G z β hβ
  have hposCM : 0 < C * M := by
    positivity
  have hcalc : (∫ θ : V → ℝ, fullVillainShiftRatio G β s θ
      ∂villainGraphGibbs G β) = N / Z := by
    rw [hnumRaw, hN, hZ]
    exact mul_div_mul_left N Z hposCM.ne'
  rw [hcalc, integral_villainShiftRatio G z β hβ s]

private theorem rotatorFreeGraph_pairWeight_eq_villainModel
    (L : ℕ) (β : ℝ) (hβ : 0 < β)
    (θ : squareBoxZ L → ℝ) :
    pairWeight (bondFrequency (squareBoxZ L))
        ((villainModel β hβ).bondWeight (squareBoxZ L)) θ =
      pairWeight (multigraphFrequency (rotatorFreeGraph L))
        (fun _ => villainWeight β) (θ ∘ squareBoxEquiv L) := by
  classical
  let G := rotatorFreeGraph L
  let Λ := squareBoxZ L
  let d : RotatorInternalBond L → Frequency (RotatorSpinSite L) := multigraphFrequency G
  let w : RotatorInternalBond L → ℝ → ℝ := fun _ => villainWeight β
  let d' : (Λ × Λ) → Frequency Λ := bondFrequency Λ
  let w' : (Λ × Λ) → ℝ → ℝ := (villainModel β hβ).bondWeight Λ
  have hw : ∀ e, IsBondWeight (w e) := by
    intro e
    simpa [w] using isBondWeight_villain hβ
  have hw' : ∀ e, IsBondWeight (w' e) :=
    (villainModel β hβ).isBondWeight_bondWeight Λ
  have hlogs :
      (∑ e : RotatorInternalBond L,
        Real.log (villainWeight β
          (θ (squareBoxEquiv L (G.src e)) - θ (squareBoxEquiv L (G.tgt e))))) =
        ∑ c : Λ × Λ,
          if LatticeStep (c.1 : ℤ × ℤ) (c.2 : ℤ × ℤ) then
            Real.log (villainWeight β (θ c.1 - θ c.2)) else 0 := by
    let g : ℤ × ℤ → ℤ × ℤ → ℝ := fun y z =>
      Real.log (villainWeight β (latticeAngle θ y - latticeAngle θ z))
    simpa only [g, G, latticeAngle_siteToZ, latticeAngle_coe] using
      (sum_rotatorInternalBond_eq_sum_latticeStep L g)
  have hlogGraph :
      Real.log (pairWeight d w (θ ∘ squareBoxEquiv L)) =
        ∑ e : RotatorInternalBond L,
          Real.log (villainWeight β
            (θ (squareBoxEquiv L (G.src e)) - θ (squareBoxEquiv L (G.tgt e)))) := by
    rw [pairWeight, Real.log_prod]
    simp only [w, d, phase_multigraphFrequency, Function.comp_apply]
    · intro e he
      rw [phase_multigraphFrequency]
      exact (VillainWeight.villainWeight_pos hβ _).ne'
  have hlogLattice :
      Real.log (pairWeight d' w' θ) =
        ∑ c : Λ × Λ,
          if LatticeStep (c.1 : ℤ × ℤ) (c.2 : ℤ × ℤ) then
            Real.log (villainWeight β (θ c.1 - θ c.2)) else 0 := by
    rw [pairWeight, Real.log_prod]
    · apply Finset.sum_congr rfl
      intro c hc
      rw [phase_bondFrequency]
      dsimp [w', FreeModel.bondWeight, villainModel]
      split_ifs with hstep
      · rfl
      · simp
    · intro c hc
      rw [phase_bondFrequency]
      dsimp [w', FreeModel.bondWeight, villainModel]
      split_ifs with hstep
      · exact (VillainWeight.villainWeight_pos hβ _).ne'
      · norm_num
  have hlog : Real.log (pairWeight d w (θ ∘ squareBoxEquiv L)) =
      Real.log (pairWeight d' w' θ) := by
    rw [hlogGraph, hlogLattice]
    exact hlogs
  have hpos₁ : 0 < pairWeight d w (θ ∘ squareBoxEquiv L) := pairWeight_pos hw _
  have hpos₂ : 0 < pairWeight d' w' θ := pairWeight_pos hw' _
  calc
    pairWeight d' w' θ = Real.exp (Real.log (pairWeight d' w' θ)) :=
      (Real.exp_log hpos₂).symm
    _ = Real.exp (Real.log (pairWeight d w (θ ∘ squareBoxEquiv L))) :=
      congrArg Real.exp hlog.symm
    _ = pairWeight d w (θ ∘ squareBoxEquiv L) := Real.exp_log hpos₁

/-- The shifted-bond observable (1.32) on the full finite square, using its product-circle
Villain Gibbs measure. -/
def dirichletFullBoxVillainShiftRatio (R n : ℕ) (hn : n ≤ R)
    (β ξ : ℝ) (θ : squareBoxZ (sideLength R) → ℝ) : ℝ :=
  fullVillainShiftRatio (rotatorFreeGraph (sideLength R)) β
    (dirichletStringShift R n hn ξ) (θ ∘ squareBoxEquiv (sideLength R))

/-- The centered Dirichlet disorder expectation in the full free-boundary Villain Gibbs law on the
translated square `squareBoxZ (sideLength R)`. -/
def dirichletFullFreeVillainDisorderExpectation (R n : ℕ) (hn : n ≤ R)
    (β ξ : ℝ) (hβ : 0 < β) : ℝ :=
  ∫ θ, dirichletFullBoxVillainShiftRatio R n hn β ξ θ ∂
    (villainModel β hβ).gibbs (squareBoxZ (sideLength R))

/-- Gauge fixing identifies the full free-square Gibbs expectation with the root-pinned one used
by the dual finite-volume construction. -/
theorem dirichletFullFreeVillainDisorderExpectation_eq_rooted
    (R n : ℕ) (hn : n ≤ R) (β ξ : ℝ) (hβ : 0 < β) :
    dirichletFullFreeVillainDisorderExpectation R n hn β ξ hβ =
      dirichletFreeVillainDisorderExpectation R n hn β ξ hβ := by
  classical
  let L := sideLength R
  let G := rotatorFreeGraph L
  let Λ := squareBoxZ L
  let d : RotatorInternalBond L → Frequency (RotatorSpinSite L) := multigraphFrequency G
  let w : RotatorInternalBond L → ℝ → ℝ := fun _ => villainWeight β
  let d' : (Λ × Λ) → Frequency Λ := bondFrequency Λ
  let w' : (Λ × Λ) → ℝ → ℝ := (villainModel β hβ).bondWeight Λ
  have hw : ∀ e, IsBondWeight (w e) := by
    intro e
    simpa [w] using isBondWeight_villain hβ
  have hw' : ∀ e, IsBondWeight (w' e) :=
    (villainModel β hβ).isBondWeight_bondWeight Λ
  have hW (θ : Λ → ℝ) : pairWeight d' w' θ =
      pairWeight d w (θ ∘ squareBoxEquiv L) := by
    exact rotatorFreeGraph_pairWeight_eq_villainModel L β hβ θ
  let graphObs : (RotatorSpinSite L → ℝ) → ℝ := fun θ =>
    fullVillainShiftRatio G β (dirichletStringShift R n hn ξ) θ
  have hcont : Continuous graphObs := by
    have hweight : Continuous (villainWeight β) :=
      Villain.continuous_villainWeight β hβ
    unfold graphObs fullVillainShiftRatio
    apply continuous_finsetProd
    intro e he
    have hangle : Continuous (fun θ : RotatorSpinSite L → ℝ =>
        θ (G.src e) - θ (G.tgt e)) := by fun_prop
    exact (hweight.comp (hangle.add continuous_const)).div₀ (hweight.comp hangle)
      (fun θ => (VillainWeight.villainWeight_pos hβ _).ne')
  have htransfer := integral_comp_pairGibbs
    (ν := circleMeasure) (V := RotatorSpinSite L) (E := RotatorInternalBond L)
    (d := d) (w := w) circleMeasure_univ_ne_zero hw hw'
    (d' := d') (w' := w') (ι := squareBoxEquiv L) (squareBoxEquiv L).injective hW
    (f := graphObs) hcont.measurable
  calc
    dirichletFullFreeVillainDisorderExpectation R n hn β ξ hβ =
        ∫ θ : Λ → ℝ,
          graphObs (θ ∘ squareBoxEquiv L) ∂pairGibbs circleMeasure d' w' := by
      rfl
    _ = ∫ θ : RotatorSpinSite L → ℝ,
          graphObs θ ∂villainGraphGibbs G β := by
      rw [show villainGraphGibbs G β = pairGibbs circleMeasure d w from rfl]
      rw [← htransfer]
    _ = dirichletFreeVillainDisorderExpectation R n hn β ξ hβ := by
      exact fullVillainShiftRatio_integral_eq_rooted G (dirichletRoot R) β hβ
        (dirichletStringShift R n hn ξ)

/-- The finite D3 identity, now stated under the full free-boundary Villain Gibbs measure. -/
theorem dirichletFullFreeVillainDisorderExpectation_eq_cosineExpectation
    (R n : ℕ) (hR : 1 ≤ R) (hn : n ≤ R) (β ξ : ℝ) (hβ : 0 < β) :
    dirichletFullFreeVillainDisorderExpectation R n hn β ξ hβ =
      cosineExpectation R n hn β ξ := by
  rw [dirichletFullFreeVillainDisorderExpectation_eq_rooted]
  exact dirichletFreeVillainDisorderExpectation_eq_cosineExpectation R n hR hn β ξ hβ

end FroehlichSpencer.BKT.VillainDisorder.Dirichlet
end
