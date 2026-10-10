/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.SOS.Literal.LimitFejer

/-!
# Gaussian domination through the comb and `E_β` (the comb-inserted SOS construction)

On the real axis FS81's (C.1) factors as `I_β = L_β E_β` (`sosInterp_re_eq`), with
`L_β(t) = e^{−β^{2/3}(1+β^{2/3}t²)^{1/2}}` and `E_β = η̂` for a finite measure `η ≥ 0`
(`Literal/LimitFejer.lean`). Put `P_E(φ) = Π_e E_β(∇φ(e))` and let `C_A = Σ_{n∈ℤ^A} (n ⊕ ·)_* dy` be the
comb on `A` (`combMeasure`).

* `psi_le_psi_zero`: for precisions `p_e > 0`, `∫ e^{−Q_p(φ−b)} P_E(φ) dC_A ≤ ∫ e^{−Q_p(φ)} P_E dC_A`.
  Write `P_E(φ) = ∫ e^{2πi⟨ξ,∇φ⟩} η^{⊗E}(dξ)`, swap the integrals, and apply
  `norm_tsum_marginal_gaussChar_le` for every `ξ`.
* `lintegral_gauss_domination`: for a flow `θ` with divergence `f`,
  `∫ e^{⟨f,φ⟩} e^{−Q_p} P_E dC_A ≤ e^{Σ_e θ_e²/(4p_e)} ∫ e^{−Q_p} P_E dC_A`
  (completing the square and Thomson).
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.SOS.Literal

open MeasureTheory Complex Filter Topology
open scoped SchwartzMap Real NNReal ENNReal
open FroehlichSpencer.BKT.Generic.PinnedCharges (SquareZeroBond Site)
open FroehlichSpencer.BKT.SOS.Roughening

variable {L : ℕ}

/-! ## The factors `L_β`, `E_β` -/

/-- `L_β(t) = e^{−β^{2/3}(1+β^{2/3}t²)^{1/2}}`. -/
def Lw (β t : ℝ) : ℝ := Real.exp (-(β ^ (2 / 3 : ℝ)) * Real.sqrt (1 + β ^ (2 / 3 : ℝ) * t ^ 2))

/-- `E_β(t) = e^{h(t)}`, `h(t) = Σ_n c_{|n|} sinc²(t − n)`. -/
def Ew (β t : ℝ) : ℝ := Real.exp (∑' n : ℤ, fsC β n.natAbs * sincSqR (t - n))

theorem fsC_natAbs (β : ℝ) (n : ℤ) : fsC β n.natAbs = -Interp.sosDefect β n := by
  unfold fsC
  rcases Int.natAbs_eq n with h | h
  · rw [← h]
  · rw [h, Int.natAbs_neg, Int.natAbs_natCast, Interp.sosDefect_neg]

theorem Ew_eq (β t : ℝ) :
    Ew β t = Real.exp (-∑' n : ℤ, Interp.sosDefect β n * Real.sinc (π * (t - n)) ^ 2) := by
  unfold Ew sincSqR
  rw [← tsum_neg]
  congr 1
  refine tsum_congr fun n => ?_
  rw [fsC_natAbs]
  ring

theorem sosInterp_re_eq {β : ℝ} (hβ : 0 ≤ β) (t : ℝ) :
    (Interp.sosInterp β t).re = Lw β t * Ew β t := by
  rw [Interp.sosInterp_ofReal hβ, Complex.ofReal_re, Ew_eq, Lw]

theorem Lw_pos (β t : ℝ) : 0 < Lw β t := Real.exp_pos _

theorem Ew_pos (β t : ℝ) : 0 < Ew β t := Real.exp_pos _

theorem continuous_Lw (β : ℝ) : Continuous (Lw β) := by
  unfold Lw; fun_prop

theorem continuous_Ew {β : ℝ} (hβ : 0 ≤ β) : Continuous (Ew β) := by
  have h : Ew β = fun t : ℝ => (Interp.sosInterp β t).re / Lw β t := by
    funext t
    rw [sosInterp_re_eq hβ, mul_div_cancel_left₀ _ (Lw_pos β t).ne']
  rw [h]
  exact (continuous_sosInterp_re hβ).div (continuous_Lw β) fun t => (Lw_pos β t).ne'

/-- `P_E(φ) = Π_e E_β(∇φ(e))`. -/
def PE (L : ℕ) (β : ℝ) (φ : Site L → ℝ) : ℝ := ∏ e, Ew β (pinnedGrad L φ e)

theorem PE_pos (β : ℝ) (φ : Site L → ℝ) : 0 < PE L β φ :=
  Finset.prod_pos fun _ _ => Ew_pos β _

theorem continuous_PE {β : ℝ} (hβ : 0 ≤ β) : Continuous (PE L β) := by
  unfold PE
  have hg : Continuous (pinnedGrad L) := (pinnedGrad L).continuous_of_finiteDimensional
  exact continuous_finsetProd _ fun e _ => (continuous_Ew hβ).comp ((continuous_apply e).comp hg)

theorem boxWeight_eq {β : ℝ} (hβ : 0 ≤ β) (φ : Site L → ℝ) :
    boxWeight L β φ = (∏ e, Lw β (pinnedGrad L φ e)) * PE L β φ := by
  unfold boxWeight PE
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun e _ => sosInterp_re_eq hβ _

/-! ## `E_β = η̂` -/

/-- The measure `η` with `E_β = η̂`. -/
def etaE (β : ℝ) : Measure ℝ := etaMeasure (fsC β)

theorem isFiniteMeasure_etaE {β : ℝ} (hβ : 0 < β) : IsFiniteMeasure (etaE β) :=
  isFiniteMeasure_etaMeasure (fsC_convex hβ) (fsC_succ_le hβ) (tendsto_fsC hβ)

theorem Ew_eq_integral {β : ℝ} (hβ : 0 < β) (t : ℝ) :
    ((Ew β t : ℝ) : ℂ) = ∫ ξ, cexp (2 * π * I * ξ * t) ∂etaE β :=
  (integral_cexp_etaMeasure (fsC_convex hβ) (fsC_succ_le hβ) (tendsto_fsC hβ) t).symm

/-- **`P_E` as a superposition of characters**. -/
theorem PE_eq_integral {β : ℝ} (hβ : 0 < β) (φ : Site L → ℝ) :
    ((PE L β φ : ℝ) : ℂ) = ∫ ξ : SquareZeroBond L → ℝ,
      cexp (2 * π * I * ∑ e, ((ξ e : ℂ) * (pinnedGrad L φ e : ℂ))) ∂Measure.pi fun _ => etaE β := by
  have := isFiniteMeasure_etaE hβ
  unfold PE
  rw [Complex.ofReal_prod]
  simp_rw [Ew_eq_integral hβ]
  rw [← integral_fintype_prod_eq_prod (𝕜 := ℂ)
    (fun e (ξ : ℝ) => cexp (2 * π * I * ξ * (pinnedGrad L φ e : ℂ)))]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  beta_reduce
  rw [← Complex.exp_sum, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun e _ => by ring

theorem PE_le {β : ℝ} (hβ : 0 < β) (φ : Site L → ℝ) :
    PE L β φ ≤ ((Measure.pi fun _ : SquareZeroBond L => etaE β).real Set.univ) := by
  have := isFiniteMeasure_etaE hβ
  have h := PE_eq_integral hβ φ
  have hn := norm_integral_le_of_norm_le_const (μ := Measure.pi fun _ : SquareZeroBond L => etaE β)
    (f := fun ξ : SquareZeroBond L → ℝ =>
      cexp (2 * π * I * ∑ e, ((ξ e : ℂ) * (pinnedGrad L φ e : ℂ)))) (C := 1)
    (Eventually.of_forall fun ξ => by
      rw [show 2 * (π : ℂ) * I * ∑ e, ((ξ e : ℂ) * (pinnedGrad L φ e : ℂ)) =
        ((2 * π * ∑ e, ξ e * pinnedGrad L φ e : ℝ) : ℂ) * I by push_cast; ring,
        Complex.norm_exp_ofReal_mul_I])
  rw [← h, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (PE_pos β φ), one_mul] at hn
  exact hn

/-! ## The comb measure -/

/-- The comb on `A`: `C_A = Σ_{n ∈ ℤ^A} (n ⊕ ·)_* dy`. -/
def combMeasure (A : Finset (Site L)) : Measure (Site L → ℝ) :=
  Measure.sum fun n : {x // x ∈ A} → ℤ =>
    (volume : Measure ({x // x ∉ A} → ℝ)).map (heightField A n)

theorem lintegral_combMeasure (A : Finset (Site L)) {F : (Site L → ℝ) → ℝ≥0∞}
    (hF : Measurable F) :
    ∫⁻ φ, F φ ∂combMeasure A = ∑' n, ∫⁻ y, F (heightField A n y) := by
  unfold combMeasure
  rw [lintegral_sum_measure]
  exact tsum_congr fun n => lintegral_map hF (measurable_heightField A n)

theorem integral_combMeasure (A : Finset (Site L)) {F : (Site L → ℝ) → ℂ} (hFc : Continuous F)
    (hF : Integrable F (combMeasure A)) :
    ∫ φ, F φ ∂combMeasure A = ∑' n, ∫ y, F (heightField A n y) := by
  unfold combMeasure at hF ⊢
  rw [integral_sum_measure hF]
  exact tsum_congr fun n =>
    integral_map (measurable_heightField A n).aemeasurable hFc.aestronglyMeasurable

/-! ## `Ψ(b) ≤ Ψ(0)` -/

theorem gaussChar_norm (p : SquareZeroBond L → ℝ) (b : Site L → ℝ) (ξ : SquareZeroBond L → ℝ)
    (φ : Site L → ℝ) : ‖gaussChar p b ξ φ‖ = Real.exp (-gaussQ p (φ - b)) := by
  unfold gaussChar
  rw [norm_mul, show 2 * (π : ℂ) * I * ∑ e, ((ξ e : ℂ) * (pinnedGrad L φ e : ℂ)) =
      ((2 * π * ∑ e, ξ e * pinnedGrad L φ e : ℝ) : ℂ) * I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]

theorem continuous_gaussChar (p : SquareZeroBond L → ℝ) (b : Site L → ℝ) :
    Continuous fun q : (Site L → ℝ) × (SquareZeroBond L → ℝ) => gaussChar p b q.2 q.1 := by
  unfold gaussChar
  have hg : Continuous (pinnedGrad L) := (pinnedGrad L).continuous_of_finiteDimensional
  have hQ : Continuous fun q : (Site L → ℝ) × (SquareZeroBond L → ℝ) => gaussQ p (q.1 - b) :=
    (continuous_gaussQ p).comp (continuous_fst.sub continuous_const)
  have hs : Continuous fun q : (Site L → ℝ) × (SquareZeroBond L → ℝ) =>
      ∑ e, ((q.2 e : ℂ) * (pinnedGrad L q.1 e : ℂ)) :=
    continuous_finsetSum _ fun e _ =>
      (Complex.continuous_ofReal.comp ((continuous_apply e).comp continuous_snd)).mul
        (Complex.continuous_ofReal.comp ((continuous_apply e).comp (hg.comp continuous_fst)))
  exact (Complex.continuous_ofReal.comp (Real.continuous_exp.comp hQ.neg)).mul
    (Complex.continuous_exp.comp (continuous_const.mul hs))

theorem continuous_gaussChar_left (p : SquareZeroBond L → ℝ) (b : Site L → ℝ)
    (ξ : SquareZeroBond L → ℝ) : Continuous (gaussChar p b ξ) := by
  unfold gaussChar
  have hg : Continuous (pinnedGrad L) := (pinnedGrad L).continuous_of_finiteDimensional
  have hQ : Continuous fun φ : Site L → ℝ => gaussQ p (φ - b) :=
    (continuous_gaussQ p).comp (continuous_id.sub continuous_const)
  have hs : Continuous fun φ : Site L → ℝ => ∑ e, ((ξ e : ℂ) * (pinnedGrad L φ e : ℂ)) :=
    continuous_finsetSum _ fun e _ =>
      continuous_const.mul (Complex.continuous_ofReal.comp ((continuous_apply e).comp hg))
  exact (Complex.continuous_ofReal.comp (Real.continuous_exp.comp hQ.neg)).mul
    (Complex.continuous_exp.comp (continuous_const.mul hs))

/-- The comb integral of a shifted Gaussian is finite. -/
theorem integrable_gauss_combMeasure (hL : 1 < L) {p : SquareZeroBond L → ℝ} (hp : ∀ e, 0 < p e)
    (A : Finset (Site L)) (b : Site L → ℝ) :
    Integrable (fun φ => Real.exp (-gaussQ p (φ - b))) (combMeasure A) ∧
      ∑' n, ∫⁻ y, ENNReal.ofReal (Real.exp (-gaussQ p (heightField A n y - b))) =
        ENNReal.ofReal (∑' n, ∫ y, Real.exp (-gaussQ p (heightField A n y - b))) ∧
      Summable fun n : {x // x ∈ A} → ℤ => ∫ y, Real.exp (-gaussQ p (heightField A n y - b)) := by
  obtain ⟨F, hF⟩ := exists_gaussChar_schwartz hL hp b 0
  obtain ⟨-, -, hsum⟩ := tsum_fourier_extZero_eq_tsum_marginal (· ∈ A) F
  have hFv : ∀ φ, F φ = ((Real.exp (-gaussQ p (φ - b)) : ℝ) : ℂ) := fun φ => by
    rw [hF]; simp [gaussChar]
  have hslice : ∀ n : {x // x ∈ A} → ℤ,
      Integrable fun y => Real.exp (-gaussQ p (heightField A n y - b)) := fun n => by
    have h := (integrable_slice (· ∈ A) F (fun i => (n i : ℝ))).re
    refine h.congr (Eventually.of_forall fun y => ?_)
    simp only [hFv]
    rfl
  have hmarg : ∀ n : {x // x ∈ A} → ℤ, marginalPi (· ∈ A) F (fun i => (n i : ℝ)) =
      ((∫ y, Real.exp (-gaussQ p (heightField A n y - b)) : ℝ) : ℂ) := fun n => by
    unfold marginalPi
    rw [← integral_complex_ofReal]
    exact integral_congr_ae (Eventually.of_forall fun y => hFv _)
  have hsumR : Summable fun n : {x // x ∈ A} → ℤ =>
      ∫ y, Real.exp (-gaussQ p (heightField A n y - b)) := by
    simp_rw [hmarg] at hsum
    exact Complex.summable_ofReal.mp hsum
  have hlin : ∀ n : {x // x ∈ A} → ℤ,
      ∫⁻ y, ENNReal.ofReal (Real.exp (-gaussQ p (heightField A n y - b))) =
        ENNReal.ofReal (∫ y, Real.exp (-gaussQ p (heightField A n y - b))) := fun n =>
    (ofReal_integral_eq_lintegral_ofReal (hslice n)
      (Eventually.of_forall fun y => (Real.exp_pos _).le)).symm
  have htot : ∑' n, ∫⁻ y, ENNReal.ofReal (Real.exp (-gaussQ p (heightField A n y - b))) =
      ENNReal.ofReal (∑' n, ∫ y, Real.exp (-gaussQ p (heightField A n y - b))) := by
    simp_rw [hlin]
    exact (ENNReal.ofReal_tsum_of_nonneg (fun n => integral_nonneg fun y => (Real.exp_pos _).le)
      hsumR).symm
  refine ⟨⟨(Real.continuous_exp.comp ((continuous_gaussQ p).comp
    (continuous_id.sub continuous_const)).neg).aestronglyMeasurable, ?_⟩, htot, hsumR⟩
  unfold HasFiniteIntegral
  have hmeas : Measurable fun φ : Site L → ℝ => ‖Real.exp (-gaussQ p (φ - b))‖ₑ :=
    (Real.continuous_exp.comp ((continuous_gaussQ p).comp
      (continuous_id.sub continuous_const)).neg).measurable.enorm
  rw [lintegral_combMeasure A hmeas]
  have henorm : ∀ φ : Site L → ℝ, ‖Real.exp (-gaussQ p (φ - b))‖ₑ =
      ENNReal.ofReal (Real.exp (-gaussQ p (φ - b))) := fun φ => by
    rw [Real.enorm_eq_ofReal (Real.exp_pos _).le]
  simp_rw [henorm, htot]
  exact ENNReal.ofReal_lt_top

instance sFinite_combMeasure (A : Finset (Site L)) : SFinite (combMeasure A) := by
  unfold combMeasure; infer_instance

theorem integrable_gaussChar_prod (hL : 1 < L) {β : ℝ} (hβ : 0 < β) {p : SquareZeroBond L → ℝ}
    (hp : ∀ e, 0 < p e) (A : Finset (Site L)) (b : Site L → ℝ) :
    Integrable (fun q : (Site L → ℝ) × (SquareZeroBond L → ℝ) => gaussChar p b q.2 q.1)
      ((combMeasure A).prod (Measure.pi fun _ => etaE β)) := by
  have hη := isFiniteMeasure_etaE hβ
  have hG := (integrable_gauss_combMeasure hL hp A b).1.comp_fst
    (Measure.pi fun _ : SquareZeroBond L => etaE β)
  refine hG.mono' (continuous_gaussChar p b).aestronglyMeasurable
    (Eventually.of_forall fun q => ?_)
  rw [gaussChar_norm]

theorem integral_gaussChar_eta {β : ℝ} (hβ : 0 < β) (p : SquareZeroBond L → ℝ)
    (b φ : Site L → ℝ) :
    ∫ ξ, gaussChar p b ξ φ ∂(Measure.pi fun _ => etaE β) =
      ((Real.exp (-gaussQ p (φ - b)) * PE L β φ : ℝ) : ℂ) := by
  unfold gaussChar
  rw [integral_const_mul, ← PE_eq_integral hβ φ, Complex.ofReal_mul]

theorem psi_eq_integral (hL : 1 < L) {β : ℝ} (hβ : 0 < β) {p : SquareZeroBond L → ℝ}
    (hp : ∀ e, 0 < p e) (A : Finset (Site L)) (b : Site L → ℝ) :
    (((∫ φ, Real.exp (-gaussQ p (φ - b)) * PE L β φ ∂combMeasure A) : ℝ) : ℂ) =
      ∫ ξ, (∫ φ, gaussChar p b ξ φ ∂combMeasure A) ∂(Measure.pi fun _ => etaE β) := by
  have := isFiniteMeasure_etaE hβ
  rw [← integral_complex_ofReal]
  simp_rw [← integral_gaussChar_eta hβ p b]
  exact integral_integral_swap (f := fun φ ξ => gaussChar p b ξ φ)
    (integrable_gaussChar_prod hL hβ hp A b)

theorem norm_integral_gaussChar_comb_le (hL : 1 < L) {p : SquareZeroBond L → ℝ}
    (hp : ∀ e, 0 < p e) (A : Finset (Site L)) (b : Site L → ℝ) (ξ : SquareZeroBond L → ℝ) :
    ‖∫ φ, gaussChar p b ξ φ ∂combMeasure A‖ ≤ (∫ φ, gaussChar p 0 ξ φ ∂combMeasure A).re := by
  obtain ⟨F, hF⟩ := exists_gaussChar_schwartz hL hp b ξ
  obtain ⟨F₀, hF₀⟩ := exists_gaussChar_schwartz hL hp 0 ξ
  have hcont : ∀ b' : Site L → ℝ, Continuous (gaussChar p b' ξ) := fun b' =>
    continuous_gaussChar_left p b' ξ
  have hint : ∀ b' : Site L → ℝ, Integrable (gaussChar p b' ξ) (combMeasure A) := fun b' => by
    refine (integrable_gauss_combMeasure hL hp A b').1.mono' (hcont b').aestronglyMeasurable
      (Eventually.of_forall fun φ => ?_)
    rw [gaussChar_norm]
  rw [integral_combMeasure A (hcont b) (hint b), integral_combMeasure A (hcont 0) (hint 0)]
  have h := norm_tsum_marginal_gaussChar_le hL hp A b ξ hF hF₀
  simp only [marginalPi, hF, hF₀] at h
  exact h

/-- **`Ψ(b) ≤ Ψ(0)`**: the comb integral of `e^{−Q_p(φ−b)} P_E(φ)` is largest at `b = 0`. -/
theorem psi_le_psi_zero (hL : 1 < L) {β : ℝ} (hβ : 0 < β) {p : SquareZeroBond L → ℝ}
    (hp : ∀ e, 0 < p e) (A : Finset (Site L)) (b : Site L → ℝ) :
    ∫ φ, Real.exp (-gaussQ p (φ - b)) * PE L β φ ∂combMeasure A ≤
      ∫ φ, Real.exp (-gaussQ p φ) * PE L β φ ∂combMeasure A := by
  have := isFiniteMeasure_etaE hβ
  have hiR := (integrable_gaussChar_prod hL hβ hp A b).integral_prod_right
  have hi0 := (integrable_gaussChar_prod hL hβ hp A 0).integral_prod_right
  have hpsi0 := psi_eq_integral hL hβ hp A 0
  simp only [sub_zero] at hpsi0
  have hnonneg : 0 ≤ ∫ φ, Real.exp (-gaussQ p (φ - b)) * PE L β φ ∂combMeasure A :=
    integral_nonneg fun φ => mul_nonneg (Real.exp_pos _).le (PE_pos β φ).le
  calc ∫ φ, Real.exp (-gaussQ p (φ - b)) * PE L β φ ∂combMeasure A
      = ‖(((∫ φ, Real.exp (-gaussQ p (φ - b)) * PE L β φ ∂combMeasure A) : ℝ) : ℂ)‖ := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg]
    _ = ‖∫ ξ, (∫ φ, gaussChar p b ξ φ ∂combMeasure A) ∂(Measure.pi fun _ => etaE β)‖ := by
        rw [psi_eq_integral hL hβ hp A b]
    _ ≤ ∫ ξ, ‖∫ φ, gaussChar p b ξ φ ∂combMeasure A‖ ∂(Measure.pi fun _ => etaE β) :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ ξ, (∫ φ, gaussChar p 0 ξ φ ∂combMeasure A).re ∂(Measure.pi fun _ => etaE β) :=
        integral_mono hiR.norm hi0.re (norm_integral_gaussChar_comb_le hL hp A b)
    _ = (∫ ξ, (∫ φ, gaussChar p 0 ξ φ ∂combMeasure A) ∂(Measure.pi fun _ => etaE β)).re :=
        integral_re hi0
    _ = ∫ φ, Real.exp (-gaussQ p φ) * PE L β φ ∂combMeasure A := by
        rw [← hpsi0, Complex.ofReal_re]

theorem integrable_gauss_PE_comb (hL : 1 < L) {β : ℝ} (hβ : 0 < β) {p : SquareZeroBond L → ℝ}
    (hp : ∀ e, 0 < p e) (A : Finset (Site L)) (b : Site L → ℝ) :
    Integrable (fun φ => Real.exp (-gaussQ p (φ - b)) * PE L β φ) (combMeasure A) := by
  have hc : Continuous fun φ : Site L → ℝ => Real.exp (-gaussQ p (φ - b)) * PE L β φ :=
    (Real.continuous_exp.comp ((continuous_gaussQ p).comp
      (continuous_id.sub continuous_const)).neg).mul (continuous_PE hβ.le)
  refine ((integrable_gauss_combMeasure hL hp A b).1.mul_const
    ((Measure.pi fun _ : SquareZeroBond L => etaE β).real Set.univ)).mono'
    hc.aestronglyMeasurable (Eventually.of_forall fun φ => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (PE_pos β φ).le)]
  exact mul_le_mul_of_nonneg_left (PE_le hβ φ) (Real.exp_pos _).le

theorem lintegral_gauss_PE_eq (hL : 1 < L) {β : ℝ} (hβ : 0 < β) {p : SquareZeroBond L → ℝ}
    (hp : ∀ e, 0 < p e) (A : Finset (Site L)) (b : Site L → ℝ) :
    ∫⁻ φ, ENNReal.ofReal (Real.exp (-gaussQ p (φ - b)) * PE L β φ) ∂combMeasure A =
      ENNReal.ofReal (∫ φ, Real.exp (-gaussQ p (φ - b)) * PE L β φ ∂combMeasure A) :=
  (ofReal_integral_eq_lintegral_ofReal (integrable_gauss_PE_comb hL hβ hp A b)
    (Eventually.of_forall fun φ => mul_nonneg (Real.exp_pos _).le (PE_pos β φ).le)).symm

/-- **Gaussian domination at fixed precisions**: for a flow `θ` with divergence `f`,
`∫ e^{⟨f,φ⟩} e^{−Q_p(φ)} P_E(φ) dC_A ≤ e^{Σ_e θ_e²/(4p_e)} ∫ e^{−Q_p(φ)} P_E(φ) dC_A`. -/
theorem lintegral_gauss_domination (hL : 1 < L) {β : ℝ} (hβ : 0 < β)
    {p : SquareZeroBond L → ℝ} (hp : ∀ e, 0 < p e) (A : Finset (Site L)) {f : Site L → ℝ}
    {θ : SquareZeroBond L → ℝ} (hθ : ∀ ψ, ∑ e, θ e * pinnedGrad L ψ e = ∑ v, f v * ψ v) :
    ∫⁻ φ, ENNReal.ofReal (Real.exp (∑ v, f v * φ v) * (Real.exp (-gaussQ p φ) * PE L β φ))
        ∂combMeasure A ≤
      ENNReal.ofReal (Real.exp (∑ e, θ e ^ 2 / (4 * p e))) *
        ∫⁻ φ, ENNReal.ofReal (Real.exp (-gaussQ p φ) * PE L β φ) ∂combMeasure A := by
  obtain ⟨b, hb⟩ := exists_gaussB_eq hL hp f
  have hpt : ∀ φ, Real.exp (∑ v, f v * φ v) * (Real.exp (-gaussQ p φ) * PE L β φ) =
      Real.exp (gaussQ p b) * (Real.exp (-gaussQ p (φ - b)) * PE L β φ) := fun φ => by
    rw [← mul_assoc, ← mul_assoc, ← Real.exp_add, ← Real.exp_add, ← sub_eq_add_neg,
      ← sub_eq_add_neg, sum_mul_sub_gaussQ hb]
  have hsplit : ∀ φ, ENNReal.ofReal (Real.exp (gaussQ p b) *
      (Real.exp (-gaussQ p (φ - b)) * PE L β φ)) = ENNReal.ofReal (Real.exp (gaussQ p b)) *
        ENNReal.ofReal (Real.exp (-gaussQ p (φ - b)) * PE L β φ) := fun φ =>
    ENNReal.ofReal_mul (Real.exp_pos _).le
  simp_rw [hpt, hsplit]
  have hmeas : Measurable fun φ : Site L → ℝ =>
      ENNReal.ofReal (Real.exp (-gaussQ p (φ - b)) * PE L β φ) :=
    ENNReal.measurable_ofReal.comp ((Real.continuous_exp.comp ((continuous_gaussQ p).comp
      (continuous_id.sub continuous_const)).neg).mul (continuous_PE hβ.le)).measurable
  rw [lintegral_const_mul _ hmeas]
  have h0 := lintegral_gauss_PE_eq hL hβ hp A 0
  simp only [sub_zero] at h0
  refine mul_le_mul' (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr
    (gaussQ_le_of_flow hp hθ hb))) ?_
  rw [lintegral_gauss_PE_eq hL hβ hp A b, h0]
  exact ENNReal.ofReal_le_ofReal (psi_le_psi_zero hL hβ hp A b)

end FroehlichSpencer.BKT.SOS.Literal

end
