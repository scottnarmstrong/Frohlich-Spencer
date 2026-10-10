/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.SOS.Literal.LimitLevy

/-!
# The joint measure on fields and bond precisions (the comb-inserted SOS construction)

Each bond weight is `I_β(t) = L_β(t) E_β(t)` and `L_β(t) = ∫₀^∞ w(x) e^{−x²t²} dx`
(`lintegral_mixW_zero`). So the literal state is the field marginal of the joint measure
`w(x) e^{−Q_{x²}(φ)} P_E(φ) dx dC_A(φ)` (`lintegral_boxWeight_eq_mix`). Its law of the precisions
`x` is the probability measure `precLaw` (`isProbabilityMeasure_precLaw`).

* `lintegral_exp_flow_le`: a flow `θ` supported on `P` with `|θ_e| ≤ c` has
  `⟨e^{Σ_e θ_e∇φ(e)}⟩ ≤ M(c²/2)`, `M = mgfExt precLaw R_P`, `R_P(x) = Σ_{e∈P} 1/(2x_e²)`
  (Gaussian domination at fixed precisions, `lintegral_gauss_domination`).
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.SOS.Literal

open MeasureTheory Set Filter Topology
open scoped Real ENNReal
open FroehlichSpencer.BKT.Generic.PinnedCharges (SquareZeroBond Site)
open FroehlichSpencer.BKT.SOS.Roughening

variable {L : ℕ}

/-! ## Products over bonds -/

theorem lintegral_pi_ofReal_prod {ι : Type*} [Fintype ι] (μ : Measure ℝ) [SigmaFinite μ]
    (F : ι → ℝ → ℝ) (hF0 : ∀ i x, 0 ≤ F i x) (hFm : ∀ i, Measurable (F i))
    (hfin : ∀ i, ∫⁻ x, ENNReal.ofReal (F i x) ∂μ ≠ ⊤) :
    ∫⁻ x, ENNReal.ofReal (∏ i, F i (x i)) ∂Measure.pi (fun _ => μ) =
      ∏ i, ∫⁻ x, ENNReal.ofReal (F i x) ∂μ := by
  classical
  have hint : ∀ i, Integrable (F i) μ := fun i => by
    refine ⟨(hFm i).aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    simp_rw [Real.enorm_eq_ofReal (hF0 i _)]
    exact lt_top_iff_ne_top.mpr (hfin i)
  have hprod := Integrable.fintype_prod (μ := fun _ => μ) hint
  rw [← ofReal_integral_eq_lintegral_ofReal hprod
    (Eventually.of_forall fun x => Finset.prod_nonneg fun i _ => hF0 i _),
    integral_fintype_prod_eq_prod (𝕜 := ℝ) F, ENNReal.ofReal_prod_of_nonneg
      fun i _ => integral_nonneg (hF0 i)]
  exact Finset.prod_congr rfl fun i _ =>
    ofReal_integral_eq_lintegral_ofReal (hint i) (Eventually.of_forall (hF0 i))

/-! ## The joint density -/

/-- The precision measure `dx` on `(0, ∞)^bonds`. -/
def precMeasure (L : ℕ) : Measure (SquareZeroBond L → ℝ) :=
  Measure.pi fun _ => (volume : Measure ℝ).restrict (Ioi 0)

/-- The mixing weight `Π_e w(x_e)`. -/
def mixWeight (β : ℝ) (x : SquareZeroBond L → ℝ) : ℝ := ∏ e, mixW β (x e)

/-- The Gaussian `e^{−Σ_e x_e² ∇φ(e)²}`. -/
def gaussG (x : SquareZeroBond L → ℝ) (φ : Site L → ℝ) : ℝ :=
  Real.exp (-gaussQ (fun e => x e ^ 2) φ)

/-- `R_P(x) = Σ_{e∈P} 1/(2x_e²)`. -/
def resP (P : Finset (SquareZeroBond L)) (x : SquareZeroBond L → ℝ) : ℝ :=
  ∑ e ∈ P, 1 / (2 * x e ^ 2)

theorem resP_nonneg (P : Finset (SquareZeroBond L)) (x : SquareZeroBond L → ℝ) :
    0 ≤ resP P x := Finset.sum_nonneg fun e _ => by positivity

theorem measurable_mixW (β : ℝ) : Measurable (mixW β) := by
  unfold mixW; fun_prop

theorem measurable_mixWeight (β : ℝ) : Measurable (mixWeight (L := L) β) := by
  unfold mixWeight
  exact Finset.measurable_prod _ fun e _ => (measurable_mixW β).comp (measurable_pi_apply e)

theorem measurable_resP (P : Finset (SquareZeroBond L)) : Measurable (resP P) := by
  unfold resP
  exact Finset.measurable_sum _ fun e _ => by fun_prop

theorem continuous_gaussG_uncurry :
    Continuous fun q : (SquareZeroBond L → ℝ) × (Site L → ℝ) => gaussG q.1 q.2 := by
  unfold gaussG gaussQ
  have hg : Continuous (pinnedGrad L) := (pinnedGrad L).continuous_of_finiteDimensional
  refine Real.continuous_exp.comp (continuous_neg.comp (continuous_finsetSum _ fun e _ => ?_))
  exact (((continuous_apply e).comp continuous_fst).pow 2).mul
    (((continuous_apply e).comp (hg.comp continuous_snd)).pow 2)

theorem mixWeight_nonneg {β : ℝ} (hβ : 0 ≤ β) (x : SquareZeroBond L → ℝ) :
    0 ≤ mixWeight β x := Finset.prod_nonneg fun _ _ => mixW_nonneg hβ _

theorem gaussG_pos (x : SquareZeroBond L → ℝ) (φ : Site L → ℝ) : 0 < gaussG x φ :=
  Real.exp_pos _

theorem gaussG_eq_prod (x : SquareZeroBond L → ℝ) (φ : Site L → ℝ) :
    gaussG x φ = ∏ e, Real.exp (-(x e ^ 2 * pinnedGrad L φ e ^ 2)) := by
  unfold gaussG gaussQ
  rw [← Real.exp_sum, ← Finset.sum_neg_distrib]

/-- **The tilted mixture over all bonds**: `∫ Π_e w(x_e) e^{λ_e/(2x_e²)} e^{−x_e²t_e²} dx`. -/
theorem lintegral_mix_gauss {β : ℝ} (hβ : 0 < β) (lam : SquareZeroBond L → ℝ)
    (hlam : ∀ e, 2 * lam e < β ^ 2) (φ : Site L → ℝ) :
    ∫⁻ x, ENNReal.ofReal (mixWeight β x * Real.exp (∑ e, lam e / (2 * x e ^ 2)) * gaussG x φ)
        ∂precMeasure L =
      ∏ e, ENNReal.ofReal (β / Real.sqrt (β ^ 2 - 2 * lam e) *
        Real.exp (-(Real.sqrt (β ^ 2 - 2 * lam e) *
          Real.sqrt (mixQ0 β + pinnedGrad L φ e ^ 2)))) := by
  have hpt : ∀ x : SquareZeroBond L → ℝ,
      mixWeight β x * Real.exp (∑ e, lam e / (2 * x e ^ 2)) * gaussG x φ =
        ∏ e, (mixW β (x e) * Real.exp (lam e / (2 * x e ^ 2)) *
          Real.exp (-(x e ^ 2 * pinnedGrad L φ e ^ 2))) := fun x => by
    rw [mixWeight, gaussG_eq_prod, Real.exp_sum, ← Finset.prod_mul_distrib,
      ← Finset.prod_mul_distrib]
  simp_rw [hpt]
  unfold precMeasure
  rw [lintegral_pi_ofReal_prod _ (fun e x => mixW β x * Real.exp (lam e / (2 * x ^ 2)) *
      Real.exp (-(x ^ 2 * pinnedGrad L φ e ^ 2)))
    (fun e x => mul_nonneg (mul_nonneg (mixW_nonneg hβ.le x) (Real.exp_pos _).le)
      (Real.exp_pos _).le)
    (fun e => ((measurable_mixW β).mul (by fun_prop)).mul (by fun_prop))
    (fun e => by rw [lintegral_mixW hβ (hlam e)]; exact ENNReal.ofReal_ne_top)]
  exact Finset.prod_congr rfl fun e _ => lintegral_mixW hβ (hlam e) _

/-- The untilted mixture: `∫ Π_e w(x_e) e^{−Q_{x²}(φ)} dx = Π_e L_β(∇φ(e))`. -/
theorem lintegral_mix_gauss_zero {β : ℝ} (hβ : 0 < β) (φ : Site L → ℝ) :
    ∫⁻ x, ENNReal.ofReal (mixWeight β x * gaussG x φ) ∂precMeasure L =
      ENNReal.ofReal (∏ e, Lw β (pinnedGrad L φ e)) := by
  have h := lintegral_mix_gauss hβ (fun _ => 0) (fun e => by rw [mul_zero]; positivity) φ
  simp only [zero_div, Finset.sum_const_zero, Real.exp_zero, mul_one, mul_zero, sub_zero,
    Real.sqrt_sq hβ.le, div_self hβ.ne', one_mul] at h
  rw [h, ENNReal.ofReal_prod_of_nonneg fun e _ => (Lw_pos β _).le]
  exact Finset.prod_congr rfl fun e _ => by rw [Lw_eq hβ]

/-! ## The literal state as a mixture -/

instance sigmaFinite_precMeasure : SigmaFinite (precMeasure L) := by
  unfold precMeasure; infer_instance

theorem literalPartition_eq_comb {β : ℝ} (hβ : 0 ≤ β) (A : Finset (Site L)) :
    literalPartition L β A = ∫⁻ φ, ENNReal.ofReal (boxWeight L β φ) ∂combMeasure A := by
  rw [lintegral_combMeasure A (F := fun φ => ENNReal.ofReal (boxWeight L β φ))
    (ENNReal.measurable_ofReal.comp (continuous_boxWeight hβ).measurable)]
  unfold literalPartition literalFiber
  refine tsum_congr fun n => ?_
  rw [Measure.map_apply (measurable_heightField A n) MeasurableSet.univ, Set.preimage_univ,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]

theorem measurable_boxWeight_mix {β : ℝ} (hβ : 0 ≤ β) {F : (Site L → ℝ) → ℝ≥0∞}
    (hF : Measurable F) :
    Measurable fun q : (Site L → ℝ) × (SquareZeroBond L → ℝ) =>
      ENNReal.ofReal (mixWeight β q.2) *
        (ENNReal.ofReal (gaussG q.2 q.1 * PE L β q.1) * F q.1) := by
  have hG : Measurable fun q : (Site L → ℝ) × (SquareZeroBond L → ℝ) => gaussG q.2 q.1 :=
    (continuous_gaussG_uncurry.comp continuous_swap).measurable
  have hPE : Measurable fun q : (Site L → ℝ) × (SquareZeroBond L → ℝ) => PE L β q.1 :=
    ((continuous_PE hβ).comp continuous_fst).measurable
  exact (ENNReal.measurable_ofReal.comp ((measurable_mixWeight β).comp measurable_snd)).mul
    ((ENNReal.measurable_ofReal.comp (hG.mul hPE)).mul (hF.comp measurable_fst))

/-- **The literal weight as a mixture of Gaussians**:
`∫ ρ(φ) F(φ) dC_A = ∫ Π_e w(x_e) ∫ e^{−Q_{x²}(φ)} P_E(φ) F(φ) dC_A dx`. -/
theorem lintegral_boxWeight_eq_mix {β : ℝ} (hβ : 0 < β) (A : Finset (Site L))
    {F : (Site L → ℝ) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ φ, ENNReal.ofReal (boxWeight L β φ) * F φ ∂combMeasure A =
      ∫⁻ x, ENNReal.ofReal (mixWeight β x) *
        ∫⁻ φ, ENNReal.ofReal (gaussG x φ * PE L β φ) * F φ ∂combMeasure A ∂precMeasure L := by
  have hpt : ∀ φ, ENNReal.ofReal (boxWeight L β φ) * F φ =
      ∫⁻ x, ENNReal.ofReal (mixWeight β x) *
        (ENNReal.ofReal (gaussG x φ * PE L β φ) * F φ) ∂precMeasure L := fun φ => by
    have hm : Measurable fun x : SquareZeroBond L → ℝ => ENNReal.ofReal (mixWeight β x * gaussG x φ) :=
      ENNReal.measurable_ofReal.comp ((measurable_mixWeight β).mul
        ((continuous_gaussG_uncurry.comp (continuous_id.prodMk continuous_const)).measurable))
    have h1 : ∀ x : SquareZeroBond L → ℝ, ENNReal.ofReal (mixWeight β x) *
        (ENNReal.ofReal (gaussG x φ * PE L β φ) * F φ) =
        ENNReal.ofReal (mixWeight β x * gaussG x φ) * (ENNReal.ofReal (PE L β φ) * F φ) :=
      fun x => by
        rw [ENNReal.ofReal_mul (gaussG_pos x φ).le, ENNReal.ofReal_mul (mixWeight_nonneg hβ.le x)]
        ring
    simp_rw [h1]
    rw [lintegral_mul_const _ hm, lintegral_mix_gauss_zero hβ φ, boxWeight_eq hβ.le,
      ENNReal.ofReal_mul (Finset.prod_nonneg fun e _ => (Lw_pos β _).le)]
    ring
  simp_rw [hpt]
  rw [lintegral_lintegral_swap ((measurable_boxWeight_mix hβ.le hF).aemeasurable)]
  refine lintegral_congr fun x => ?_
  rw [lintegral_const_mul _ (by
    have hG : Measurable fun φ : Site L → ℝ => gaussG x φ :=
      (continuous_gaussG_uncurry.comp (continuous_const.prodMk continuous_id)).measurable
    exact (ENNReal.measurable_ofReal.comp (hG.mul (continuous_PE hβ.le).measurable)).mul hF)]

/-- The comb density of the precisions, `S(x) = ∫ e^{−Q_{x²}(φ)} P_E(φ) dC_A`. -/
def combDensity (L : ℕ) (β : ℝ) (A : Finset (Site L)) (x : SquareZeroBond L → ℝ) : ℝ≥0∞ :=
  ∫⁻ φ, ENNReal.ofReal (gaussG x φ * PE L β φ) ∂combMeasure A

theorem measurable_combDensity {β : ℝ} (hβ : 0 ≤ β) (A : Finset (Site L)) :
    Measurable (combDensity L β A) := by
  unfold combDensity
  have h : Measurable fun q : (SquareZeroBond L → ℝ) × (Site L → ℝ) =>
      ENNReal.ofReal (gaussG q.1 q.2 * PE L β q.2) :=
    ENNReal.measurable_ofReal.comp ((continuous_gaussG_uncurry.mul
      ((continuous_PE hβ).comp continuous_snd)).measurable)
  exact h.lintegral_prod_right'

/-- **The law of the precisions**, `Z⁻¹ Π_e w(x_e) S(x) dx`. -/
def precLaw (L : ℕ) (β : ℝ) (A : Finset (Site L)) : Measure (SquareZeroBond L → ℝ) :=
  (literalPartition L β A)⁻¹ •
    (precMeasure L).withDensity fun x => ENNReal.ofReal (mixWeight β x) * combDensity L β A x

theorem lintegral_precLaw {β : ℝ} (hβ : 0 ≤ β) (A : Finset (Site L))
    {g : (SquareZeroBond L → ℝ) → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x, g x ∂precLaw L β A = (literalPartition L β A)⁻¹ *
      ∫⁻ x, ENNReal.ofReal (mixWeight β x) * combDensity L β A x * g x ∂precMeasure L := by
  have hm : Measurable fun x : SquareZeroBond L → ℝ =>
      ENNReal.ofReal (mixWeight β x) * combDensity L β A x :=
    (ENNReal.measurable_ofReal.comp (measurable_mixWeight β)).mul (measurable_combDensity hβ A)
  unfold precLaw
  rw [lintegral_smul_measure, lintegral_withDensity_eq_lintegral_mul _ hm hg, smul_eq_mul]
  rfl

theorem literalPartition_ne_zero (hL : 1 < L) {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1)
    (A : Finset (Site L)) : literalPartition L β A ≠ 0 := by
  rw [literalPartition_eq hL hβ hβ1 A]
  exact (ENNReal.ofReal_pos.mpr (tsum_literalWeight_pos hL hβ hβ1 A)).ne'

theorem literalPartition_ne_top (hL : 1 < L) {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1)
    (A : Finset (Site L)) : literalPartition L β A ≠ ⊤ := by
  rw [literalPartition_eq hL hβ hβ1 A]
  exact ENNReal.ofReal_ne_top

theorem isProbabilityMeasure_precLaw (hL : 1 < L) {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1)
    (A : Finset (Site L)) : IsProbabilityMeasure (precLaw L β A) := by
  constructor
  have h := lintegral_precLaw hβ.le A (g := fun _ => 1) measurable_const
  rw [lintegral_one] at h
  simp only [mul_one] at h
  rw [h]
  have h2 := lintegral_boxWeight_eq_mix hβ A (F := fun _ => 1) measurable_const
  simp only [mul_one] at h2
  unfold combDensity
  rw [← h2, ← literalPartition_eq_comb hβ.le A]
  exact ENNReal.inv_mul_cancel (literalPartition_ne_zero hL hβ hβ1 A)
    (literalPartition_ne_top hL hβ hβ1 A)

/-! ## The moment bound -/

/-- The divergence `f_v = Σ_e θ_e ∇1_v(e)` of a flow `θ`. -/
def flowDiv (θ : SquareZeroBond L → ℝ) (v : Site L) : ℝ :=
  ∑ e, θ e * pinnedGrad L (Pi.single v 1) e

theorem sum_flow_eq (θ : SquareZeroBond L → ℝ) (ψ : Site L → ℝ) :
    ∑ e, θ e * pinnedGrad L ψ e = ∑ v, flowDiv θ v * ψ v := by
  have hlin : ∀ ψ : Site L → ℝ, ∑ e, θ e * pinnedGrad L ψ e =
      ((Fintype.linearCombination ℝ θ) ∘ₗ pinnedGrad L) ψ := fun ψ => by
    rw [LinearMap.comp_apply, Fintype.linearCombination_apply]
    exact Finset.sum_congr rfl fun e _ => by rw [smul_eq_mul, mul_comm]
  rw [hlin, LinearMap.pi_apply_eq_sum_univ]
  refine Finset.sum_congr rfl fun v _ => ?_
  have hsingle : (fun j => if v = j then (1 : ℝ) else 0) = Pi.single v 1 :=
    funext fun w => by rw [Pi.single_apply]; exact if_congr eq_comm rfl rfl
  rw [smul_eq_mul, ← hlin, mul_comm, hsingle]
  rfl

theorem ae_precMeasure_pos : ∀ᵐ x ∂precMeasure L, ∀ e, 0 < x e := by
  rw [ae_iff]
  have hset : {x : SquareZeroBond L → ℝ | ¬∀ e, 0 < x e} =
      ⋃ e, Function.eval e ⁻¹' Iic (0 : ℝ) := by
    ext x
    simp only [Set.mem_ofPred_eq, not_forall, not_lt, Set.mem_iUnion, Set.mem_preimage,
      Function.eval, Set.mem_Iic]
  rw [hset]
  refine measure_iUnion_null fun e => ?_
  unfold precMeasure
  refine Measure.pi_eval_preimage_null _ ?_
  rw [Measure.restrict_apply measurableSet_Iic, Set.Iic_inter_Ioi]
  simp

theorem lintegral_literalState_eq_mix (hL : 1 < L) {β : ℝ} (hβ : 0 < β) (A : Finset (Site L))
    {F : (Site L → ℝ) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ φ, F φ ∂literalState L β A = (literalPartition L β A)⁻¹ *
      ∫⁻ x, ENNReal.ofReal (mixWeight β x) *
        ∫⁻ φ, ENNReal.ofReal (gaussG x φ * PE L β φ) * F φ ∂combMeasure A ∂precMeasure L := by
  have _ := hL
  rw [lintegral_literalState hβ.le A hF, ← lintegral_boxWeight_eq_mix hβ A hF,
    lintegral_combMeasure A (F := fun φ => ENNReal.ofReal (boxWeight L β φ) * F φ)
      ((ENNReal.measurable_ofReal.comp (continuous_boxWeight hβ.le).measurable).mul hF)]

/-- **The moment of a flow**: if `θ` is supported on `P` and `|θ_e| ≤ c`, then
`⟨e^{Σ_e θ_e ∇φ(e)}⟩ ≤ M(c²/2)` with `M = mgfExt precLaw R_P`. -/
theorem lintegral_exp_flow_le (hL : 1 < L) {β : ℝ} (hβ : 0 < β) (A : Finset (Site L))
    (P : Finset (SquareZeroBond L)) {c : ℝ} {θ : SquareZeroBond L → ℝ}
    (hθP : ∀ e ∉ P, θ e = 0) (hθc : ∀ e, |θ e| ≤ c) :
    ∫⁻ φ, ENNReal.ofReal (Real.exp (∑ e, θ e * pinnedGrad L φ e)) ∂literalState L β A ≤
      mgfExt (precLaw L β A) (resP P) (c ^ 2 / 2) := by
  have hg : Continuous (pinnedGrad L) := (pinnedGrad L).continuous_of_finiteDimensional
  have hFm : Measurable fun φ : Site L → ℝ =>
      ENNReal.ofReal (Real.exp (∑ e, θ e * pinnedGrad L φ e)) := by
    refine ENNReal.measurable_ofReal.comp (Real.continuous_exp.comp ?_).measurable
    exact continuous_finsetSum _ fun e _ => continuous_const.mul ((continuous_apply e).comp hg)
  rw [lintegral_literalState_eq_mix hL hβ A hFm]
  unfold mgfExt
  rw [lintegral_precLaw hβ.le A (g := fun x => ENNReal.ofReal (Real.exp (c ^ 2 / 2 * resP P x)))
    (ENNReal.measurable_ofReal.comp (Real.continuous_exp.measurable.comp
      ((measurable_resP P).const_mul _)))]
  refine mul_le_mul_right (lintegral_mono_ae ?_) _
  filter_upwards [ae_precMeasure_pos] with x hx
  have hp : ∀ e, 0 < x e ^ 2 := fun e => pow_pos (hx e) 2
  have hdom := lintegral_gauss_domination (L := L) (β := β) (p := fun e => x e ^ 2)
    (by have := hL; exact this) hβ hp A (f := flowDiv θ) (θ := θ) (sum_flow_eq θ)
  have hlhs : ∀ φ : Site L → ℝ, ENNReal.ofReal (gaussG x φ * PE L β φ) *
      ENNReal.ofReal (Real.exp (∑ e, θ e * pinnedGrad L φ e)) =
      ENNReal.ofReal (Real.exp (∑ v, flowDiv θ v * φ v) *
        (Real.exp (-gaussQ (fun e => x e ^ 2) φ) * PE L β φ)) := fun φ => by
    rw [← ENNReal.ofReal_mul (mul_nonneg (gaussG_pos x φ).le (PE_pos β φ).le), sum_flow_eq,
      mul_comm, gaussG]
  simp_rw [hlhs]
  have hbound : ∑ e, θ e ^ 2 / (4 * x e ^ 2) ≤ c ^ 2 / 2 * resP P x := by
    unfold resP
    rw [Finset.mul_sum, ← Finset.sum_subset (Finset.subset_univ P) (fun e _ he => by
      rw [hθP e he]; ring)]
    refine Finset.sum_le_sum fun e _ => ?_
    have hθ2 : θ e ^ 2 ≤ c ^ 2 := by
      have := hθc e
      have hc : 0 ≤ c := (abs_nonneg _).trans this
      nlinarith [abs_nonneg (θ e), sq_abs (θ e)]
    have hxe := hp e
    rw [show c ^ 2 / 2 * (1 / (2 * x e ^ 2)) = c ^ 2 / (4 * x e ^ 2) by field_simp; ring]
    exact div_le_div_of_nonneg_right hθ2 (by positivity)
  calc ENNReal.ofReal (mixWeight β x) * ∫⁻ φ, ENNReal.ofReal (Real.exp (∑ v, flowDiv θ v * φ v) *
        (Real.exp (-gaussQ (fun e => x e ^ 2) φ) * PE L β φ)) ∂combMeasure A
      ≤ ENNReal.ofReal (mixWeight β x) * (ENNReal.ofReal (Real.exp
          (∑ e, θ e ^ 2 / (4 * x e ^ 2))) * ∫⁻ φ, ENNReal.ofReal
            (Real.exp (-gaussQ (fun e => x e ^ 2) φ) * PE L β φ) ∂combMeasure A) :=
        mul_le_mul_right hdom _
    _ ≤ ENNReal.ofReal (mixWeight β x) * combDensity L β A x *
          ENNReal.ofReal (Real.exp (c ^ 2 / 2 * resP P x)) := by
        rw [mul_assoc, mul_comm (ENNReal.ofReal (Real.exp _)) _]
        refine mul_le_mul_right (mul_le_mul_right (ENNReal.ofReal_le_ofReal
          (Real.exp_le_exp.mpr hbound)) _) _

end FroehlichSpencer.BKT.SOS.Literal

end
