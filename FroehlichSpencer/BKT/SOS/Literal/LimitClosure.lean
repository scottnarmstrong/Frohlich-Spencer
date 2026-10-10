/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.SOS.Literal.LimitJoint

/-!
# The self-consistent bound on the precisions (the comb-inserted SOS construction)

Let `M(λ) = mgfExt precLaw R_P λ`, `R_P(x) = Σ_{e∈P} 1/(2x_e²)`, `k = |P|`, `β_λ = √(β² − 2λ)`,
`δ = β − β_λ` and `K₀ = (β/β_λ) e^{δ√q₀}`. For `0 ≤ λ < β²/2`:

* `mgf_le_tilt`: `M(λ) ≤ K₀^k ⟨e^{δ Σ_{e∈P} |∇φ(e)|}⟩`. Integrate out the precisions given the field
  (`lintegral_mix_gauss`) and bound the tilted mixture by `K₀ e^{δ|t|} L_β(t)` (`mixTilt_le`).
* `lintegral_exp_abs_le`: `⟨e^{δ Σ_P |∇φ|}⟩ ≤ 2^k M(δ²/2)` (expand into `2^k` sign patterns and use
  `lintegral_exp_flow_le`).
* `lintegral_exp_abs_lt_top`: `⟨e^{δ Σ_P |∇φ|}⟩ < ∞` for `δ < β`, by comparison with the literal
  partition function at `β − δ`.
* `mgf_le_bound`: hence `M(λ) ≤ (2K₀)^k M(θλ) ≤ (2K₀)^k M(λ)^θ` with `θ = 2λ/β² < 1`, and so
  `M(λ) ≤ (2K₀)^{k/(1−θ)}`.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.SOS.Literal

open MeasureTheory Set Filter Topology
open scoped Real ENNReal
open FroehlichSpencer.BKT.Generic.PinnedCharges (SquareZeroBond Site)
open FroehlichSpencer.BKT.SOS.Roughening

variable {L : ℕ}

/-- `β_λ = √(β² − 2λ)`. -/
def betaLam (β lam : ℝ) : ℝ := Real.sqrt (β ^ 2 - 2 * lam)

/-- `K₀ = (β/β_λ) e^{(β−β_λ)√q₀}`. -/
def tiltK0 (β lam : ℝ) : ℝ :=
  β / betaLam β lam * Real.exp ((β - betaLam β lam) * Real.sqrt (mixQ0 β))

theorem betaLam_pos {β lam : ℝ} (hl : 2 * lam < β ^ 2) : 0 < betaLam β lam :=
  Real.sqrt_pos.mpr (by linarith)

theorem betaLam_le {β lam : ℝ} (hβ : 0 < β) (hl0 : 0 ≤ lam) : betaLam β lam ≤ β := by
  unfold betaLam
  rw [Real.sqrt_le_left hβ.le]
  linarith

theorem betaLam_zero {β : ℝ} (hβ : 0 < β) : betaLam β 0 = β := by
  unfold betaLam
  rw [mul_zero, sub_zero, Real.sqrt_sq hβ.le]

theorem tiltK0_pos {β lam : ℝ} (hβ : 0 < β) (hl : 2 * lam < β ^ 2) : 0 < tiltK0 β lam := by
  unfold tiltK0
  have := betaLam_pos hl
  positivity

/-- The bond factors after integrating out the precisions. -/
theorem prod_tilt_le {β : ℝ} (hβ : 0 < β) {lam : ℝ} (hl0 : 0 ≤ lam) (hl : 2 * lam < β ^ 2)
    (P : Finset (SquareZeroBond L)) (t : SquareZeroBond L → ℝ) :
    ∏ e, (β / betaLam β (if e ∈ P then lam else 0) *
        Real.exp (-(betaLam β (if e ∈ P then lam else 0) * Real.sqrt (mixQ0 β + t e ^ 2)))) ≤
      tiltK0 β lam ^ P.card *
        Real.exp ((β - betaLam β lam) * ∑ e ∈ P, |t e|) * ∏ e, Lw β (t e) := by
  classical
  set g : SquareZeroBond L → ℝ := fun e =>
    if e ∈ P then tiltK0 β lam * Real.exp ((β - betaLam β lam) * |t e|) else 1 with hg
  have hle : ∀ e, β / betaLam β (if e ∈ P then lam else 0) *
      Real.exp (-(betaLam β (if e ∈ P then lam else 0) * Real.sqrt (mixQ0 β + t e ^ 2))) ≤
        g e * Lw β (t e) := by
    intro e
    by_cases he : e ∈ P
    · simp only [he, ↓reduceIte, hg]
      have h := mixTilt_le hβ hl0 hl (t e)
      unfold tiltK0 betaLam
      linarith
    · simp only [he, ↓reduceIte, hg, betaLam_zero hβ, div_self hβ.ne', one_mul, Lw_eq hβ]
      exact le_rfl
  have hprod := Finset.prod_le_prod₀ (s := Finset.univ) (fun e _ => by
    have := betaLam_pos (β := β) (lam := if e ∈ P then lam else 0) (by split_ifs <;> nlinarith)
    positivity) fun e _ => hle e
  refine hprod.trans (le_of_eq ?_)
  rw [Finset.prod_mul_distrib]
  congr 1
  simp only [hg]
  rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_mul_distrib, Finset.prod_const,
    ← Real.exp_sum, Finset.mul_sum]

/-- **The tilt bound** `M(λ) ≤ K₀^k ⟨e^{δ Σ_P |∇φ|}⟩`. -/
theorem mgf_le_tilt {β : ℝ} (hβ : 0 < β) (A : Finset (Site L))
    (P : Finset (SquareZeroBond L)) {lam : ℝ} (hl0 : 0 ≤ lam) (hl : 2 * lam < β ^ 2) :
    mgfExt (precLaw L β A) (resP P) lam ≤ ENNReal.ofReal (tiltK0 β lam ^ P.card) *
      ∫⁻ φ, ENNReal.ofReal (Real.exp ((β - betaLam β lam) * ∑ e ∈ P, |pinnedGrad L φ e|))
        ∂literalState L β A := by
  classical
  set lamv : SquareZeroBond L → ℝ := fun e => if e ∈ P then lam else 0 with hlamv
  have hlamv2 : ∀ e, 2 * lamv e < β ^ 2 := fun e => by
    simp only [hlamv]; split_ifs <;> nlinarith
  have hres : ∀ x : SquareZeroBond L → ℝ,
      lam * resP P x = ∑ e, lamv e / (2 * x e ^ 2) := fun x => by
    unfold resP
    rw [Finset.mul_sum, ← Finset.sum_subset (Finset.subset_univ P) (fun e _ he => by
      simp only [hlamv, he, ↓reduceIte, zero_div])]
    refine Finset.sum_congr rfl fun e he => ?_
    simp only [hlamv, he, ↓reduceIte]
    ring
  have hg : Continuous (pinnedGrad L) := (pinnedGrad L).continuous_of_finiteDimensional
  have hFm : Measurable fun φ : Site L → ℝ =>
      ENNReal.ofReal (Real.exp ((β - betaLam β lam) * ∑ e ∈ P, |pinnedGrad L φ e|)) := by
    refine ENNReal.measurable_ofReal.comp (Real.continuous_exp.comp ?_).measurable
    exact continuous_const.mul (continuous_finsetSum _ fun e _ =>
      ((continuous_apply e).comp hg).abs)
  unfold mgfExt
  rw [lintegral_precLaw hβ.le A (g := fun x => ENNReal.ofReal (Real.exp (lam * resP P x)))
    (ENNReal.measurable_ofReal.comp (Real.continuous_exp.measurable.comp
      ((measurable_resP P).const_mul _))), lintegral_literalState hβ.le A hFm,
    ← lintegral_combMeasure A (F := fun φ => ENNReal.ofReal (boxWeight L β φ) *
      ENNReal.ofReal (Real.exp ((β - betaLam β lam) * ∑ e ∈ P, |pinnedGrad L φ e|)))
      ((ENNReal.measurable_ofReal.comp (continuous_boxWeight hβ.le).measurable).mul hFm)]
  have hGm : ∀ x : SquareZeroBond L → ℝ, Measurable fun φ : Site L → ℝ =>
      ENNReal.ofReal (gaussG x φ * PE L β φ) := fun x =>
    ENNReal.measurable_ofReal.comp (((continuous_gaussG_uncurry.comp
      (continuous_const.prodMk continuous_id)).mul (continuous_PE hβ.le)).measurable)
  have hb : ∀ x : SquareZeroBond L → ℝ, ENNReal.ofReal (mixWeight β x) * combDensity L β A x *
      ENNReal.ofReal (Real.exp (lam * resP P x)) =
      ∫⁻ φ, ENNReal.ofReal (mixWeight β x * Real.exp (∑ e, lamv e / (2 * x e ^ 2)) *
        gaussG x φ) * ENNReal.ofReal (PE L β φ) ∂combMeasure A := fun x => by
    unfold combDensity
    rw [mul_right_comm, ← lintegral_const_mul _ (hGm x)]
    refine lintegral_congr fun φ => ?_
    rw [hres, ← ENNReal.ofReal_mul (mixWeight_nonneg hβ.le x), ← ENNReal.ofReal_mul
      (mul_nonneg (mixWeight_nonneg hβ.le x) (Real.exp_pos _).le), ← ENNReal.ofReal_mul
      (mul_nonneg (mul_nonneg (mixWeight_nonneg hβ.le x) (Real.exp_pos _).le)
        (gaussG_pos x φ).le)]
    ring_nf
  simp_rw [hb]
  have hjoint : Measurable fun q : (SquareZeroBond L → ℝ) × (Site L → ℝ) =>
      ENNReal.ofReal (mixWeight β q.1 * Real.exp (∑ e, lamv e / (2 * q.1 e ^ 2)) *
        gaussG q.1 q.2) * ENNReal.ofReal (PE L β q.2) := by
    refine (ENNReal.measurable_ofReal.comp ((((measurable_mixWeight β).comp measurable_fst).mul
      (Real.continuous_exp.measurable.comp (Finset.measurable_sum _ fun e _ =>
        (measurable_const.div (by fun_prop))))).mul
      continuous_gaussG_uncurry.measurable)).mul ?_
    exact ENNReal.measurable_ofReal.comp ((continuous_PE hβ.le).measurable.comp measurable_snd)
  rw [lintegral_lintegral_swap hjoint.aemeasurable]
  have hxm : ∀ φ : Site L → ℝ, Measurable fun x : SquareZeroBond L → ℝ =>
      ENNReal.ofReal (mixWeight β x * Real.exp (∑ e, lamv e / (2 * x e ^ 2)) * gaussG x φ) :=
    fun φ => ENNReal.measurable_ofReal.comp (((measurable_mixWeight β).mul
      (Real.continuous_exp.measurable.comp (Finset.measurable_sum _ fun e _ =>
        (measurable_const.div (by fun_prop))))).mul
      (continuous_gaussG_uncurry.comp (continuous_id.prodMk continuous_const)).measurable)
  have hBm : Measurable fun φ : Site L → ℝ => ENNReal.ofReal (boxWeight L β φ) *
      ENNReal.ofReal (Real.exp ((β - betaLam β lam) * ∑ e ∈ P, |pinnedGrad L φ e|)) :=
    (ENNReal.measurable_ofReal.comp (continuous_boxWeight hβ.le).measurable).mul hFm
  have hφ : ∀ φ : Site L → ℝ, ∫⁻ x, ENNReal.ofReal (mixWeight β x *
      Real.exp (∑ e, lamv e / (2 * x e ^ 2)) * gaussG x φ) * ENNReal.ofReal (PE L β φ)
        ∂precMeasure L = ENNReal.ofReal (PE L β φ) * ∏ e, ENNReal.ofReal (β /
          Real.sqrt (β ^ 2 - 2 * lamv e) * Real.exp (-(Real.sqrt (β ^ 2 - 2 * lamv e) *
            Real.sqrt (mixQ0 β + pinnedGrad L φ e ^ 2)))) := fun φ => by
    rw [lintegral_mul_const _ (hxm φ), lintegral_mix_gauss hβ lamv hlamv2 φ, mul_comm]
  simp_rw [hφ]
  rw [mul_left_comm, ← lintegral_const_mul _ hBm]
  refine mul_le_mul_right (lintegral_mono fun φ => ?_) _
  rw [← ENNReal.ofReal_prod_of_nonneg fun e _ => by positivity, ← ENNReal.ofReal_mul
    (PE_pos β φ).le, ← ENNReal.ofReal_mul (boxWeight_pos hβ.le φ).le,
    ← ENNReal.ofReal_mul (pow_nonneg (tiltK0_pos hβ hl).le _)]
  refine ENNReal.ofReal_le_ofReal ?_
  have h := prod_tilt_le hβ hl0 hl P (fun e => pinnedGrad L φ e)
  unfold betaLam at h
  rw [boxWeight_eq hβ.le]
  have hPE := PE_pos β φ
  calc PE L β φ * ∏ e, (β / Real.sqrt (β ^ 2 - 2 * lamv e) *
        Real.exp (-(Real.sqrt (β ^ 2 - 2 * lamv e) * Real.sqrt (mixQ0 β + pinnedGrad L φ e ^ 2))))
      ≤ PE L β φ * (tiltK0 β lam ^ P.card * Real.exp ((β - Real.sqrt (β ^ 2 - 2 * lam)) *
          ∑ e ∈ P, |pinnedGrad L φ e|) * ∏ e, Lw β (pinnedGrad L φ e)) :=
        mul_le_mul_of_nonneg_left h hPE.le
    _ = _ := by unfold betaLam; ring

/-! ## Sign patterns -/

/-- The sign pattern of `S ⊆ P`: `δ` on `S`, `−δ` on `P ∖ S`, `0` off `P`. -/
def signFlow (P S : Finset (SquareZeroBond L)) (δ : ℝ) (e : SquareZeroBond L) : ℝ :=
  if e ∈ S then δ else if e ∈ P then -δ else 0

theorem exp_sum_abs_le (P : Finset (SquareZeroBond L)) (δ : ℝ) (t : SquareZeroBond L → ℝ) :
    Real.exp (δ * ∑ e ∈ P, |t e|) ≤
      ∑ S ∈ P.powerset, Real.exp (∑ e, signFlow P S δ e * t e) := by
  classical
  have h1 : Real.exp (δ * ∑ e ∈ P, |t e|) ≤
      ∏ e ∈ P, (Real.exp (δ * t e) + Real.exp (-(δ * t e))) := by
    rw [Finset.mul_sum, Real.exp_sum]
    refine Finset.prod_le_prod₀ (fun e _ => (Real.exp_pos _).le) fun e _ => ?_
    rcases le_or_gt 0 (t e) with h | h
    · rw [abs_of_nonneg h]; linarith [Real.exp_pos (-(δ * t e))]
    · rw [abs_of_neg h, show δ * -t e = -(δ * t e) by ring]; linarith [Real.exp_pos (δ * t e)]
  refine h1.trans (le_of_eq ?_)
  rw [Finset.prod_add]
  refine Finset.sum_congr rfl fun S hS => ?_
  have hSP : S ⊆ P := Finset.mem_powerset.mp hS
  rw [← Real.exp_sum, ← Real.exp_sum, ← Real.exp_add]
  congr 1
  have hsupp : ∑ e, signFlow P S δ e * t e = ∑ e ∈ P, signFlow P S δ e * t e := by
    refine (Finset.sum_subset (Finset.subset_univ P) fun e _ he => ?_).symm
    have heS : e ∉ S := fun h => he (hSP h)
    simp only [signFlow, heS, he, ↓reduceIte, zero_mul]
  have hR : ∑ e ∈ P, signFlow P S δ e * t e =
      ∑ e ∈ S, δ * t e + ∑ e ∈ P \ S, -(δ * t e) := by
    rw [← Finset.sum_sdiff hSP, add_comm]
    congr 1
    · refine Finset.sum_congr rfl fun e he => ?_
      simp only [signFlow, he, ↓reduceIte]
    · refine Finset.sum_congr rfl fun e he => ?_
      have he' := Finset.mem_sdiff.mp he
      simp only [signFlow, he'.2, he'.1, ↓reduceIte]
      ring
  rw [hsupp, hR]

/-- **The sign expansion** `⟨e^{δ Σ_P |∇φ|}⟩ ≤ 2^k M(δ²/2)`. -/
theorem lintegral_exp_abs_le (hL : 1 < L) {β : ℝ} (hβ : 0 < β) (A : Finset (Site L))
    (P : Finset (SquareZeroBond L)) {δ : ℝ} (hδ : 0 ≤ δ) :
    ∫⁻ φ, ENNReal.ofReal (Real.exp (δ * ∑ e ∈ P, |pinnedGrad L φ e|)) ∂literalState L β A ≤
      2 ^ P.card * mgfExt (precLaw L β A) (resP P) (δ ^ 2 / 2) := by
  classical
  have hg : Continuous (pinnedGrad L) := (pinnedGrad L).continuous_of_finiteDimensional
  have hSm : ∀ S : Finset (SquareZeroBond L), Measurable fun φ : Site L → ℝ =>
      ENNReal.ofReal (Real.exp (∑ e, signFlow P S δ e * pinnedGrad L φ e)) := fun S =>
    ENNReal.measurable_ofReal.comp (Real.continuous_exp.comp (continuous_finsetSum _ fun e _ =>
      continuous_const.mul ((continuous_apply e).comp hg))).measurable
  calc ∫⁻ φ, ENNReal.ofReal (Real.exp (δ * ∑ e ∈ P, |pinnedGrad L φ e|)) ∂literalState L β A
      ≤ ∫⁻ φ, ∑ S ∈ P.powerset, ENNReal.ofReal
          (Real.exp (∑ e, signFlow P S δ e * pinnedGrad L φ e)) ∂literalState L β A := by
        refine lintegral_mono fun φ => ?_
        rw [← ENNReal.ofReal_sum_of_nonneg fun S _ => (Real.exp_pos _).le]
        exact ENNReal.ofReal_le_ofReal (exp_sum_abs_le P δ _)
    _ = ∑ S ∈ P.powerset, ∫⁻ φ, ENNReal.ofReal
          (Real.exp (∑ e, signFlow P S δ e * pinnedGrad L φ e)) ∂literalState L β A :=
        lintegral_finsetSum _ fun S _ => hSm S
    _ ≤ ∑ _S ∈ P.powerset, mgfExt (precLaw L β A) (resP P) (δ ^ 2 / 2) := by
        refine Finset.sum_le_sum fun S hS => lintegral_exp_flow_le hL hβ A P (fun e he => ?_)
          fun e => ?_
        · have heS : e ∉ S := fun h => he (Finset.mem_powerset.mp hS h)
          simp only [signFlow, heS, he, ↓reduceIte]
        · unfold signFlow
          split_ifs <;> simp [abs_of_nonneg hδ, hδ]
    _ = 2 ^ P.card * mgfExt (precLaw L β A) (resP P) (δ ^ 2 / 2) := by
        rw [Finset.sum_const, Finset.card_powerset, nsmul_eq_mul]
        push_cast
        rfl

/-! ## A priori finiteness -/

theorem sosInterp_re_le_exp {β : ℝ} (hβ : 0 ≤ β) (t : ℝ) :
    (Interp.sosInterp β t).re ≤ Real.exp (seriesConst β) * Real.exp (-(β * |t|)) :=
  (Complex.re_le_norm _).trans (norm_sosInterp_ofReal_le_exp hβ t)

/-- `ρ_β(φ) e^{δ Σ_P |∇φ|} ≤ C ρ_{β−δ}(φ)`. -/
theorem boxWeight_mul_exp_le {β δ : ℝ} (hβ : 0 ≤ β) (hδ0 : 0 ≤ δ) (hδ : δ ≤ β)
    (P : Finset (SquareZeroBond L)) (φ : Site L → ℝ) :
    boxWeight L β φ * Real.exp (δ * ∑ e ∈ P, |pinnedGrad L φ e|) ≤
      (Real.exp (seriesConst β) / (Real.exp (-((β - δ) ^ (2 / 3 : ℝ))) *
        Real.exp (-seriesConst (β - δ)))) ^ Fintype.card (SquareZeroBond L) *
        boxWeight L (β - δ) φ := by
  classical
  set κ := Real.exp (-((β - δ) ^ (2 / 3 : ℝ))) * Real.exp (-seriesConst (β - δ)) with hκ
  have hκ0 : 0 < κ := by positivity
  have hsum : ∑ e ∈ P, |pinnedGrad L φ e| ≤ ∑ e, |pinnedGrad L φ e| :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ P) fun e _ _ => abs_nonneg _
  have h1 : boxWeight L β φ * Real.exp (δ * ∑ e ∈ P, |pinnedGrad L φ e|) ≤
      ∏ e, ((Interp.sosInterp β (pinnedGrad L φ e : ℂ)).re *
        Real.exp (δ * |pinnedGrad L φ e|)) := by
    rw [Finset.prod_mul_distrib, ← Real.exp_sum, ← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hsum hδ0))
      (boxWeight_pos hβ φ).le
  refine h1.trans ?_
  unfold boxWeight
  rw [← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod₀ (fun e _ => mul_nonneg
    (Interp.sosInterp_ofReal_im_eq_zero_and_re_pos hβ _).2.le (Real.exp_pos _).le) fun e _ => ?_
  set t := pinnedGrad L φ e
  have hup := sosInterp_re_le_exp hβ t
  have hlow := sosInterp_re_ge_exp (by linarith : (0 : ℝ) ≤ β - δ) t
  rw [← hκ] at hlow
  calc (Interp.sosInterp β (t : ℂ)).re * Real.exp (δ * |t|)
      ≤ Real.exp (seriesConst β) * Real.exp (-(β * |t|)) * Real.exp (δ * |t|) :=
        mul_le_mul_of_nonneg_right hup (Real.exp_pos _).le
    _ = Real.exp (seriesConst β) / κ * (κ * Real.exp (-((β - δ) * |t|))) := by
        rw [mul_assoc, ← Real.exp_add]
        field_simp
        ring_nf
    _ ≤ Real.exp (seriesConst β) / κ * (Interp.sosInterp (β - δ) (t : ℂ)).re :=
        mul_le_mul_of_nonneg_left hlow (by positivity)

/-- **A priori finiteness** `⟨e^{δ Σ_P |∇φ|}⟩ < ∞` for `0 ≤ δ < β ≤ 1`. -/
theorem lintegral_exp_abs_lt_top (hL : 1 < L) {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1)
    (A : Finset (Site L)) (P : Finset (SquareZeroBond L)) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ < β) :
    ∫⁻ φ, ENNReal.ofReal (Real.exp (δ * ∑ e ∈ P, |pinnedGrad L φ e|)) ∂literalState L β A < ⊤ := by
  have hg : Continuous (pinnedGrad L) := (pinnedGrad L).continuous_of_finiteDimensional
  have hFm : Measurable fun φ : Site L → ℝ =>
      ENNReal.ofReal (Real.exp (δ * ∑ e ∈ P, |pinnedGrad L φ e|)) := by
    refine ENNReal.measurable_ofReal.comp (Real.continuous_exp.comp ?_).measurable
    exact continuous_const.mul (continuous_finsetSum _ fun e _ =>
      ((continuous_apply e).comp hg).abs)
  have hγ : 0 < β - δ := by linarith
  have hγ1 : β - δ ≤ 1 := by linarith
  set C := (Real.exp (seriesConst β) / (Real.exp (-((β - δ) ^ (2 / 3 : ℝ))) *
    Real.exp (-seriesConst (β - δ)))) ^ Fintype.card (SquareZeroBond L) with hC
  have hBm : Measurable fun φ : Site L → ℝ => ENNReal.ofReal (boxWeight L β φ) *
      ENNReal.ofReal (Real.exp (δ * ∑ e ∈ P, |pinnedGrad L φ e|)) :=
    (ENNReal.measurable_ofReal.comp (continuous_boxWeight hβ.le).measurable).mul hFm
  rw [lintegral_literalState hβ.le A hFm, ← lintegral_combMeasure A hBm]
  have hle : ∫⁻ φ, ENNReal.ofReal (boxWeight L β φ) *
      ENNReal.ofReal (Real.exp (δ * ∑ e ∈ P, |pinnedGrad L φ e|)) ∂combMeasure A ≤
      ENNReal.ofReal C * literalPartition L (β - δ) A := by
    have hγm : Measurable fun φ : Site L → ℝ => ENNReal.ofReal (boxWeight L (β - δ) φ) :=
      ENNReal.measurable_ofReal.comp (continuous_boxWeight hγ.le).measurable
    rw [literalPartition_eq_comb hγ.le A, ← lintegral_const_mul _ hγm]
    refine lintegral_mono fun φ => ?_
    rw [← ENNReal.ofReal_mul (boxWeight_pos hβ.le φ).le, ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal (boxWeight_mul_exp_le hβ.le hδ0 hδ.le P φ)
  refine ENNReal.mul_lt_top (ENNReal.inv_lt_top.mpr (pos_iff_ne_zero.mpr
    (literalPartition_ne_zero hL hβ hβ1 A))) (hle.trans_lt ?_)
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (lt_top_iff_ne_top.mpr (literalPartition_ne_top hL hγ hγ1 A))

/-! ## The closure -/

theorem mgfExt_mono_of_nonneg {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {X : Ω → ℝ}
    (hX : ∀ ω, 0 ≤ X ω) {a b : ℝ} (hab : a ≤ b) : mgfExt μ X a ≤ mgfExt μ X b :=
  lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_right hab (hX ω)))

theorem one_le_mgfExt {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX : ∀ ω, 0 ≤ X ω) {a : ℝ} (ha : 0 ≤ a) : 1 ≤ mgfExt μ X a := by
  have h := mgfExt_mono_of_nonneg μ hX ha
  rwa [mgfExt_zero] at h

theorem tilt_delta_sq_le {β lam : ℝ} (hβ : 0 < β) (hl0 : 0 ≤ lam) (hl : 2 * lam < β ^ 2) :
    (β - betaLam β lam) ^ 2 / 2 ≤ (2 * lam / β ^ 2) * lam := by
  set s := betaLam β lam
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = β ^ 2 - 2 * lam := Real.sq_sqrt (by linarith)
  have hsβ : s ≤ β := betaLam_le hβ hl0
  have hd : (β - s) * β ≤ 2 * lam := by nlinarith
  have hd0 : 0 ≤ β - s := by linarith
  have h1 : β - s ≤ 2 * lam / β := by rw [le_div_iff₀ hβ]; exact hd
  have h2 : (β - s) ^ 2 ≤ (2 * lam / β) ^ 2 := pow_le_pow_left₀ hd0 h1 2
  calc (β - s) ^ 2 / 2 ≤ (2 * lam / β) ^ 2 / 2 := by linarith
    _ = 2 * lam / β ^ 2 * lam := by field_simp

/-- **The self-consistent bound** `M(λ) ≤ (2K₀)^{k/(1−2λ/β²)}` for `0 ≤ λ < β²/2`. -/
theorem mgf_le_bound (hL : 1 < L) {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) (A : Finset (Site L))
    (P : Finset (SquareZeroBond L)) {lam : ℝ} (hl0 : 0 ≤ lam) (hl : 2 * lam < β ^ 2) :
    mgfExt (precLaw L β A) (resP P) lam ≤
      ENNReal.ofReal ((2 * tiltK0 β lam) ^ ((P.card : ℝ) / (1 - 2 * lam / β ^ 2))) := by
  have hprob := isProbabilityMeasure_precLaw hL hβ hβ1 A
  set M := mgfExt (precLaw L β A) (resP P) lam with hM
  set δ := β - betaLam β lam with hδ
  set θ := 2 * lam / β ^ 2 with hθ
  have hK0 := tiltK0_pos hβ hl
  have hδ0 : 0 ≤ δ := by rw [hδ]; linarith [betaLam_le hβ hl0]
  have hδβ : δ < β := by rw [hδ]; linarith [betaLam_pos hl]
  have hθ0 : 0 ≤ θ := by positivity
  have hθ1 : θ < 1 := by rw [hθ, div_lt_one (by positivity)]; exact hl
  -- `M ≤ (2K₀)^k M(δ²/2)`
  have h1 := mgf_le_tilt hβ A P hl0 hl
  have hfin : M < ⊤ := h1.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (lintegral_exp_abs_lt_top hL hβ hβ1 A P hδ0 hδβ))
  have h2 := lintegral_exp_abs_le hL hβ A P hδ0
  have h3 : mgfExt (precLaw L β A) (resP P) (δ ^ 2 / 2) ≤
      mgfExt (precLaw L β A) (resP P) (θ * lam) :=
    mgfExt_mono_of_nonneg _ (resP_nonneg P) (tilt_delta_sq_le hβ hl0 hl)
  have hM1 : 1 ≤ M := one_le_mgfExt _ (resP_nonneg P) hl0
  rcases eq_or_lt_of_le hl0 with hlam | hlam
  · -- `λ = 0`
    subst hlam
    rw [hM, mgfExt_zero, hθ]
    simp only [mul_zero, zero_div, sub_zero, div_one]
    rw [← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal (Real.one_le_rpow ?_ (Nat.cast_nonneg _))
    unfold tiltK0
    rw [betaLam_zero hβ, sub_self, zero_mul, Real.exp_zero, mul_one, div_self hβ.ne']
    norm_num
  have hθpos : 0 < θ := by positivity
  have h4 : mgfExt (precLaw L β A) (resP P) (θ * lam) ≤ M ^ θ := by
    have h := mgfExt_le_rpow_mul_rpow (precLaw L β A) (measurable_resP P) 0 lam hθpos hθ1
    rw [mul_zero, zero_add, mgfExt_zero, ENNReal.one_rpow, one_mul] at h
    exact h
  have hchain : M ≤ ENNReal.ofReal ((2 * tiltK0 β lam) ^ P.card) * M ^ θ := by
    calc M ≤ ENNReal.ofReal (tiltK0 β lam ^ P.card) *
          ∫⁻ φ, ENNReal.ofReal (Real.exp (δ * ∑ e ∈ P, |pinnedGrad L φ e|)) ∂literalState L β A :=
          h1
      _ ≤ ENNReal.ofReal (tiltK0 β lam ^ P.card) *
          (2 ^ P.card * mgfExt (precLaw L β A) (resP P) (δ ^ 2 / 2)) := mul_le_mul_right h2 _
      _ ≤ ENNReal.ofReal (tiltK0 β lam ^ P.card) * (2 ^ P.card * M ^ θ) :=
          mul_le_mul_right (mul_le_mul_right (h3.trans h4) _) _
      _ = ENNReal.ofReal ((2 * tiltK0 β lam) ^ P.card) * M ^ θ := by
          rw [mul_pow, ENNReal.ofReal_mul (pow_nonneg zero_le_two _), ENNReal.ofReal_pow
            zero_le_two, ENNReal.ofReal_ofNat]
          ring
  -- real algebra
  set m := M.toReal with hm
  have hMm : M = ENNReal.ofReal m := (ENNReal.ofReal_toReal hfin.ne).symm
  have hm1 : 1 ≤ m := by
    rw [hm, ← ENNReal.toReal_one]
    exact ENNReal.toReal_mono hfin.ne hM1
  have hm0 : 0 < m := by linarith
  set C := (2 * tiltK0 β lam) ^ P.card with hC
  have hC0 : 0 < C := by positivity
  rw [hMm, ENNReal.ofReal_rpow_of_nonneg hm0.le hθ0, ← ENNReal.ofReal_mul hC0.le,
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at hchain
  -- `m ≤ C m^θ` gives `m^{1−θ} ≤ C`
  have h5 : m ^ (1 - θ) ≤ C := by
    rw [Real.rpow_sub hm0, Real.rpow_one, div_le_iff₀ (Real.rpow_pos_of_pos hm0 _)]
    exact hchain
  have h6 : m ≤ C ^ (1 / (1 - θ)) := by
    have := Real.rpow_le_rpow (Real.rpow_nonneg hm0.le _) h5
      (by positivity : (0 : ℝ) ≤ 1 / (1 - θ))
    rwa [← Real.rpow_mul hm0.le, mul_one_div_cancel (by linarith), Real.rpow_one] at this
  rw [hMm]
  refine ENNReal.ofReal_le_ofReal (h6.trans (le_of_eq ?_))
  rw [hC, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  congr 1
  ring

/-- **The uniform exponential bound for flows**: for `0 ≤ c < β ≤ 1` and a flow `θ` supported on
`P` with `|θ_e| ≤ 1`, `⟨e^{c Σ_e θ_e ∇φ(e)}⟩ ≤ (2K₀)^{|P|/(1−c²/β²)}`, uniformly in the box and
in `A`. -/
theorem lintegral_exp_flow_bound (hL : 1 < L) {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1)
    (A : Finset (Site L)) (P : Finset (SquareZeroBond L)) {c : ℝ} (hc0 : 0 ≤ c) (hcβ : c < β)
    {θ : SquareZeroBond L → ℝ} (hθP : ∀ e ∉ P, θ e = 0) (hθ1 : ∀ e, |θ e| ≤ 1) :
    ∫⁻ φ, ENNReal.ofReal (Real.exp (c * ∑ e, θ e * pinnedGrad L φ e)) ∂literalState L β A ≤
      ENNReal.ofReal ((2 * tiltK0 β (c ^ 2 / 2)) ^ ((P.card : ℝ) / (1 - c ^ 2 / β ^ 2))) := by
  have hflow := lintegral_exp_flow_le hL hβ A P (c := c) (θ := fun e => c * θ e)
    (fun e he => by rw [hθP e he, mul_zero]) (fun e => by
      rw [abs_mul, abs_of_nonneg hc0]; exact mul_le_of_le_one_right hc0 (hθ1 e))
  have hc2 : 2 * (c ^ 2 / 2) < β ^ 2 := by nlinarith
  have hbound := mgf_le_bound hL hβ hβ1 A P (by positivity) hc2
  rw [show 2 * (c ^ 2 / 2) / β ^ 2 = c ^ 2 / β ^ 2 by ring] at hbound
  refine le_trans (le_of_eq ?_) (hflow.trans hbound)
  refine lintegral_congr fun φ => ?_
  congr 2
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun e _ => by ring

end FroehlichSpencer.BKT.SOS.Literal

end
