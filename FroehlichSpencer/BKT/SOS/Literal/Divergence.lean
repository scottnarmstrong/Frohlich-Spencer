/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.SOS.Literal.Theorem73
public import FroehlichSpencer.BKT.SOS.Literal.MomentExtension

/-!
# The extended moment of the literal state: evenness and divergence (the finite comb construction)

* `literalMomentExt_eq_tsum`: for `u, v ∈ A` and every `ε`,
  `⟨e^{ε[φ(u)−φ(v)]}⟩ = Z⁻¹ Σ_n W(n) e^{ε(n(u)−n(v))}` in `[0, ∞]`.
* `literalMomentExt_neg`: the extended moment is even in `ε` (`n ↦ −n`, `y ↦ −y`).
* `literalMomentExt_eq_top`: for `u ≠ v` and `|ε| ≥ 4β` it is `∞`. Raising the height at `u` by `k`
  costs at most `(κ e^{−β|k|})⁴` (`literalWeight_shift_ge`): the face `u` has at most four bonds
  (`card_incident_le_four`, counting the parallel bonds to the exterior), and on the real axis
  `κ e^{−β|s|} I_β(t) ≤ I_β(t + s)` (`sosInterp_re_shift_ge`, from
  `e^{−β^{2/3}} e^{−6β^{2/3}Σ} e^{−β|t|} ≤ I_β(t) ≤ e^{6β^{2/3}Σ} e^{−β|t|}`).
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.SOS.Literal

open MeasureTheory
open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Generic.PinnedCharges (Site SquareZeroBond)
open FroehlichSpencer.BKT.Generic.PinnedCharges.Layer (card_incident_le_four)
open FroehlichSpencer.BKT.Rotator (RotatorDualFace)
open FroehlichSpencer.BKT.SOS.Roughening
open FroehlichSpencer.BKT.Rotator.BesselInterp (latticeSum latticeSum_nonneg)

variable {L : ℕ}

/-! ## Two-sided exponential bounds on the real axis -/

/-- The series constant `6 β^{2/3} Σ_k (1+k²)⁻¹` of `E_β`. -/
def seriesConst (β : ℝ) : ℝ := β ^ (2 / 3 : ℝ) * 2 * (3 * latticeSum)

/-- `I_β(t) ≥ e^{−β^{2/3}} e^{−6β^{2/3}Σ} e^{−β|t|}`. -/
theorem sosInterp_re_ge_exp {β : ℝ} (hβ : 0 ≤ β) (t : ℝ) :
    Real.exp (-(β ^ (2 / 3 : ℝ))) * Real.exp (-seriesConst β) * Real.exp (-(β * |t|)) ≤
      (Interp.sosInterp β t).re := by
  rw [Interp.sosInterp_ofReal hβ, Complex.ofReal_re]
  have hS : -seriesConst β ≤ -∑' n : ℤ, Interp.sosDefect β n * Real.sinc (Real.pi * (t - n)) ^ 2 := by
    have h := Interp.norm_sosSeries_ofReal_le hβ t
    rw [Interp.sosSeries_ofReal, Complex.norm_real, Real.norm_eq_abs] at h
    unfold seriesConst
    linarith [le_abs_self (∑' n : ℤ, Interp.sosDefect β n * Real.sinc (Real.pi * (t - n)) ^ 2)]
  have hD : -(β ^ (2 / 3 : ℝ)) + -(β * |t|) ≤
      -(β ^ (2 / 3 : ℝ)) * Real.sqrt (1 + β ^ (2 / 3 : ℝ) * t ^ 2) := by
    set u := β ^ (1 / 3 : ℝ)
    have hu0 : 0 ≤ u := Real.rpow_nonneg hβ _
    have h23 : β ^ (2 / 3 : ℝ) = u ^ 2 := (Interp.rpow_one_third_sq hβ).symm
    have h3 : β = u ^ 3 := (Interp.rpow_one_third_cube hβ).symm
    have hsq : Real.sqrt (1 + u ^ 2 * t ^ 2) ≤ 1 + u * |t| := by
      rw [Real.sqrt_le_iff]
      refine ⟨by positivity, ?_⟩
      nlinarith [sq_abs t, abs_nonneg t, mul_nonneg hu0 (abs_nonneg t)]
    rw [h23]
    rw [h3]
    nlinarith [mul_le_mul_of_nonneg_left hsq (sq_nonneg u)]
  calc Real.exp (-(β ^ (2 / 3 : ℝ))) * Real.exp (-seriesConst β) * Real.exp (-(β * |t|))
      = Real.exp (-(β ^ (2 / 3 : ℝ)) + -(β * |t|)) * Real.exp (-seriesConst β) := by
        rw [Real.exp_add]; ring
    _ ≤ Real.exp (-(β ^ (2 / 3 : ℝ)) * Real.sqrt (1 + β ^ (2 / 3 : ℝ) * t ^ 2)) *
        Real.exp (-∑' n : ℤ, Interp.sosDefect β n * Real.sinc (Real.pi * (t - n)) ^ 2) :=
        mul_le_mul (Real.exp_le_exp.mpr hD) (Real.exp_le_exp.mpr hS) (Real.exp_pos _).le
          (Real.exp_pos _).le

/-- The shift constant `κ = e^{−β^{2/3}} e^{−12β^{2/3}Σ} ∈ (0, 1]`. -/
def shiftConst (β : ℝ) : ℝ :=
  Real.exp (-(β ^ (2 / 3 : ℝ))) * Real.exp (-seriesConst β) * Real.exp (-seriesConst β)

theorem shiftConst_pos (β : ℝ) : 0 < shiftConst β := by unfold shiftConst; positivity

theorem shiftConst_le_one {β : ℝ} (hβ : 0 ≤ β) : shiftConst β ≤ 1 := by
  have hb : 0 ≤ β ^ (2 / 3 : ℝ) := Real.rpow_nonneg hβ _
  have hs : 0 ≤ seriesConst β := by unfold seriesConst; have := latticeSum_nonneg; positivity
  unfold shiftConst
  rw [← Real.exp_add, ← Real.exp_add]
  exact Real.exp_le_one_iff.mpr (by linarith)

/-- **The shift bound on the real axis**: `κ e^{−β|s|} I_β(t) ≤ I_β(t + s)`. -/
theorem sosInterp_re_shift_ge {β : ℝ} (hβ : 0 ≤ β) (t s : ℝ) :
    shiftConst β * Real.exp (-(β * |s|)) * (Interp.sosInterp β t).re ≤
      (Interp.sosInterp β (t + s : ℝ)).re := by
  have hup : (Interp.sosInterp β t).re ≤ Real.exp (seriesConst β) * Real.exp (-(β * |t|)) :=
    (Complex.re_le_norm _).trans (norm_sosInterp_ofReal_le_exp hβ t)
  have hlow := sosInterp_re_ge_exp hβ (t + s)
  have htri : |t + s| ≤ |t| + |s| := abs_add_le t s
  have hexp : Real.exp (-(β * |t|)) * Real.exp (-(β * |s|)) ≤ Real.exp (-(β * |t + s|)) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hκ0 : 0 ≤ shiftConst β * Real.exp (-(β * |s|)) := by
    have := shiftConst_pos β; positivity
  calc shiftConst β * Real.exp (-(β * |s|)) * (Interp.sosInterp β t).re
      ≤ shiftConst β * Real.exp (-(β * |s|)) *
          (Real.exp (seriesConst β) * Real.exp (-(β * |t|))) :=
        mul_le_mul_of_nonneg_left hup hκ0
    _ = Real.exp (-(β ^ (2 / 3 : ℝ))) * Real.exp (-seriesConst β) *
          (Real.exp (-(β * |t|)) * Real.exp (-(β * |s|))) := by
        unfold shiftConst
        have hE : Real.exp (-seriesConst β) * Real.exp (seriesConst β) = 1 := by
          rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
        linear_combination (Real.exp (-(β ^ (2 / 3 : ℝ))) * Real.exp (-seriesConst β) *
          Real.exp (-(β * |s|)) * Real.exp (-(β * |t|))) * hE
    _ ≤ Real.exp (-(β ^ (2 / 3 : ℝ))) * Real.exp (-seriesConst β) *
          Real.exp (-(β * |t + s|)) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
    _ ≤ _ := hlow

/-! ## Raising one height -/

/-- The unit field at the site `u`. -/
abbrev unitAt (u : Site L) : Site L → ℝ := Pi.single u 1

theorem pinnedField_unitAt_mem (u : Site L) (k : RotatorDualFace L) :
    0 ≤ pinnedField (unitAt u) k ∧ pinnedField (unitAt u) k ≤ 1 := by
  cases k with
  | none => simp [pinnedField]
  | some x =>
    simp only [pinnedField, Option.elim, unitAt, Pi.single_apply]
    split_ifs <;> norm_num

theorem abs_pinnedGrad_unitAt_le (u : Site L) (e : SquareZeroBond L) :
    |pinnedGrad L (unitAt u) e| ≤ 1 := by
  rw [pinnedGrad_apply]
  simp only [Multigraph.grad]
  have h1 := pinnedField_unitAt_mem u ((squareZero L).src e)
  have h2 := pinnedField_unitAt_mem u ((squareZero L).tgt e)
  rw [abs_le]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

theorem incident_of_pinnedGrad_unitAt_ne_zero (u : Site L) (e : SquareZeroBond L)
    (h : pinnedGrad L (unitAt u) e ≠ 0) :
    (squareZero L).src e = some u ∨ (squareZero L).tgt e = some u := by
  by_contra hne
  push Not at hne
  apply h
  have hz : ∀ k : RotatorDualFace L, k ≠ some u → pinnedField (unitAt u) k = 0 := by
    intro k hk
    cases k with
    | none => simp [pinnedField]
    | some x =>
      simp only [pinnedField, Option.elim, unitAt]
      exact Pi.single_eq_of_ne (fun h' => hk (by rw [h'])) 1
  rw [pinnedGrad_apply]
  simp only [Multigraph.grad, hz _ hne.1, hz _ hne.2, sub_self]

/-- **Raising one height**: `(κ e^{−β|k|})⁴ ρ(φ) ≤ ρ(φ + k 1_u)`. -/
theorem boxWeight_shift_ge {β : ℝ} (hβ : 0 ≤ β) (φ : Site L → ℝ) (u : Site L) (k : ℝ) :
    (shiftConst β * Real.exp (-(β * |k|))) ^ 4 * boxWeight L β φ ≤
      boxWeight L β (φ + k • unitAt u) := by
  classical
  set q := shiftConst β * Real.exp (-(β * |k|)) with hq
  have hq0 : 0 < q := mul_pos (shiftConst_pos β) (Real.exp_pos _)
  have hq1 : q ≤ 1 := by
    rw [hq]
    calc shiftConst β * Real.exp (-(β * |k|)) ≤ 1 * 1 :=
          mul_le_mul (shiftConst_le_one hβ) (Real.exp_le_one_iff.mpr (by
            have := abs_nonneg k; nlinarith)) (Real.exp_pos _).le zero_le_one
      _ = 1 := one_mul 1
  set d : SquareZeroBond L → ℝ := fun e => pinnedGrad L (unitAt u) e with hd
  set f : SquareZeroBond L → ℝ := fun e => if d e = 0 then 1 else q with hf
  have hgrad : ∀ e, pinnedGrad L (φ + k • unitAt u) e = pinnedGrad L φ e + k * d e := fun e => by
    rw [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hedge : ∀ e, f e * (Interp.sosInterp β (pinnedGrad L φ e : ℂ)).re ≤
      (Interp.sosInterp β (pinnedGrad L (φ + k • unitAt u) e : ℂ)).re := by
    intro e
    rw [hgrad]
    by_cases h0 : d e = 0
    · simp only [hf, h0, ↓reduceIte, one_mul, mul_zero, add_zero]
      exact le_rfl
    · simp only [hf, h0, ↓reduceIte]
      have hs := sosInterp_re_shift_ge hβ (pinnedGrad L φ e) (k * d e)
      have hkd : |k * d e| ≤ |k| := by
        rw [abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) (abs_pinnedGrad_unitAt_le u e)
      have hI := (Interp.sosInterp_ofReal_im_eq_zero_and_re_pos hβ (pinnedGrad L φ e)).2
      refine le_trans ?_ hs
      refine mul_le_mul_of_nonneg_right ?_ hI.le
      rw [hq]
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith))
        (shiftConst_pos β).le
  have hprod : (∏ e, f e) * boxWeight L β φ ≤ boxWeight L β (φ + k • unitAt u) := by
    unfold boxWeight
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod₀ (fun e _ => mul_nonneg ?_
      (Interp.sosInterp_ofReal_im_eq_zero_and_re_pos hβ _).2.le) fun e _ => hedge e
    simp only [hf]
    split_ifs
    · exact zero_le_one
    · exact hq0.le
  have hcount : ∏ e, f e = q ^ (Finset.univ.filter fun e => d e ≠ 0).card := by
    rw [hf, Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]
  have hcard : (Finset.univ.filter fun e => d e ≠ 0).card ≤ 4 := by
    refine le_trans (Finset.card_le_card fun e he => ?_) (card_incident_le_four u)
    rw [Finset.mem_filter] at he ⊢
    exact ⟨Finset.mem_univ _, incident_of_pinnedGrad_unitAt_ne_zero u e he.2⟩
  have hpow : q ^ 4 ≤ ∏ e, f e := by
    rw [hcount]
    exact pow_le_pow_of_le_one hq0.le hq1 hcard
  exact le_trans (mul_le_mul_of_nonneg_right hpow (boxWeight_pos hβ φ).le) hprod

theorem heightField_add_single (A : Finset (Site L)) (n : {x // x ∈ A} → ℤ) {u : Site L}
    (hu : u ∈ A) (k : ℤ) (y : {x // x ∉ A} → ℝ) :
    heightField A (n + k • Pi.single ⟨u, hu⟩ 1) y = heightField A n y + (k : ℝ) • unitAt u := by
  funext x
  simp only [heightField, mergePi, Pi.add_apply, Pi.smul_apply, smul_eq_mul, unitAt]
  by_cases hx : x ∈ A
  · simp only [hx, ↓reduceDIte, Pi.single_apply, Subtype.mk.injEq]
    split_ifs <;> push_cast <;> ring
  · have hxu : x ≠ u := fun h => hx (h ▸ hu)
    simp [hx, hxu]

/-- **Raising one height in the marginal weights.** -/
theorem literalWeight_shift_ge (hL : 1 < L) {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1)
    (A : Finset (Site L)) {u : Site L} (hu : u ∈ A) (n : {x // x ∈ A} → ℤ) (k : ℤ) :
    (shiftConst β * Real.exp (-(β * |(k : ℝ)|))) ^ 4 * literalWeight L β A n ≤
      literalWeight L β A (n + k • Pi.single ⟨u, hu⟩ 1) := by
  unfold literalWeight
  rw [← integral_const_mul]
  refine integral_mono ((integrable_boxWeight_slice hL hβ hβ1 A _).const_mul _)
    (integrable_boxWeight_slice hL hβ hβ1 A _) fun y => ?_
  simp only
  rw [heightField_add_single A n hu k y]
  exact boxWeight_shift_ge hβ.le _ u _

/-! ## The extended moment: formula, evenness, divergence -/

/-- **The extended moment as a series**, for every `ε`. -/
theorem literalMomentExt_eq_tsum {β : ℝ} (hβ : 0 ≤ β) {A : Finset (Site L)} {u v : Site L}
    (hu : u ∈ A) (hv : v ∈ A) (ε : ℝ) :
    literalMomentExt L β A u v ε = (literalPartition L β A)⁻¹ *
      ∑' n, ∫⁻ y, ENNReal.ofReal (boxWeight L β (heightField A n y)) *
        ENNReal.ofReal (Real.exp (ε * ((n ⟨u, hu⟩ : ℝ) - n ⟨v, hv⟩))) := by
  have hmeas : Measurable fun φ : Site L → ℝ => ENNReal.ofReal (Real.exp (ε * (φ u - φ v))) :=
    ENNReal.measurable_ofReal.comp (Real.continuous_exp.comp (continuous_const.mul
      ((continuous_apply u).sub (continuous_apply v)))).measurable
  unfold literalMomentExt
  rw [lintegral_literalState hβ A hmeas]
  congr 1
  refine tsum_congr fun n => ?_
  simp_rw [heightField_apply_mem A n _ hu, heightField_apply_mem A n _ hv]

/-- **The extended moment is even in `ε`.** -/
theorem literalMomentExt_neg {β : ℝ} (hβ : 0 ≤ β) {A : Finset (Site L)} {u v : Site L}
    (hu : u ∈ A) (hv : v ∈ A) (ε : ℝ) :
    literalMomentExt L β A u v (-ε) = literalMomentExt L β A u v ε := by
  rw [literalMomentExt_eq_tsum hβ hu hv, literalMomentExt_eq_tsum hβ hu hv]
  congr 1
  rw [← (Equiv.neg ({x // x ∈ A} → ℤ)).tsum_eq]
  refine tsum_congr fun n => ?_
  have hW : ∀ y, boxWeight L β (heightField A (-n) y) = boxWeight L β (heightField A n (-y)) :=
    fun y => by
      rw [show heightField A (-n) y = -heightField A n (-y) by
        rw [← heightField_neg, neg_neg], boxWeight_neg hβ]
  simp only [Equiv.neg_apply, Pi.neg_apply, Int.cast_neg]
  simp_rw [hW]
  have hexp : Real.exp (-ε * (-(n ⟨u, hu⟩ : ℝ) - -(n ⟨v, hv⟩ : ℝ))) =
      Real.exp (ε * ((n ⟨u, hu⟩ : ℝ) - n ⟨v, hv⟩)) := by ring_nf
  rw [hexp]
  exact Generic.measurePreserving_neg_pi.lintegral_comp_emb
    (Homeomorph.neg ({x // x ∉ A} → ℝ)).measurableEmbedding (fun y => ENNReal.ofReal (boxWeight L β (heightField A n y)) *
    ENNReal.ofReal (Real.exp (ε * ((n ⟨u, hu⟩ : ℝ) - n ⟨v, hv⟩))))

/-- A summand of the moment series: `∫ ρ(n ⊕ y) e^{c} dy = W(n) e^{c}`. -/
theorem lintegral_boxWeight_mul_eq (hL : 1 < L) {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1)
    (A : Finset (Site L)) (n : {x // x ∈ A} → ℤ) (c : ℝ) :
    ∫⁻ y, ENNReal.ofReal (boxWeight L β (heightField A n y)) * ENNReal.ofReal c =
      ENNReal.ofReal (literalWeight L β A n) * ENNReal.ofReal c := by
  have hmeas : Measurable fun y => ENNReal.ofReal (boxWeight L β (heightField A n y)) :=
    ENNReal.measurable_ofReal.comp
      ((continuous_boxWeight hβ.le).measurable.comp (measurable_heightField A n))
  rw [lintegral_mul_const _ hmeas]
  congr 1
  unfold literalWeight
  exact (ofReal_integral_eq_lintegral_ofReal (integrable_boxWeight_slice hL hβ hβ1 A _)
    (Filter.Eventually.of_forall fun y => (boxWeight_pos hβ.le _).le)).symm

/-- **Divergence of the moment**: for `u ≠ v` in `A` and `|ε| ≥ 4β`,
`⟨e^{ε[φ(u)−φ(v)]}⟩ = ∞`. Along the ray `n = ±m 1_u` the weights decay at most like
`κ⁴ e^{−4βm} W(0)` (`literalWeight_shift_ge`), against the growth `e^{|ε|m}`. -/
theorem literalMomentExt_eq_top (hL : 1 < L) {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1)
    {A : Finset (Site L)} {u v : Site L} (hu : u ∈ A) (hv : v ∈ A) (huv : u ≠ v) {ε : ℝ}
    (hε : 4 * β ≤ |ε|) : literalMomentExt L β A u v ε = ⊤ := by
  classical
  rw [literalMomentExt_eq_tsum hβ.le hu hv]
  obtain ⟨s, hsε, hs0, habs⟩ : ∃ s : ℤ, (∀ m : ℕ, ε * ((s * m : ℤ) : ℝ) = |ε| * m) ∧ s ≠ 0 ∧
      ∀ m : ℕ, |((s * m : ℤ) : ℝ)| = m := by
    rcases le_or_gt 0 ε with h | h
    · refine ⟨1, fun m => ?_, one_ne_zero, fun m => ?_⟩
      · simp only [Int.cast_natCast, one_mul]
        rw [abs_of_nonneg h]
      · simp only [Int.cast_natCast, one_mul, Nat.abs_cast]
    · refine ⟨-1, fun m => ?_, by norm_num, fun m => ?_⟩
      · simp only [Int.cast_neg, Int.cast_natCast, neg_one_mul]
        rw [abs_of_neg h]
        ring
      · simp only [Int.cast_neg, Int.cast_natCast, neg_one_mul, abs_neg, Nat.abs_cast]
  set g : ℕ → ({x // x ∈ A} → ℤ) := fun m => (s * m : ℤ) • Pi.single ⟨u, hu⟩ 1 with hg
  have hgu : ∀ m, g m ⟨u, hu⟩ = s * m := fun m => by
    simp only [hg, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
  have hne : (⟨v, hv⟩ : {x // x ∈ A}) ≠ ⟨u, hu⟩ := fun h => huv (congrArg Subtype.val h).symm
  have hgv : ∀ m, g m ⟨v, hv⟩ = 0 := fun m => by
    simp only [hg, Pi.smul_apply, Pi.single_eq_of_ne hne, smul_eq_mul, mul_zero]
  have hginj : Function.Injective g := by
    intro m m' h
    have h' := congrFun h ⟨u, hu⟩
    rw [hgu, hgu] at h'
    exact_mod_cast mul_left_cancel₀ hs0 h'
  set c := ENNReal.ofReal (shiftConst β ^ 4 * literalWeight L β A 0) with hc
  have hc0 : c ≠ 0 := (ENNReal.ofReal_pos.mpr
    (mul_pos (pow_pos (shiftConst_pos β) 4) (literalWeight_pos hL hβ hβ1 A 0))).ne'
  set F : ({x // x ∈ A} → ℤ) → ENNReal := fun n => ∫⁻ y,
    ENNReal.ofReal (boxWeight L β (heightField A n y)) *
      ENNReal.ofReal (Real.exp (ε * ((n ⟨u, hu⟩ : ℝ) - n ⟨v, hv⟩))) with hF
  have hterm : ∀ m : ℕ, c ≤ F (g m) := by
    intro m
    rw [hF]
    dsimp only
    rw [lintegral_boxWeight_mul_eq hL hβ hβ1 A, hgu, hgv, Int.cast_zero, sub_zero, hsε,
      ← ENNReal.ofReal_mul (literalWeight_pos hL hβ hβ1 A _).le]
    refine ENNReal.ofReal_le_ofReal ?_
    have hW := literalWeight_shift_ge hL hβ hβ1 A hu 0 (s * m)
    rw [zero_add, habs] at hW
    have hexp : (shiftConst β * Real.exp (-(β * m))) ^ 4 =
        shiftConst β ^ 4 * Real.exp (-(4 * β * m)) := by
      rw [mul_pow, ← Real.exp_nat_mul]
      congr 2
      push_cast
      ring
    rw [hexp] at hW
    have he : Real.exp (-(4 * β * m)) * Real.exp (4 * β * m) = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    have h1 : Real.exp (4 * β * m) ≤ Real.exp (|ε| * m) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hε (Nat.cast_nonneg m))
    calc shiftConst β ^ 4 * literalWeight L β A 0
        = shiftConst β ^ 4 * Real.exp (-(4 * β * m)) * literalWeight L β A 0 *
            Real.exp (4 * β * m) := by
          linear_combination (-(shiftConst β ^ 4 * literalWeight L β A 0)) * he
      _ ≤ literalWeight L β A (g m) * Real.exp (4 * β * m) :=
          mul_le_mul_of_nonneg_right hW (Real.exp_pos _).le
      _ ≤ literalWeight L β A (g m) * Real.exp (|ε| * m) :=
          mul_le_mul_of_nonneg_left h1 (literalWeight_pos hL hβ hβ1 A _).le
  have hle : ∑' _ : ℕ, c ≤ ∑' n, F n :=
    (ENNReal.tsum_le_tsum hterm).trans (ENNReal.tsum_comp_le_tsum_of_injective hginj F)
  rw [ENNReal.tsum_const_eq_top_of_ne_zero hc0, top_le_iff] at hle
  rw [hle, ENNReal.mul_top (ENNReal.inv_ne_zero.mpr (by
    rw [literalPartition_eq hL hβ hβ1 A]; exact ENNReal.ofReal_ne_top))]

end FroehlichSpencer.BKT.SOS.Literal

end
