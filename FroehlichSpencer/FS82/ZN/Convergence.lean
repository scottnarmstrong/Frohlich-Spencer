/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.ZN.Model
public import FroehlichSpencer.FS82.ZN.Disorder
public import Mathlib.MeasureTheory.Integral.PeakFunction
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Measure.FiniteMeasurePi
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.UniformOn
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Finite-volume pinning limits

The exponential pinning law on each compact circle link concentrates equally at its `N` roots.
This module proves the one-link limit by reducing a period to `N` translated cells and applies
the compact peak-function theorem on one cell.
-/

public section

namespace FroehlichSpencer.FS82.ZN

noncomputable section

open Set Filter MeasureTheory Metric intervalIntegral
open FroehlichSpencer.FS82.Cubical FroehlichSpencer.FS82.Wilson
open Fintype
open scoped Topology NNReal BoundedContinuousFunction

local instance : Fact (0 < (1 : ℝ)) := ⟨one_pos⟩
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance instIsAddHaarMeasureUnitAddCircleVolume_froehlichSpencer_2 : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

private theorem lintegral_finProd {n : ℕ} {α : Fin n → Type*}
    [∀ i, MeasurableSpace (α i)] (μ : (i : Fin n) → Measure (α i))
    [∀ i, SigmaFinite (μ i)] (f : ∀ i : Fin n, α i → ENNReal)
    (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : (i : Fin n) → α i, ∏ i, f i (x i) ∂Measure.pi μ =
      ∏ i, ∫⁻ y, f i y ∂μ i := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hp := (measurePreserving_piFinSuccAbove μ (0 : Fin (n + 1))).symm
      let e := (MeasurableEquiv.piFinSuccAbove α 0).symm
      rw [← hp.lintegral_comp_emb e.measurableEmbedding]
      change (∫⁻ x : α 0 × ((i : Fin n) → α (Fin.succAbove 0 i)),
        ∏ i, f i (Fin.insertNth 0 x.1 x.2 i)
          ∂(μ 0).prod (Measure.pi fun i => μ (Fin.succAbove 0 i))) = _
      have hfactor (x : α 0 × ((i : Fin n) → α (Fin.succAbove 0 i))) :
          (∏ i : Fin (n + 1), f i (Fin.insertNth 0 x.1 x.2 i)) =
            f 0 x.1 * ∏ i : Fin n,
              f (Fin.succAbove 0 i) (x.2 i) := by
        rw [Fin.prod_univ_succ]
        rw [Fin.insertNth_apply_same]
        congr 1
      calc
        _ = ∫⁻ x : α 0 × ((i : Fin n) → α (Fin.succAbove 0 i)),
            f 0 x.1 * ∏ i : Fin n, f (Fin.succAbove 0 i) (x.2 i)
              ∂(μ 0).prod (Measure.pi fun i => μ (Fin.succAbove 0 i)) := by
                apply lintegral_congr
                intro x
                exact hfactor x
        _ = ∫⁻ x : α 0, ∫⁻ y : (i : Fin n) → α (Fin.succAbove 0 i),
            f 0 x * ∏ i, f (Fin.succAbove 0 i) (y i)
              ∂Measure.pi (fun i => μ (Fin.succAbove 0 i)) ∂μ 0 := by
                rw [lintegral_prod _ (by fun_prop)]
        _ = ∫⁻ x : α 0, f 0 x *
            (∏ i : Fin n,
              ∫⁻ y, f (Fin.succAbove 0 i) y ∂μ (Fin.succAbove 0 i)) ∂μ 0 := by
              apply lintegral_congr_ae
              filter_upwards [] with x
              have hmeas : Measurable (fun y : (i : Fin n) → α (Fin.succAbove 0 i) =>
                  ∏ i, f (Fin.succAbove 0 i) (y i)) := by fun_prop
              rw [lintegral_const_mul'' _ hmeas.aemeasurable,
                ih (fun i => μ (Fin.succAbove 0 i))
                  (fun i => f (Fin.succAbove 0 i)) (fun i => hf (Fin.succAbove 0 i))]
        _ = (∫⁻ x, f 0 x ∂μ 0) *
            ∏ i : Fin n,
              ∫⁻ y, f (Fin.succAbove 0 i) y ∂μ (Fin.succAbove 0 i) :=
              lintegral_mul_const'' _ (hf 0).aemeasurable
        _ = ∏ i : Fin (n + 1), ∫⁻ y, f i y ∂μ i := by
              rw [Fin.prod_univ_succ]
              congr 1

private theorem lintegral_fintype_prod {ι : Type*} [Fintype ι]
    {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
    (μ : (i : ι) → Measure (α i)) [∀ i, SigmaFinite (μ i)]
    (f : ∀ i, α i → ENNReal) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : (i : ι) → α i, ∏ i, f i (x i) ∂Measure.pi μ =
      ∏ i, ∫⁻ y, f i y ∂μ i := by
  let e := (Fintype.equivFin ι).symm
  rw [← (measurePreserving_piCongrLeft μ e).lintegral_comp_emb
    (MeasurableEquiv.measurableEmbedding _)]
  simp_rw [← e.prod_comp, MeasurableEquiv.coe_piCongrLeft,
    Equiv.piCongrLeft_apply_apply]
  exact lintegral_finProd (fun i => μ (e i)) (fun i => f (e i))
    (fun i => hf (e i))

private theorem measure_pi_withDensity {ι : Type*} [Fintype ι]
    {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
    (μ : (i : ι) → Measure (α i)) [∀ i, SigmaFinite (μ i)]
    (f : ∀ i : ι, α i → ENNReal) (hf : ∀ i, Measurable (f i))
    [∀ i, SigmaFinite ((μ i).withDensity (f i))] :
    Measure.pi (fun i => (μ i).withDensity (f i)) =
      (Measure.pi μ).withDensity (fun x => ∏ i, f i (x i)) := by
  classical
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs),
    ← lintegral_indicator (MeasurableSet.univ_pi hs)]
  have hind : (Set.pi Set.univ s).indicator (fun x => ∏ i, f i (x i)) =
      fun x => ∏ i, (s i).indicator (f i) (x i) := by
    funext x
    by_cases hx : ∀ i, x i ∈ s i
    · simp [Set.indicator, Set.mem_pi, hx]
    · obtain ⟨i, hi⟩ := not_forall.mp hx
      have hzero : ∏ i, (s i).indicator (f i) (x i) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ i) (by simp [Set.indicator, hi])
      simpa [Set.indicator, Set.mem_pi, hx] using hzero.symm
  rw [hind, lintegral_fintype_prod]
  · congr 1
    funext i
    rw [lintegral_indicator (hs i), withDensity_apply (f i) (hs i)]
  · intro i
    exact (hf i).indicator (hs i)

private theorem measure_pi_withDensity_nnreal {ι : Type*} [Fintype ι]
    {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
    (μ : (i : ι) → Measure (α i)) [∀ i, SigmaFinite (μ i)]
    (f : ∀ i : ι, α i → NNReal) (hf : ∀ i, Measurable (f i))
    [∀ i, SigmaFinite ((μ i).withDensity (fun x => (f i x : ENNReal)))] :
    Measure.pi (fun i => (μ i).withDensity (fun x => (f i x : ENNReal))) =
      (Measure.pi μ).withDensity
        (fun x => ((∏ i, f i (x i) : NNReal) : ENNReal)) := by
  have h := measure_pi_withDensity μ (fun i x => (f i x : ENNReal))
    (fun i => measurable_coe_nnreal_ennreal.comp (hf i))
  rw [h]
  congr 1
  funext x
  simp

def laplaceCell : Set ℝ := Icc (-(1/2 : ℝ)) (1/2)
def laplacePhase (x : ℝ) : ℝ := Real.cos (2 * Real.pi * x)
def laplaceKernel (h : NNReal) (x : ℝ) : ℝ := Real.exp ((h:ℝ) * (laplacePhase x - 1))
def laplaceMass (h : NNReal) : ℝ := ∫ x in laplaceCell, laplaceKernel h x

theorem continuous_laplacePhase : Continuous laplacePhase := by
  exact Real.continuous_cos.comp (continuous_const.mul continuous_id)

theorem continuous_laplaceKernel (h : NNReal) : Continuous (laplaceKernel h) := by
  exact Real.continuous_exp.comp (continuous_const.mul (continuous_laplacePhase.sub continuous_const))

theorem laplacePhase_le_one (x : ℝ) : laplacePhase x ≤ 1 := by
  exact Real.cos_le_one _

theorem laplacePhase_eq_one_iff_zero {x : ℝ} (hx : x ∈ laplaceCell) :
    laplacePhase x = 1 ↔ x = 0 := by
  constructor
  · intro h
    unfold laplacePhase at h
    rcases (Real.cos_eq_one_iff (2 * Real.pi * x)).mp h with ⟨n, hn⟩
    have hnx : (n : ℝ) = x := by
      nlinarith [Real.pi_pos]
    rcases hx with ⟨hxlo, hxhi⟩
    have hnlo : (-1 : ℝ) < (n : ℝ) := by rw [hnx]; nlinarith [hxlo]
    have hnhi : (n : ℝ) < 1 := by rw [hnx]; nlinarith [hxhi]
    have hnlo' : (-1 : ℤ) < n := by exact_mod_cast hnlo
    have hnhi' : n < 1 := by exact_mod_cast hnhi
    have : n = 0 := by omega
    rw [← hnx, this]
    norm_num
  · rintro rfl
    simp [laplacePhase]

theorem laplaceKernel_integrableOn (h : NNReal) : IntegrableOn (laplaceKernel h) laplaceCell := by
  exact (continuous_laplaceKernel h).continuousOn.integrableOn_compact isCompact_Icc

theorem laplaceMass_pos (h : NNReal) : 0 < laplaceMass h := by
  unfold laplaceMass
  have hn : 0 ≤ᵐ[volume.restrict laplaceCell] laplaceKernel h :=
    ae_of_all _ fun x => (Real.exp_pos _).le
  have hi := laplaceKernel_integrableOn h
  rw [setIntegral_pos_iff_support_of_nonneg_ae hn hi]
  have hsupport : Function.support (laplaceKernel h) = univ :=
    Function.support_eq_univ (fun x => by simp [laplaceKernel])
  rw [hsupport, univ_inter]
  change 0 < volume (Icc (-(1/2 : ℝ)) (1/2 : ℝ))
  rw [Real.volume_Icc]
  exact ENNReal.ofReal_pos.mpr (by norm_num)

def laplacePeak (h : NNReal) (x : ℝ) : ℝ := laplaceKernel h x / laplaceMass h

theorem laplacePeak_nonneg (h : NNReal) (x : ℝ) : 0 ≤ laplacePeak h x :=
  div_nonneg (Real.exp_pos _).le (laplaceMass_pos h).le

theorem laplacePeak_integral (h : NNReal) :
    ∫ x in laplaceCell, laplacePeak h x = 1 := by
  unfold laplacePeak laplaceMass
  rw [MeasureTheory.integral_div]
  exact div_self (laplaceMass_pos h).ne'

theorem laplacePeak_tendsto_uniformlyOn (U : Set ℝ) (hU : IsOpen U) (h0 : (0:ℝ) ∈ U) :
    TendstoUniformlyOn laplacePeak 0 atTop (laplaceCell \ U) := by
  by_cases he : laplaceCell \ U = ∅
  · simp [TendstoUniformlyOn, he]
  have hne : (laplaceCell \ U).Nonempty := Set.nonempty_iff_ne_empty.mpr he
  obtain ⟨x, hx, hxmax⟩ := (isCompact_Icc.diff hU).exists_isMaxOn hne
      (continuous_laplacePhase.continuousOn.mono sdiff_subset)
  have hstrict : laplacePhase x < 1 := by
    have hxne : x ≠ 0 := fun hx0 => hx.2 (hx0 ▸ h0)
    have hne1 : laplacePhase x ≠ 1 := fun heq => hxne ((laplacePhase_eq_one_iff_zero hx.1).mp heq)
    exact lt_of_le_of_ne (laplacePhase_le_one x) hne1
  obtain ⟨t', htt', ht'1⟩ : ∃ t', laplacePhase x < t' ∧ t' < 1 := exists_between hstrict
  have h0s : (0:ℝ) ∈ laplaceCell := by simp [laplaceCell]
  obtain ⟨V, hVopen, hV0, hV⟩ : ∃ V : Set ℝ, IsOpen V ∧ (0:ℝ) ∈ V ∧
      V ∩ laplaceCell ⊆ laplacePhase ⁻¹' Ioi t' :=
    _root_.continuousOn_iff.1 continuous_laplacePhase.continuousOn 0 h0s (Ioi t')
      isOpen_Ioi (by simpa [laplacePhase] using ht'1)
  have hsnhds : laplaceCell ∈ 𝓝 (0:ℝ) := by
    apply mem_of_superset (Metric.ball_mem_nhds 0 (by norm_num : (0:ℝ) < 1/2))
    intro y hy
    have hyabs : |y| < 1/2 := by simpa [Metric.mem_ball, Real.dist_eq] using hy
    change -(1/2:ℝ) ≤ y ∧ y ≤ 1/2
    exact ⟨(abs_lt.mp hyabs).1.le, (abs_lt.mp hyabs).2.le⟩
  have hVmeasure : 0 < volume (V ∩ laplaceCell) :=
    MeasureTheory.Measure.measure_pos_of_mem_nhds volume
      (Filter.inter_mem (hVopen.mem_nhds hV0) hsnhds)
  have hfinite : volume (V ∩ laplaceCell) < ⊤ := by
    calc
      volume (V ∩ laplaceCell) ≤ volume laplaceCell := measure_mono inter_subset_right
      _ < ⊤ := isCompact_Icc.measure_lt_top
  have hm : 0 < volume.real (V ∩ laplaceCell) :=
    ENNReal.toReal_pos hVmeasure.ne' (ne_of_lt hfinite)
  have hVmeas : MeasurableSet (V ∩ laplaceCell) :=
    hVopen.measurableSet.inter isClosed_Icc.measurableSet
  have hlower (h : NNReal) :
      volume.real (V ∩ laplaceCell) * Real.exp ((↑h:ℝ) * (t' - 1)) ≤ laplaceMass h := by
    have hconstInt : IntegrableOn (fun _ : ℝ => Real.exp ((↑h:ℝ) * (t' - 1)))
        (V ∩ laplaceCell) volume := integrableOn_const (ne_of_lt hfinite)
    have hker_nonneg : 0 ≤ᵐ[volume.restrict laplaceCell] laplaceKernel h :=
      ae_of_all _ fun _ => (Real.exp_pos _).le
    have hker_int := laplaceKernel_integrableOn h
    have hsubint : IntegrableOn (laplaceKernel h) (V ∩ laplaceCell) volume :=
      hker_int.mono_set (s := V ∩ laplaceCell) inter_subset_right
    have hconst_le :
        ∫ y in V ∩ laplaceCell, Real.exp ((↑h:ℝ) * (t' - 1)) ∂volume ≤ laplaceMass h := by
      calc
        _ ≤ ∫ y in V ∩ laplaceCell, laplaceKernel h y ∂volume := by
          apply setIntegral_mono_on hconstInt hsubint hVmeas
          intro y hy
          apply Real.exp_le_exp.mpr
          have hphase : t' < laplacePhase y := hV hy
          have hh : 0 ≤ (h:ℝ) := h.2
          have hmul : 0 ≤ (h:ℝ) * (laplacePhase y - t') :=
            mul_nonneg hh (sub_nonneg.mpr hphase.le)
          nlinarith [hmul]
        _ ≤ ∫ y in laplaceCell, laplaceKernel h y ∂volume := by
          apply setIntegral_mono_set hker_int hker_nonneg
          exact Eventually.of_forall inter_subset_right
    calc
      _ = ∫ y in V ∩ laplaceCell, Real.exp ((↑h:ℝ) * (t' - 1)) ∂volume := by
        rw [setIntegral_const, smul_eq_mul]
      _ ≤ laplaceMass h := hconst_le
  have htail : Tendsto (fun h : NNReal => Real.exp ((↑h:ℝ) * (laplacePhase x - t')))
      atTop (𝓝 0) := by
    have harg : Tendsto (fun h : NNReal => (laplacePhase x - t') * (↑h:ℝ)) atTop atBot := by
      exact (tendsto_const_mul_atBot_of_neg (r := laplacePhase x - t') (by linarith [htt']) ).mpr
        (NNReal.tendsto_coe_atTop.mpr tendsto_id)
    convert Real.tendsto_exp_atBot.comp harg using 1
    ext h
    simp only [Function.comp_apply]
    rw [mul_comm]
  refine tendstoUniformlyOn_iff.2 ?_
  intro ε hε
  filter_upwards [(tendsto_order.1 htail).2 (ε * volume.real (V ∩ laplaceCell))
      (mul_pos hε hm)] with h hbound
  intro y hy
  have hyc : laplacePhase y ≤ laplacePhase x := hxmax hy
  have hyK : laplaceKernel h y ≤ Real.exp ((↑h:ℝ) * (laplacePhase x - 1)) := by
    unfold laplaceKernel
    apply Real.exp_le_exp.mpr
    have hh : 0 ≤ (h:ℝ) := h.2
    nlinarith [hh, hyc]
  have hratio : laplacePeak h y ≤
      (volume.real (V ∩ laplaceCell))⁻¹ *
        Real.exp ((↑h:ℝ) * (laplacePhase x - t')) := by
    unfold laplacePeak laplaceMass
    calc
      _ ≤ Real.exp ((↑h:ℝ) * (laplacePhase x - 1)) /
          (volume.real (V ∩ laplaceCell) * Real.exp ((↑h:ℝ) * (t' - 1))) :=
        div_le_div₀ (Real.exp_nonneg _) hyK (mul_pos hm (Real.exp_pos _)) (hlower h)
      _ = (volume.real (V ∩ laplaceCell))⁻¹ *
          Real.exp ((↑h:ℝ) * (laplacePhase x - t')) := by
        rw [div_eq_mul_inv, mul_inv_rev]
        have he : (↑h:ℝ) * (laplacePhase x - t') =
            (↑h:ℝ) * (laplacePhase x - 1) - (↑h:ℝ) * (t' - 1) := by ring
        rw [he, Real.exp_sub]
        field_simp [Real.exp_ne_zero]
  have hquot : (volume.real (V ∩ laplaceCell))⁻¹ *
      Real.exp ((↑h:ℝ) * (laplacePhase x - t')) < ε := by
    have hdiv : Real.exp ((↑h:ℝ) * (laplacePhase x - t')) /
        volume.real (V ∩ laplaceCell) < ε := (div_lt_iff₀ hm).2 hbound
    simpa [div_eq_mul_inv, mul_comm] using hdiv
  simpa [Real.dist_eq, abs_of_nonneg (laplacePeak_nonneg h y)] using
    (lt_of_le_of_lt hratio hquot)

theorem tendsto_laplaceCell_integral {F : ℝ → ℝ} (hF : ContinuousOn F laplaceCell) :
    Tendsto (fun h : NNReal => ∫ x in laplaceCell, laplacePeak h x * F x)
      atTop (𝓝 (F 0)) := by
  have hpeak := tendsto_setIntegral_peak_smul_of_integrableOn_of_tendsto
    (μ := volume) (g := F) (l := atTop) (x₀ := 0) (s := laplaceCell)
    (φ := laplacePeak) (a := F 0)
    isClosed_Icc.measurableSet (t := laplaceCell) isClosed_Icc.measurableSet
    Subset.rfl self_mem_nhdsWithin
    (show volume laplaceCell ≠ ⊤ from ne_of_lt (by
      change volume (Icc (-(1 / 2 : ℝ)) (1 / 2)) < ⊤
      exact isCompact_Icc.measure_lt_top))
    (Filter.Eventually.of_forall fun h x _ => laplacePeak_nonneg h x)
    (fun U hU h0 => laplacePeak_tendsto_uniformlyOn U hU h0)
    (tendsto_const_nhds.congr' (Filter.Eventually.of_forall fun h =>
      (laplacePeak_integral h).symm))
    (Filter.Eventually.of_forall fun h =>
      (continuous_laplaceKernel h).div_const (laplaceMass h) |>.aestronglyMeasurable)
    (hF.integrableOn_compact isCompact_Icc)
    (hF.continuousWithinAt (by simp [laplaceCell]))
  simpa only [smul_eq_mul] using hpeak

/-- Real-coordinate form of the circle character. -/
theorem circleCosCharacter_real (n : ℕ) (x : ℝ) :
    circleCosCharacter n (x : UnitAddCircle) = Real.cos (2 * Real.pi * (n : ℝ) * x) := by
  unfold circleCosCharacter
  rw [fourier_coe_apply]
  have hz : 2 * (↑Real.pi : ℂ) * Complex.I * (↑(n : ℤ) : ℂ) * (↑x : ℂ) /
      (↑(1 : ℝ) : ℂ) = (↑(2 * Real.pi * (n : ℝ) * x) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [hz, Complex.exp_re]
  simp

theorem circleCosCharacter_on_cell (N : ℕ) (hN : 0 < N) (k : Fin N) (x : ℝ) :
    circleCosCharacter N (((k.val : ℝ) + x) / (N : ℝ) : UnitAddCircle) =
      laplacePhase x := by
  rw [circleCosCharacter_real]
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have harg : 2 * Real.pi * (N : ℝ) * (((k.val : ℝ) + x) / (N : ℝ)) =
      (2 * Real.pi * x) + (k.val : ℝ) * (2 * Real.pi) := by
    field_simp [ne_of_gt hNr]
    ring
  rw [harg, Real.cos_add_nat_mul_two_pi]
  rfl

@[expose] def znCellObservable {N : ℕ} (F : UnitAddCircle → ℝ) (k : Fin N)
    (x : ℝ) : ℝ := F (((k.val : ℝ) + x) / (N : ℝ) : UnitAddCircle)

theorem continuous_znCellObservable {N : ℕ} (F : UnitAddCircle → ℝ)
    (hF : Continuous F) (k : Fin N) : Continuous (znCellObservable F k) := by
  unfold znCellObservable
  exact hF.comp (by fun_prop)

def znCellLeft (N k : ℕ) : ℝ :=
  (k : ℝ) / (N : ℝ) + (-(1 / 2 : ℝ)) / (N : ℝ)

def znCellRight (N k : ℕ) : ℝ :=
  (k : ℝ) / (N : ℝ) + (1 / 2 : ℝ) / (N : ℝ)

theorem znCellRight_eq_left_succ (N k : ℕ) : znCellRight N k = znCellLeft N (k + 1) := by
  simp only [znCellRight, znCellLeft, Nat.cast_add, Nat.cast_one]
  ring

theorem intervalIntegral_cell_eq_setIntegral (f : ℝ → ℝ) :
    (∫ x in (-(1 / 2 : ℝ))..(1 / 2 : ℝ), f x) = ∫ x in laplaceCell, f x := by
  rw [intervalIntegral.integral_of_le (by norm_num), ← integral_Icc_eq_integral_Ioc]
  rfl

def znOneLinkIntegrand (N : ℕ) (h : NNReal) (F : UnitAddCircle → ℝ)
    (z : UnitAddCircle) : ℝ := F z * Real.exp ((h : ℝ) * circleCosCharacter N z)

theorem continuous_znOneLinkIntegrand {N : ℕ} (h : NNReal) (F : UnitAddCircle → ℝ)
    (hF : Continuous F) : Continuous (znOneLinkIntegrand N h F) := by
  exact hF.mul (Real.continuous_exp.comp (continuous_const.mul (continuous_circleCosCharacter N)))


theorem znOneLink_cell_change {N : ℕ} (hN : 0 < N) (h : NNReal)
    (F : UnitAddCircle → ℝ) (k : Fin N) :
    (∫ x in (-(1 / 2 : ℝ))..(1 / 2 : ℝ),
      znCellObservable F k x * Real.exp ((h : ℝ) * laplacePhase x)) =
      (N : ℝ) * ∫ x in znCellLeft N k.val..znCellRight N k.val,
        znOneLinkIntegrand N h F (x : UnitAddCircle) := by
  have hchange := intervalIntegral.integral_comp_add_div
    (f := fun y : ℝ => znOneLinkIntegrand N h F (y : UnitAddCircle))
    (a := -(1 / 2 : ℝ)) (b := (1 / 2 : ℝ)) (c := (N : ℝ))
    (d := (k.val : ℝ) / (N : ℝ)) (by exact_mod_cast (Nat.ne_of_gt hN))
  have hpoint (x : ℝ) :
      znOneLinkIntegrand N h F
          (((k.val : ℝ) / (N : ℝ) + x / (N : ℝ)) : UnitAddCircle) =
        znCellObservable F k x * Real.exp ((h : ℝ) * laplacePhase x) := by
    unfold znOneLinkIntegrand znCellObservable
    have harg : (k.val : ℝ) / (N : ℝ) + x / (N : ℝ) =
        ((k.val : ℝ) + x) / (N : ℝ) := by ring
    rw [harg, circleCosCharacter_on_cell N hN k x]
  calc
    _ = ∫ x in (-(1 / 2 : ℝ))..(1 / 2 : ℝ),
          znOneLinkIntegrand N h F
            (((k.val : ℝ) / (N : ℝ) + x / (N : ℝ)) : UnitAddCircle) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [] with x hx
      exact (hpoint x).symm
    _ = (N : ℝ) * ∫ x in znCellLeft N k.val..znCellRight N k.val,
          znOneLinkIntegrand N h F (x : UnitAddCircle) := by
      simpa [znCellLeft, znCellRight, smul_eq_mul] using hchange

def znNatFin (N : ℕ) (hN : 0 < N) (j : ℕ) : Fin N :=
  ⟨j % N, Nat.mod_lt _ hN⟩

theorem znOneLink_period_decomp {N : ℕ} (hN : 0 < N) (h : NNReal)
    (F : UnitAddCircle → ℝ) (hF : Continuous F) :
    (∫ z : UnitAddCircle, znOneLinkIntegrand N h F z) =
      ∑ j ∈ Finset.range N, (N : ℝ)⁻¹ *
        ∫ x in laplaceCell,
          znCellObservable F (znNatFin N hN j) x * Real.exp ((h : ℝ) * laplacePhase x) := by
  let g : ℝ → ℝ := fun x => znOneLinkIntegrand N h F (x : UnitAddCircle)
  let a : ℕ → ℝ := fun j => znCellLeft N j
  have hper : ∫ x in a 0..a N, g x = ∫ z : UnitAddCircle, znOneLinkIntegrand N h F z := by
    have ha0 : a 0 = -(1 / 2 : ℝ) / (N : ℝ) := by
      simp [a, znCellLeft]
    have haN : a N = (-(1 / 2 : ℝ) / (N : ℝ)) + 1 := by
      simp [a, znCellLeft]
      field_simp [ne_of_gt (show (0:ℝ) < N by exact_mod_cast hN)]
      ring
    rw [ha0, haN]
    calc
      _ = ∫ z : UnitAddCircle, znOneLinkIntegrand N h F z ∂(AddCircle.measureSpace (T := (1 : ℝ))).volume :=
        UnitAddCircle.intervalIntegral_preimage
          (-(1 / 2 : ℝ) / (N : ℝ)) (znOneLinkIntegrand N h F)
      _ = ∫ z : UnitAddCircle, znOneLinkIntegrand N h F z := by
        have hvol : (AddCircle.measureSpace (T := (1 : ℝ))).volume =
            (volume : Measure UnitAddCircle) := by
          calc
            _ = AddCircle.haarAddCircle := by
              simpa using (AddCircle.volume_eq_smul_haarAddCircle (T := (1 : ℝ)))
            _ = _ := rfl
        rw [hvol]
  have hsum :
      (∑ j ∈ Finset.range N, ∫ x in a j..a (j + 1), g x) = ∫ x in a 0..a N, g x := by
    apply intervalIntegral.sum_integral_adjacent_intervals
    intro j hj
    exact (continuous_znOneLinkIntegrand h F hF).comp
      (AddCircle.continuous_mk' (1 : ℝ)) |>.intervalIntegrable _ _
  calc
    _ = ∫ x in a 0..a N, g x := hper.symm
    _ = ∑ j ∈ Finset.range N, ∫ x in a j..a (j + 1), g x := hsum.symm
    _ = ∑ j ∈ Finset.range N, (N : ℝ)⁻¹ *
          ∫ x in laplaceCell,
            znCellObservable F (znNatFin N hN j) x * Real.exp ((h : ℝ) * laplacePhase x) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjN : j < N := Finset.mem_range.mp hj
      let k : Fin N := ⟨j, hjN⟩
      have hcell := znOneLink_cell_change hN h F k
      rw [znCellRight_eq_left_succ] at hcell
      have hcell' :
          (∫ x in laplaceCell,
            znCellObservable F (znNatFin N hN j) x * Real.exp ((h : ℝ) * laplacePhase x)) =
          (N : ℝ) * ∫ x in a j..a (j + 1), g x := by
        have hcell'' := hcell
        rw [intervalIntegral_cell_eq_setIntegral] at hcell''
        simpa [g, a, k, znNatFin, Nat.mod_eq_of_lt hjN] using hcell''
      calc
        _ = (N : ℝ)⁻¹ * ((N : ℝ) * ∫ x in a j..a (j + 1), g x) := by
          field_simp [ne_of_gt (show (0:ℝ) < N by exact_mod_cast hN)]
        _ = _ := by rw [← hcell']

theorem laplaceCell_exp_factor (h : NNReal) (x : ℝ) :
    Real.exp ((h : ℝ) * laplacePhase x) =
      Real.exp (h : ℝ) * laplaceKernel h x := by
  rw [laplaceKernel, ← Real.exp_add]
  congr 1
  ring

theorem znCell_integral_factor {N : ℕ} (h : NNReal) (F : UnitAddCircle → ℝ)
    (k : Fin N) :
    (∫ x in laplaceCell,
      znCellObservable F k x * Real.exp ((h : ℝ) * laplacePhase x)) =
      Real.exp (h : ℝ) *
        ∫ x in laplaceCell, laplaceKernel h x * znCellObservable F k x := by
  calc
    _ = ∫ x in laplaceCell,
          Real.exp (h : ℝ) * (laplaceKernel h x * znCellObservable F k x) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [] with x
      rw [laplaceCell_exp_factor]
      ring
    _ = Real.exp (h : ℝ) *
          ∫ x in laplaceCell, laplaceKernel h x * znCellObservable F k x := by
      rw [MeasureTheory.integral_const_mul]

theorem znCell_peak_integral {N : ℕ} (h : NNReal) (F : UnitAddCircle → ℝ)
    (k : Fin N) :
    (∫ x in laplaceCell, laplacePeak h x * znCellObservable F k x) =
      (laplaceMass h)⁻¹ *
        ∫ x in laplaceCell, laplaceKernel h x * znCellObservable F k x := by
  calc
    _ = ∫ x in laplaceCell,
          (laplaceMass h)⁻¹ * (laplaceKernel h x * znCellObservable F k x) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [] with x
      unfold laplacePeak
      rw [div_eq_mul_inv]
      ring
    _ = (laplaceMass h)⁻¹ *
          ∫ x in laplaceCell, laplaceKernel h x * znCellObservable F k x := by
      rw [MeasureTheory.integral_const_mul]

theorem znCell_ratio_eq_peak {N : ℕ} (h : NNReal) (F : UnitAddCircle → ℝ)
    (k : Fin N) :
    ((∫ x in laplaceCell,
        znCellObservable F k x * Real.exp ((h : ℝ) * laplacePhase x)) /
      (Real.exp (h : ℝ) * laplaceMass h)) =
      ∫ x in laplaceCell, laplacePeak h x * znCellObservable F k x := by
  rw [znCell_integral_factor, znCell_peak_integral]
  field_simp [Real.exp_ne_zero, (laplaceMass_pos h).ne']

theorem znCell_constant_integral (h : NNReal) :
    (∫ x in laplaceCell, Real.exp ((h : ℝ) * laplacePhase x)) =
      Real.exp (h : ℝ) * laplaceMass h := by
  calc
    _ = ∫ x in laplaceCell, Real.exp (h : ℝ) * laplaceKernel h x := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [] with x
      rw [laplaceCell_exp_factor]
    _ = Real.exp (h : ℝ) * laplaceMass h := by
      rw [MeasureTheory.integral_const_mul]
      rfl

theorem pinningNormalizer_eq_cellMass {N : ℕ} (hN : 0 < N) (h : NNReal) :
    pinningNormalizer N h = Real.exp (h : ℝ) * laplaceMass h := by
  have hdecomp := znOneLink_period_decomp hN h (fun _ => (1 : ℝ)) continuous_const
  have hlocal (j : ℕ) :
      ∫ x in laplaceCell,
        znCellObservable (fun _ => (1 : ℝ)) (znNatFin N hN j) x *
          Real.exp ((h : ℝ) * laplacePhase x) = Real.exp (h : ℝ) * laplaceMass h := by
    simpa [znCellObservable] using znCell_constant_integral h
  calc
    pinningNormalizer N h =
        ∑ j ∈ Finset.range N, (N : ℝ)⁻¹ *
          ∫ x in laplaceCell,
            znCellObservable (fun _ => (1 : ℝ)) (znNatFin N hN j) x *
              Real.exp ((h : ℝ) * laplacePhase x) := by
      simpa [pinningNormalizer, znOneLinkIntegrand] using hdecomp
    _ = Real.exp (h : ℝ) * laplaceMass h := by
      simp_rw [hlocal]
      rw [Finset.sum_const, Finset.card_range]
      simp only [nsmul_eq_mul]
      field_simp [ne_of_gt (show (0 : ℝ) < N by exact_mod_cast hN)]

theorem znOneLink_ratio_eq_peak_sum {N : ℕ} (hN : 0 < N) (h : NNReal)
    (F : UnitAddCircle → ℝ) (hF : Continuous F) :
    ((∫ z : UnitAddCircle, znOneLinkIntegrand N h F z) / pinningNormalizer N h) =
      ∑ j ∈ Finset.range N, (N : ℝ)⁻¹ *
        ∫ x in laplaceCell,
          laplacePeak h x * znCellObservable F (znNatFin N hN j) x := by
  have hnum := znOneLink_period_decomp hN h F hF
  rw [hnum, pinningNormalizer_eq_cellMass hN h, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  let k := znNatFin N hN j
  calc
    ((N : ℝ)⁻¹ *
        ∫ x in laplaceCell,
          znCellObservable F k x * Real.exp ((h : ℝ) * laplacePhase x)) /
        (Real.exp (h : ℝ) * laplaceMass h) =
      (N : ℝ)⁻¹ *
        ((∫ x in laplaceCell,
          znCellObservable F k x * Real.exp ((h : ℝ) * laplacePhase x)) /
            (Real.exp (h : ℝ) * laplaceMass h)) := by
      field_simp [Real.exp_ne_zero, (laplaceMass_pos h).ne',
        ne_of_gt (show (0 : ℝ) < N by exact_mod_cast hN)]
    _ = (N : ℝ)⁻¹ *
        ∫ x in laplaceCell, laplacePeak h x * znCellObservable F k x := by
      rw [znCell_ratio_eq_peak]

theorem tendsto_znOneLink_ratio {N : ℕ} (hN : 0 < N)
    (F : UnitAddCircle → ℝ) (hF : Continuous F) :
    Tendsto (fun h : NNReal =>
      (∫ z : UnitAddCircle, znOneLinkIntegrand N h F z) / pinningNormalizer N h)
      atTop (𝓝 ((N : ℝ)⁻¹ * ∑ k : Fin N, F (znRoot N k))) := by
  have hlocal (k : Fin N) :
      Tendsto (fun h : NNReal => ∫ x in laplaceCell,
        laplacePeak h x * znCellObservable F k x) atTop (𝓝 (F (znRoot N k))) := by
    have hpeak := tendsto_laplaceCell_integral
      (F := znCellObservable F k) (continuous_znCellObservable F hF k).continuousOn
    simpa [znCellObservable, znRoot] using hpeak
  have hsum : Tendsto (fun h : NNReal =>
      ∑ j ∈ Finset.range N, (N : ℝ)⁻¹ *
        ∫ x in laplaceCell,
          laplacePeak h x * znCellObservable F (znNatFin N hN j) x)
      atTop (𝓝 (∑ j ∈ Finset.range N, (N : ℝ)⁻¹ *
        F (znRoot N (znNatFin N hN j)))) := by
    apply tendsto_finsetSum
    intro j hj
    exact tendsto_const_nhds.mul (hlocal (znNatFin N hN j))
  have hroots :
      (∑ j ∈ Finset.range N, F (znRoot N (znNatFin N hN j))) =
        ∑ k : Fin N, F (znRoot N k) := by
    let f : ℕ → ℝ := fun j => F (znRoot N (znNatFin N hN j))
    calc
      _ = ∑ k : Fin N, f k.val := (Fin.sum_univ_eq_sum_range f N).symm
      _ = ∑ k : Fin N, F (znRoot N k) := by
        apply Finset.sum_congr rfl
        intro k hk
        simp [f, znNatFin, Nat.mod_eq_of_lt k.isLt, znRoot]
  have hsum' : Tendsto (fun h : NNReal =>
      ∑ j ∈ Finset.range N, (N : ℝ)⁻¹ *
        ∫ x in laplaceCell,
          laplacePeak h x * znCellObservable F (znNatFin N hN j) x)
      atTop (𝓝 ((N : ℝ)⁻¹ * ∑ k : Fin N, F (znRoot N k))) := by
    convert hsum using 1
    congr 1
    rw [← Finset.mul_sum, hroots]
  apply hsum'.congr'
  filter_upwards [] with h
  exact (znOneLink_ratio_eq_peak_sum hN h F hF).symm

@[expose] def znLinkDensityNN (N : ℕ) (h : NNReal) (z : UnitAddCircle) : NNReal :=
  (znPinningFactor N h z).toNNReal

theorem znLinkDensityNN_coe (N : ℕ) (h : NNReal) (z : UnitAddCircle) :
    (znLinkDensityNN N h z : ℝ) = znPinningFactor N h z := by
  exact Real.coe_toNNReal _ (znPinningFactor_pos N h z).le

theorem znLinkFactor_integral_one (N : ℕ) (h : NNReal) :
    (∫ z : UnitAddCircle, znPinningFactor N h z) = 1 := by
  unfold znPinningFactor pinningNormalization
  rw [MeasureTheory.integral_const_mul]
  unfold pinningNormalizer
  exact inv_mul_cancel₀ (pinningNormalizer_pos N h).ne'

theorem znLinkDensity_integrable (N : ℕ) (h : NNReal) :
    Integrable (fun z : UnitAddCircle => (znLinkDensityNN N h z : ℝ)) := by
  have hEq : (fun z : UnitAddCircle => (znLinkDensityNN N h z : ℝ)) =
      znPinningFactor N h := by funext z; exact znLinkDensityNN_coe N h z
  rw [hEq]
  apply MeasureTheory.integrableOn_univ.mp
  exact (continuous_znPinningFactor N h).continuousOn.integrableOn_compact isCompact_univ

@[expose] def znLinkMeasure (N : ℕ) (h : NNReal) : Measure UnitAddCircle :=
  volume.withDensity (fun z => (znLinkDensityNN N h z : ENNReal))

theorem znLinkMeasure_isProbabilityMeasure (N : ℕ) (h : NNReal) :
    IsProbabilityMeasure (znLinkMeasure N h) := by
  apply isProbabilityMeasure_iff.mpr
  have hmeas : Measurable (fun z : UnitAddCircle => (znLinkDensityNN N h z : ENNReal)) := by
    exact measurable_coe_nnreal_ennreal.comp
      (measurable_real_toNNReal.comp (continuous_znPinningFactor N h).measurable)
  rw [znLinkMeasure,
    withDensity_apply (f := fun z => (znLinkDensityNN N h z : ENNReal)) MeasurableSet.univ,
    Measure.restrict_univ]
  rw [lintegral_coe_eq_integral (znLinkDensityNN N h) (znLinkDensity_integrable N h)]
  rw [show (∫ z : UnitAddCircle, (znLinkDensityNN N h z : ℝ)) = 1 from by
    simpa only [znLinkDensityNN_coe] using znLinkFactor_integral_one N h]
  norm_num

@[expose] def znLinkProbabilityMeasure (N : ℕ) (h : NNReal) : ProbabilityMeasure UnitAddCircle :=
  ⟨znLinkMeasure N h, znLinkMeasure_isProbabilityMeasure N h⟩

@[expose] def znRootDiscreteMeasure (N : ℕ) : Measure UnitAddCircle :=
  ∑ k ∈ Finset.univ, ENNReal.ofReal ((N : ℝ)⁻¹) • Measure.dirac (znRoot N k)

theorem znRootDiscreteMeasure_isProbabilityMeasure {N : ℕ} (hN : 0 < N) :
    IsProbabilityMeasure (znRootDiscreteMeasure N) := by
  apply isProbabilityMeasure_iff.mpr
  rw [znRootDiscreteMeasure, Measure.finsetSum_apply]
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  simp [Measure.smul_apply, ENNReal.ofReal_inv_of_pos hNr]
  exact ENNReal.mul_inv_cancel (by exact_mod_cast (Nat.ne_of_gt hN)) (by simp)

theorem znLinkProbabilityMeasure_integral (N : ℕ) (h : NNReal)
    (F : UnitAddCircle → ℝ) :
    (∫ z : UnitAddCircle, F z ∂(znLinkProbabilityMeasure N h)) =
      (∫ z : UnitAddCircle, F z *
        Real.exp ((h : ℝ) * circleCosCharacter N z)) / pinningNormalizer N h := by
  have hmeas : Measurable (fun z : UnitAddCircle => znLinkDensityNN N h z) :=
    measurable_real_toNNReal.comp (continuous_znPinningFactor N h).measurable
  calc
    _ = ∫ z : UnitAddCircle, znLinkDensityNN N h z * F z ∂volume := by
      change (∫ z : UnitAddCircle, F z ∂znLinkMeasure N h) = _
      rw [znLinkMeasure, integral_withDensity_eq_integral_smul hmeas]
      change (∫ z : UnitAddCircle, (znLinkDensityNN N h z : ℝ) * F z ∂volume) = _
      rfl
    _ = ∫ z : UnitAddCircle, znPinningFactor N h z * F z ∂volume := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [] with z
      rw [znLinkDensityNN_coe]
    _ = pinningNormalization N h *
        ∫ z : UnitAddCircle, Real.exp ((h : ℝ) * circleCosCharacter N z) * F z ∂volume := by
      calc
        _ = ∫ z : UnitAddCircle,
            pinningNormalization N h *
              (Real.exp ((h : ℝ) * circleCosCharacter N z) * F z) ∂volume := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards [] with z
          change (pinningNormalization N h *
              Real.exp ((h : ℝ) * circleCosCharacter N z)) * F z = _
          ring
        _ = _ := by rw [MeasureTheory.integral_const_mul]
    _ = (∫ z : UnitAddCircle, F z *
          Real.exp ((h : ℝ) * circleCosCharacter N z)) / pinningNormalizer N h := by
      rw [pinningNormalization, div_eq_mul_inv]
      have hint :
          (∫ z : UnitAddCircle,
            Real.exp ((h : ℝ) * circleCosCharacter N z) * F z) =
          ∫ z : UnitAddCircle,
            F z * Real.exp ((h : ℝ) * circleCosCharacter N z) := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards [] with z
        ring
      rw [hint]
      ring

@[expose] def znUniformFinDiscreteMeasure (N : ℕ) : Measure (Fin N) :=
  ∑ k : Fin N, ENNReal.ofReal ((N : ℝ)⁻¹) • Measure.dirac k

theorem znUniformFinDiscreteMeasure_isProbabilityMeasure {N : ℕ} (hN : 0 < N) :
    IsProbabilityMeasure (znUniformFinDiscreteMeasure N) := by
  apply isProbabilityMeasure_iff.mpr
  rw [znUniformFinDiscreteMeasure, Measure.finsetSum_apply]
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  simp [Measure.smul_apply, ENNReal.ofReal_inv_of_pos hNr]
  exact ENNReal.mul_inv_cancel (by exact_mod_cast (Nat.ne_of_gt hN)) (by simp)

@[expose] def znUniformFinProbabilityMeasure {N : ℕ} (hN : 0 < N) :
    ProbabilityMeasure (Fin N) :=
  ⟨znUniformFinDiscreteMeasure N, znUniformFinDiscreteMeasure_isProbabilityMeasure hN⟩

theorem znUniformFinProbabilityMeasure_integral {N : ℕ} (hN : 0 < N)
    (F : Fin N → ℝ) :
    (∫ k : Fin N, F k ∂(znUniformFinProbabilityMeasure hN)) =
      (N : ℝ)⁻¹ * ∑ k : Fin N, F k := by
  change (∫ k : Fin N, F k ∂znUniformFinDiscreteMeasure N) = _
  unfold znUniformFinDiscreteMeasure
  rw [integral_finsetSum_measure]
  · simp_rw [MeasureTheory.integral_smul_measure, integral_dirac]
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    rw [ENNReal.toReal_ofReal (inv_nonneg.mpr hNr.le)]
    simp [smul_eq_mul]
    rw [Finset.mul_sum]
  · intro k hk
    exact (integrable_dirac (show ‖F k‖ₑ < ⊤ by finiteness)).smul_measure
      (by finiteness)

theorem znUniformFinProbabilityMeasure_singleton {N : ℕ} (hN : 0 < N)
    (k : Fin N) :
    (znUniformFinProbabilityMeasure hN : Measure (Fin N)) {k} =
      ENNReal.ofReal ((N : ℝ)⁻¹) := by
  change znUniformFinDiscreteMeasure N {k} = _
  simp [znUniformFinDiscreteMeasure, Measure.finsetSum_apply, Measure.smul_apply,
    ENNReal.ofReal_inv_of_pos (show (0:ℝ) < N by exact_mod_cast hN),
    Finset.sum_eq_single k, Pi.single_apply]

@[expose] def znRootProbabilityMeasure (N : ℕ) (hN : 0 < N) :
    ProbabilityMeasure UnitAddCircle :=
  ⟨znRootDiscreteMeasure N, znRootDiscreteMeasure_isProbabilityMeasure hN⟩

theorem znRootProbabilityMeasure_eq_map_uniform {N : ℕ} (hN : 0 < N) :
    znRootProbabilityMeasure N hN = (znUniformFinProbabilityMeasure hN).map (znRoot N) := by
  apply ProbabilityMeasure.toMeasure_injective
  simp only [ProbabilityMeasure.toMeasure_map]
  change znRootDiscreteMeasure N =
    Measure.map (znRoot N) (znUniformFinDiscreteMeasure N)
  symm
  have hm : AEMeasurable (znRoot N) (znUniformFinDiscreteMeasure N) :=
    (measurable_of_countable (znRoot N)).aemeasurable
  unfold znUniformFinDiscreteMeasure znRootDiscreteMeasure
  rw [Measure.map_finset_sum' hm]
  simp_rw [Measure.map_smul _ (measurable_of_countable (znRoot N)).aemeasurable,
    Measure.map_dirac]

theorem znRootProbabilityMeasure_integral {N : ℕ} (hN : 0 < N)
    (F : UnitAddCircle →ᵇ ℝ) :
    (∫ z : UnitAddCircle, F z ∂(znRootProbabilityMeasure N hN)) =
      (N : ℝ)⁻¹ * ∑ k : Fin N, F (znRoot N k) := by
  rw [show znRootProbabilityMeasure N hN =
      (znUniformFinProbabilityMeasure hN).map (znRoot N) from
        znRootProbabilityMeasure_eq_map_uniform hN,
    ProbabilityMeasure.toMeasure_map]
  rw [MeasureTheory.integral_map (measurable_of_countable (znRoot N)).aemeasurable
    (F.continuous.stronglyMeasurable.aestronglyMeasurable)]
  simpa using znUniformFinProbabilityMeasure_integral hN (fun k => F (znRoot N k))

theorem tendsto_znLinkProbabilityMeasure {N : ℕ} (hN : 0 < N) :
    Tendsto (fun h : NNReal => znLinkProbabilityMeasure N h) atTop
      (𝓝 (znRootProbabilityMeasure N hN)) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro F
  have hlim := tendsto_znOneLink_ratio hN (fun z : UnitAddCircle => F z) F.continuous
  have hevent : ∀ᶠ h : NNReal in atTop,
      (∫ z : UnitAddCircle,
        znOneLinkIntegrand N h (fun z => F z) z) / pinningNormalizer N h =
          ∫ z : UnitAddCircle, F z ∂znLinkProbabilityMeasure N h := by
    filter_upwards [] with h
    simpa [znOneLinkIntegrand] using (znLinkProbabilityMeasure_integral N h F).symm
  have hconv := hlim.congr' hevent
  simpa only [znRootProbabilityMeasure_integral] using hconv

theorem tendsto_znProductProbabilityMeasure {B : Box 4} {N : ℕ} (hN : 0 < N) :
    Tendsto (fun h : NNReal => ProbabilityMeasure.pi
        (fun _ : PrimalLinks B => znLinkProbabilityMeasure N h)) atTop
      (𝓝 (ProbabilityMeasure.pi
        (fun _ : PrimalLinks B => znRootProbabilityMeasure N hN))) := by
  have htuple : Tendsto (fun h : NNReal =>
      fun _ : PrimalLinks B => znLinkProbabilityMeasure N h) atTop
      (𝓝 (fun _ : PrimalLinks B => znRootProbabilityMeasure N hN)) :=
    tendsto_pi_nhds.2 fun _ => tendsto_znLinkProbabilityMeasure hN
  have hcont : Continuous (fun μ : PrimalLinks B → ProbabilityMeasure UnitAddCircle =>
      ProbabilityMeasure.pi μ) := ProbabilityMeasure.continuous_pi
  exact (hcont.continuousAt
    (x := fun _ : PrimalLinks B => znRootProbabilityMeasure N hN)).tendsto.comp htuple

theorem znRootProduct_eq_map_uniform {B : Box 4} {N : ℕ} (hN : 0 < N) :
    (ProbabilityMeasure.pi (fun _ : PrimalLinks B => znUniformFinProbabilityMeasure hN)).map
      (znConfigAsCircle (B := B) N) =
    ProbabilityMeasure.pi (fun _ : PrimalLinks B => znRootProbabilityMeasure N hN) := by
  apply ProbabilityMeasure.toMeasure_injective
  simp only [ProbabilityMeasure.toMeasure_map, ProbabilityMeasure.toMeasure_pi,
    znRootProbabilityMeasure_eq_map_uniform hN]
  change (Measure.pi (fun _ : PrimalLinks B =>
      (znUniformFinProbabilityMeasure hN : Measure (Fin N)))).map
        (fun a e => znRoot N (a e)) =
    Measure.pi (fun _ : PrimalLinks B =>
      Measure.map (znRoot N) (znUniformFinProbabilityMeasure hN : Measure (Fin N)))
  exact MeasureTheory.Measure.pi_map_pi
    (fun _ => (measurable_of_countable (znRoot N)).aemeasurable)

theorem znUniformProductProbabilityMeasure_singleton {B : Box 4} {N : ℕ}
    (hN : 0 < N) (a : ZNConfig B N) :
    (Measure.pi (fun _ : PrimalLinks B => znUniformFinProbabilityMeasure hN)).real {a} =
      ((N : ℝ)⁻¹) ^ Fintype.card (PrimalLinks B) := by
  have hrect : ({a} : Set (ZNConfig B N)) =
      Set.univ.pi (fun e : PrimalLinks B => {a e}) := by
    ext b
    simp only [Set.mem_singleton_iff, Set.mem_pi, Set.mem_univ, true_implies]
    constructor
    · intro hb
      exact fun e => congrFun hb e
    · intro hb
      exact funext hb
  rw [Measure.real_def, hrect, MeasureTheory.Measure.pi_pi]
  simp_rw [znUniformFinProbabilityMeasure_singleton hN]
  have hNr : 0 ≤ (N : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg N)
  simp [Finset.prod_const, ENNReal.toReal_ofReal hNr]

theorem znRootProductProbabilityMeasure_integral {B : Box 4} {N : ℕ}
    (hN : 0 < N) (F : PrimalAngleConfig B →ᵇ ℝ) :
    (∫ θ : PrimalAngleConfig B, F θ ∂
      (ProbabilityMeasure.pi (fun _ : PrimalLinks B => znRootProbabilityMeasure N hN))) =
      ((N : ℝ)⁻¹) ^ Fintype.card (PrimalLinks B) *
        ∑ a : ZNConfig B N, F (znConfigAsCircle N a) := by
  rw [← znRootProduct_eq_map_uniform hN, ProbabilityMeasure.toMeasure_map]
  rw [MeasureTheory.integral_map
    (measurable_of_countable (znConfigAsCircle N)).aemeasurable
    (F.continuous.stronglyMeasurable.aestronglyMeasurable)]
  have hcont : Continuous (fun a : ZNConfig B N => F (znConfigAsCircle N a)) := by
    fun_prop
  have hint : Integrable (fun a : ZNConfig B N => F (znConfigAsCircle N a))
      (Measure.pi (fun _ : PrimalLinks B => znUniformFinProbabilityMeasure hN)) := by
    apply MeasureTheory.integrableOn_univ.mp
    exact hcont.continuousOn.integrableOn_compact isCompact_univ
  change (∫ a : ZNConfig B N, F (znConfigAsCircle N a) ∂
      Measure.pi (fun _ : PrimalLinks B => znUniformFinProbabilityMeasure hN)) = _
  rw [MeasureTheory.integral_fintype hint]
  simp_rw [znUniformProductProbabilityMeasure_singleton hN, smul_eq_mul]
  rw [← Finset.mul_sum]

@[expose] def znProductProbabilityMeasure {B : Box 4} (N : ℕ) (h : NNReal) :
    ProbabilityMeasure (PrimalAngleConfig B) :=
  ProbabilityMeasure.pi (fun _ : PrimalLinks B => znLinkProbabilityMeasure N h)

@[expose] def znProductDensityNN {B : Box 4} (N : ℕ) (h : NNReal)
    (θ : PrimalAngleConfig B) : NNReal :=
  ∏ e : PrimalLinks B, znLinkDensityNN N h (θ e)

theorem znProductDensityNN_coe {B : Box 4} (N : ℕ) (h : NNReal)
    (θ : PrimalAngleConfig B) :
    (znProductDensityNN N h θ : ℝ) = znPinningDensity N h θ := by
  simp [znProductDensityNN, znPinningDensity, znLinkDensityNN_coe]

theorem measurable_znProductDensityNN {B : Box 4} (N : ℕ) (h : NNReal) :
    Measurable (znProductDensityNN (B := B) N h) := by
  classical
  unfold znProductDensityNN
  refine Finset.measurable_prod Finset.univ ?_
  intro e he
  exact (measurable_real_toNNReal.comp
    (continuous_znPinningFactor N h).measurable).comp (continuous_apply e).measurable

theorem znProductProbabilityMeasure_toMeasure {B : Box 4} (N : ℕ) (h : NNReal) :
    (znProductProbabilityMeasure (B := B) N h : Measure (PrimalAngleConfig B)) =
      (volume : Measure (PrimalAngleConfig B)).withDensity
        (fun θ => (znProductDensityNN N h θ : ENNReal)) := by
  classical
  let μ : (e : PrimalLinks B) → Measure UnitAddCircle := fun _ => volume
  let f : (e : PrimalLinks B) → UnitAddCircle → NNReal := fun _ => znLinkDensityNN N h
  have hmeas : ∀ e, Measurable (f e) := fun _ =>
    measurable_real_toNNReal.comp (continuous_znPinningFactor N h).measurable
  have hsig : ∀ e, SigmaFinite ((μ e).withDensity (fun z => (f e z : ENNReal))) := by
    intro e
    let : IsProbabilityMeasure ((μ e).withDensity (fun z => (f e z : ENNReal))) :=
      znLinkMeasure_isProbabilityMeasure N h
    infer_instance
  have hprod := measure_pi_withDensity_nnreal μ f hmeas
  have hprod' : Measure.pi (fun _ : PrimalLinks B => znLinkMeasure N h) =
      (Measure.pi fun _ : PrimalLinks B => (volume : Measure UnitAddCircle)).withDensity
        (fun θ => (znProductDensityNN N h θ : ENNReal)) := by
    simpa [μ, f, znLinkMeasure, znProductDensityNN] using hprod
  change Measure.pi (fun _ : PrimalLinks B => znLinkMeasure N h) = _
  rw [MeasureTheory.volume_pi]
  exact hprod'

theorem znProductProbabilityMeasure_integral {B : Box 4} (N : ℕ) (h : NNReal)
    (F : PrimalAngleConfig B → ℝ) :
    (∫ θ, F θ ∂(znProductProbabilityMeasure (B := B) N h)) =
      ∫ θ, znPinningDensity N h θ * F θ := by
  calc
    _ = ∫ θ, F θ ∂((volume : Measure (PrimalAngleConfig B)).withDensity
        (fun θ => (znProductDensityNN N h θ : ENNReal))) := by
      rw [znProductProbabilityMeasure_toMeasure (B := B) N h]
    _ = ∫ θ, znProductDensityNN N h θ * F θ := by
      rw [integral_withDensity_eq_integral_smul (measurable_znProductDensityNN N h) F]
      apply MeasureTheory.integral_congr_ae
      filter_upwards [] with θ
      rfl
    _ = ∫ θ, znPinningDensity N h θ * F θ := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [] with θ
      rw [znProductDensityNN_coe]

@[expose] def finiteZNNormalizedInsertion {B : Box 4} (β : ℝ) (N : ℕ)
    (h : NNReal) (G : PrimalAngleConfig B →ᵇ ℝ) : ℝ :=
  (∫ θ, G θ * znPinningDensity N h θ) /
    finiteZNPartitionFunction (B := B) β N h

theorem tendsto_finiteZNNormalizedInsertion {B : Box 4} (β : ℝ) {N : ℕ}
    (hN : 0 < N) (G : PrimalAngleConfig B →ᵇ ℝ) :
    Tendsto (fun h : NNReal => finiteZNNormalizedInsertion β N h G) atTop
      (𝓝 ((∑ a : ZNConfig B N, G (znConfigAsCircle N a)) /
        discreteZNPartitionFunction (B := B) β N)) := by
  let W : PrimalAngleConfig B →ᵇ ℝ :=
    BoundedContinuousFunction.mkOfCompact
      ⟨wilsonActionDensity β, continuous_wilsonActionDensity β⟩
  let muLim : ProbabilityMeasure (PrimalAngleConfig B) :=
    ProbabilityMeasure.pi (fun _ : PrimalLinks B => znRootProbabilityMeasure N hN)
  have hμ : Tendsto (fun h : NNReal => znProductProbabilityMeasure (B := B) N h)
      atTop (𝓝 muLim) := by
    simpa [muLim, znProductProbabilityMeasure] using
      tendsto_znProductProbabilityMeasure (B := B) (N := N) hN
  have hGlim : Tendsto (fun h : NNReal =>
      ∫ θ, G θ ∂(znProductProbabilityMeasure (B := B) N h)) atTop
      (𝓝 (∫ θ, G θ ∂muLim)) := by
    exact ((ProbabilityMeasure.continuous_integral_boundedContinuousFunction G).continuousAt.tendsto).comp hμ
  have hWlim : Tendsto (fun h : NNReal =>
      ∫ θ, W θ ∂(znProductProbabilityMeasure (B := B) N h)) atTop
      (𝓝 (∫ θ, W θ ∂muLim)) := by
    exact ((ProbabilityMeasure.continuous_integral_boundedContinuousFunction W).continuousAt.tendsto).comp hμ
  have hGendpoint : (∫ θ, G θ ∂muLim) =
      ((N : ℝ) ^ Fintype.card (PrimalLinks B))⁻¹ *
        ∑ a : ZNConfig B N, G (znConfigAsCircle N a) := by
    simpa only [inv_pow] using znRootProductProbabilityMeasure_integral hN G
  have hWendpoint : (∫ θ, W θ ∂muLim) =
      ((N : ℝ) ^ Fintype.card (PrimalLinks B))⁻¹ *
        discreteZNPartitionFunction (B := B) β N := by
    rw [znRootProductProbabilityMeasure_integral hN W]
    simp [W, discreteZNPartitionFunction, discreteZNWeight, inv_pow]
  have hGmodel (h : NNReal) :
      (∫ θ, G θ * znPinningDensity N h θ) =
        ∫ θ, G θ ∂(znProductProbabilityMeasure (B := B) N h) := by
    rw [znProductProbabilityMeasure_integral]
    apply MeasureTheory.integral_congr_ae
    filter_upwards [] with θ
    ring
  have hWmodel (h : NNReal) :
      finiteZNPartitionFunction (B := B) β N h =
        ∫ θ, W θ ∂(znProductProbabilityMeasure (B := B) N h) := by
    rw [znProductProbabilityMeasure_integral]
    unfold finiteZNPartitionFunction finiteZNWeight
    apply MeasureTheory.integral_congr_ae
    filter_upwards [] with θ
    simp [W]
    ring
  have hGlim' : Tendsto (fun h : NNReal =>
      ∫ θ, G θ * znPinningDensity N h θ) atTop
      (𝓝 (((N : ℝ) ^ Fintype.card (PrimalLinks B))⁻¹ *
        ∑ a : ZNConfig B N, G (znConfigAsCircle N a))) := by
    have h := hGlim.congr' (Filter.Eventually.of_forall fun h => (hGmodel h).symm)
    simpa [hGendpoint] using h
  have hWlim' : Tendsto (fun h : NNReal =>
      finiteZNPartitionFunction (B := B) β N h) atTop
      (𝓝 (((N : ℝ) ^ Fintype.card (PrimalLinks B))⁻¹ *
        discreteZNPartitionFunction (B := B) β N)) := by
    have h := hWlim.congr' (Filter.Eventually.of_forall fun h => (hWmodel h).symm)
    simpa [hWendpoint] using h
  have hc : 0 < ((N : ℝ) ^ Fintype.card (PrimalLinks B))⁻¹ :=
    inv_pos.mpr (pow_pos (by exact_mod_cast hN) _)
  have hZ : 0 < discreteZNPartitionFunction (B := B) β N :=
    discreteZNPartitionFunction_pos β N hN
  have hratio :
      (((N : ℝ) ^ Fintype.card (PrimalLinks B))⁻¹ *
        ∑ a : ZNConfig B N, G (znConfigAsCircle N a)) /
      (((N : ℝ) ^ Fintype.card (PrimalLinks B))⁻¹ *
        discreteZNPartitionFunction (B := B) β N) =
      (∑ a : ZNConfig B N, G (znConfigAsCircle N a)) /
        discreteZNPartitionFunction (B := B) β N := by
    field_simp [hc.ne', hZ.ne']
  have hquot := hGlim'.div hWlim' (mul_ne_zero hc.ne' hZ.ne')
  change Tendsto (fun h : NNReal =>
    (∫ θ, G θ * znPinningDensity N h θ) /
      finiteZNPartitionFunction (B := B) β N h) atTop
    (𝓝 ((((N : ℝ) ^ Fintype.card (PrimalLinks B))⁻¹ *
      ∑ a : ZNConfig B N, G (znConfigAsCircle N a)) /
      (((N : ℝ) ^ Fintype.card (PrimalLinks B))⁻¹ *
        discreteZNPartitionFunction (B := B) β N))) at hquot
  simpa only [finiteZNNormalizedInsertion, hratio] using hquot


theorem tendsto_finiteDisorderExpectation {B : Box 4} (β : ℝ) {N : ℕ}
    (hN : 0 < N) (ξ : ℕ) (S : Chain 4 B) :
    Tendsto (fun h : NNReal => finiteDisorderExpectation β N ξ h S) atTop
      (𝓝 (discreteDisorderExpectation β N ξ S)) := by
  let G : PrimalAngleConfig B →ᵇ ℝ :=
    BoundedContinuousFunction.mkOfCompact
      ⟨twistedWilsonActionDensity β N ξ S,
        continuous_twistedWilsonActionDensity β N ξ S⟩
  have hlim := tendsto_finiteZNNormalizedInsertion β hN G
  have heq (h : NNReal) :
      finiteDisorderExpectation β N ξ h S = finiteZNNormalizedInsertion β N h G := by
    unfold finiteDisorderExpectation finiteDisorderNumerator finiteZNNormalizedInsertion
    congr 1
  have hend :
      (∑ a : ZNConfig B N, G (znConfigAsCircle N a)) /
        discreteZNPartitionFunction (B := B) β N = discreteDisorderExpectation β N ξ S := by
    simp [G, discreteDisorderExpectation, discreteDisorderNumerator]
  simpa only [hend] using hlim.congr' (Filter.Eventually.of_forall fun h => (heq h).symm)

/-- The C1-positioned centered-cube disorder insertion converges to its
literal finite `ℤ_N` endpoint. -/
theorem tendsto_finiteCenteredDisorderExpectation
    (β : ℝ) {N ξ L T N_box : ℕ} (hN : 0 < N)
    (hL : L ≤ N_box) (hT : T ≤ N_box) (hbox : 0 < N_box) :
    Tendsto
      (fun h : NNReal =>
        finiteCenteredDisorderExpectation β N ξ L T N_box h hL hT hbox)
      atTop
      (𝓝 (discreteCenteredDisorderExpectation β N ξ L T N_box hL hT hbox)) := by
  exact tendsto_finiteDisorderExpectation β hN ξ
    (centeredRectangularTwistSheet hL hT hbox)

end

end FroehlichSpencer.FS82.ZN

end
