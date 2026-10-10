/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Infinite.FourierApproximation
public import FroehlichSpencer.FS82.Infinite.FourierVariationalIntegral

import Mathlib.MeasureTheory.Integral.Bochner.Basic

open MeasureTheory
open Filter
open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Infinite
open FroehlichSpencer.FS82.Infinite.Fourier
open FroehlichSpencer.FS82.Infinite.FourierApproximation
open FroehlichSpencer.FS82.Infinite.FourierVariational
open FroehlichSpencer.FS82.Infinite.FourierVariationalIntegral
open scoped ComplexConjugate

@[expose] public section

namespace FroehlichSpencer.FS82.Infinite.FourierGreenEquality

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
local instance : BorelSpace (AddCircle (1 : ℝ) ×
    (AddCircle (1 : ℝ) × AddCircle (1 : ℝ))) := by infer_instance
local instance : BorelSpace Torus4 := by
  dsimp [Torus4]
  infer_instance
local instance : IsFiniteMeasure torus4Haar := by
  dsimp [torus4Haar]
  infer_instance


private theorem continuous_torus4Coord_local (i : Fin 4) :
    Continuous (fun k : Torus4 => torus4Coord k i) := by
  fin_cases i <;> simp [torus4Coord] <;> fun_prop

private theorem continuous_fourierLaplacianSymbol_local :
    Continuous fourierLaplacianSymbol := by
  unfold fourierLaplacianSymbol
  apply continuous_finsetSum
  intro i hi
  have hcoord := continuous_torus4Coord_local i
  have hfourier : Continuous (fun k : Torus4 =>
      fourier 1 (torus4Coord k i)) :=
    (map_continuous (fourier 1)).comp hcoord
  exact (continuous_norm.comp (continuous_const.sub hfourier)).pow 2

private theorem continuous_globalLinkFourierComponent_local
    (μ : GlobalLinkField) (i : Fin 4) :
    Continuous (globalLinkFourierComponent μ i) := by
  unfold globalLinkFourierComponent
  apply continuous_finsetSum
  intro c hc
  exact continuous_const.mul
    (FourierApproximation.continuous_latticeCharacter (latticeCellPoint c))

private theorem continuous_latticeChainFourierComponent_local
    (q : RealLatticeChain 4) (axes : Finset (Fin 4)) :
    Continuous (latticeChainFourierComponent q axes) := by
  unfold latticeChainFourierComponent
  apply continuous_finsetSum
  intro c hc
  exact continuous_const.mul
    (FourierApproximation.continuous_latticeCharacter (latticeCellPoint c))

theorem fourierLaplacianSymbol_torusNeg (k : Torus4) :
    fourierLaplacianSymbol (-k) = fourierLaplacianSymbol k := by
  have hcoord (i : Fin 4) : torus4Coord (-k) i = -torus4Coord k i := by
    fin_cases i <;> simp [torus4Coord]
  unfold fourierLaplacianSymbol
  apply Finset.sum_congr rfl
  intro i hi
  rw [hcoord i]
  have hfourier : fourier 1 (-torus4Coord k i) =
      conj (fourier 1 (torus4Coord k i)) := by
    rw [fourier_one, fourier_one, AddCircle.toCircle_neg, Circle.coe_inv_eq_conj]
  rw [hfourier]
  have hnorm : (1 : ℂ) - conj (fourier 1 (torus4Coord k i)) =
      conj (1 - fourier 1 (torus4Coord k i)) := by simp
  rw [hnorm]
  rw [Complex.norm_conj]

theorem globalLinkFourierComponent_torusNeg (μ : GlobalLinkField) (i : Fin 4)
    (k : Torus4) :
    globalLinkFourierComponent μ i (-k) =
      conj (globalLinkFourierComponent μ i k) := by
  classical
  simp only [globalLinkFourierComponent, map_sum, map_mul,
    Complex.conj_ofReal, FourierApproximation.latticeCharacter_torusNeg]

noncomputable def regularizedPotentialMap (μ : GlobalLinkField) (n : ℕ)
    (i : Fin 4) : C(Torus4, ℂ) where
  toFun k := globalLinkFourierComponent μ i k /
    ((fourierLaplacianSymbol k + ((n : ℝ) + 1)⁻¹ : ℝ) : ℂ)
  continuous_toFun := by
    have hnum := continuous_globalLinkFourierComponent_local μ i
    have hreal := continuous_fourierLaplacianSymbol_local.add
      (continuous_const : Continuous (fun _ : Torus4 => ((n : ℝ) + 1)⁻¹))
    have hden : Continuous (fun k : Torus4 =>
        ((fourierLaplacianSymbol k + ((n : ℝ) + 1)⁻¹ : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp hreal
    apply hnum.div hden
    intro k
    have hpos : 0 < fourierLaplacianSymbol k + ((n : ℝ) + 1)⁻¹ := by
      exact add_pos_of_nonneg_of_pos (fourierLaplacianSymbol_nonneg k) (by positivity)
    exact_mod_cast ne_of_gt hpos

theorem regularizedPotentialMap_torusNeg (μ : GlobalLinkField) (n : ℕ)
    (i : Fin 4) (k : Torus4) :
    regularizedPotentialMap μ n i (-k) =
      conj (regularizedPotentialMap μ n i k) := by
  have hden := fourierLaplacianSymbol_torusNeg k
  simp only [regularizedPotentialMap, ContinuousMap.coe_mk,
    globalLinkFourierComponent_torusNeg, hden, map_div₀, Complex.conj_ofReal]

theorem exists_globalLinkField_regularizedApprox (μ : GlobalLinkField) (n : ℕ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ φ : GlobalLinkField, ∀ i k,
      ‖globalLinkFourierComponent φ i k - regularizedPotentialMap μ n i k‖ < ε := by
  classical
  choose c hc using fun i : Fin 4 =>
    exists_realFourierPoly_approx (regularizedPotentialMap μ n i)
      (fun k => by simpa using regularizedPotentialMap_torusNeg μ n i (-k)) ε hε
  refine ⟨liftLinkCoefficients (realFamilyPairCoefficients c), ?_⟩
  intro i k
  rw [liftRealFamily_fourier]
  calc
    ‖realFourierPoly (c i) k - regularizedPotentialMap μ n i k‖ =
        ‖(regularizedPotentialMap μ n i - realFourierPoly (c i)) k‖ := by
      calc
        _ = ‖-((regularizedPotentialMap μ n i - realFourierPoly (c i)) k)‖ := by
          congr 1
          simp [ContinuousMap.sub_apply]
        _ = _ := norm_neg _
    _ ≤ ‖regularizedPotentialMap μ n i - realFourierPoly (c i)‖ :=
      (regularizedPotentialMap μ n i - realFourierPoly (c i)).norm_coe_le_norm k
    _ < ε := hc i

noncomputable def fourierPotential (μ : GlobalLinkField) (i : Fin 4) (k : Torus4) : ℂ :=
  globalLinkFourierComponent μ i k / (fourierLaplacianSymbol k : ℂ)

noncomputable def weightedApproxError (μ : GlobalLinkField) (n : ℕ) (k : Torus4) : ℝ :=
  fourierLaplacianSymbol k * ∑ i : Fin 4,
    Complex.normSq (fourierPotential μ i k - regularizedPotentialMap μ n i k)

noncomputable def weightedPotentialError (μ φ : GlobalLinkField) (k : Torus4) : ℝ :=
  fourierLaplacianSymbol k * ∑ i : Fin 4,
    Complex.normSq (globalLinkFourierComponent φ i k - fourierPotential μ i k)

private theorem complex_normSq_sub_le (z w : ℂ) :
    Complex.normSq (z - w) ≤ 2 * Complex.normSq z + 2 * Complex.normSq w := by
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
  have htri := norm_sub_le z w
  have hnonneg₀ := norm_nonneg (z - w)
  have hnonneg₁ := norm_nonneg z
  have hnonneg₂ := norm_nonneg w
  nlinarith [sq_nonneg (‖z‖ - ‖w‖)]

private theorem scaled_normSq_div_le (z : ℂ) {lam d : ℝ}
    (hlam : 0 < lam) (hd : lam ≤ d) :
    lam * Complex.normSq (z / (d : ℂ)) ≤ Complex.normSq z / lam := by
  rw [Complex.normSq_div, Complex.normSq_ofReal]
  have hdpos : 0 < d := lt_of_lt_of_le hlam hd
  have hcoef : lam / d ^ 2 ≤ 1 / lam := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hdpos) hlam).2
    nlinarith [sq_nonneg (d - lam)]
  have hnonneg : 0 ≤ Complex.normSq z := Complex.normSq_nonneg _
  calc
    lam * (Complex.normSq z / (d * d)) =
        Complex.normSq z * (lam / (d * d)) := by
          field_simp [ne_of_gt hdpos]
    _ ≤ Complex.normSq z * (1 / lam) :=
      mul_le_mul_of_nonneg_left (by simpa [pow_two] using hcoef) hnonneg
    _ = Complex.normSq z / lam := by ring

private theorem tendsto_inv_nat_add_one :
    Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (nhds 0) := by
  have htop : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  change Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (nhds 0)
  exact tendsto_inv_atTop_zero.comp htop

private theorem weightedApproxError_tendsto_zero
    (μ : GlobalLinkField) (k : Torus4) (hpos : 0 < fourierLaplacianSymbol k) :
    Tendsto (fun n : ℕ => weightedApproxError μ n k) atTop (nhds 0) := by
  let lam := fourierLaplacianSymbol k
  have hdelta := tendsto_inv_nat_add_one
  have hreal : Tendsto (fun n : ℕ => lam + ((n : ℝ) + 1)⁻¹) atTop (nhds lam) := by
    simpa using tendsto_const_nhds.add hdelta
  have hden : Tendsto (fun n : ℕ =>
      ((lam + ((n : ℝ) + 1)⁻¹ : ℝ) : ℂ)) atTop (nhds (lam : ℂ)) :=
    (Complex.continuous_ofReal.continuousAt.tendsto).comp hreal
  have hquot (i : Fin 4) : Tendsto (fun n : ℕ =>
      globalLinkFourierComponent μ i k /
        ((lam + ((n : ℝ) + 1)⁻¹ : ℝ) : ℂ)) atTop
      (nhds (globalLinkFourierComponent μ i k / (lam : ℂ))) :=
    tendsto_const_nhds.div hden (by exact_mod_cast ne_of_gt hpos)
  have hnormSq (i : Fin 4) : Tendsto (fun n : ℕ =>
      Complex.normSq (fourierPotential μ i k - regularizedPotentialMap μ n i k))
      atTop (nhds 0) := by
    have hdiff : Tendsto (fun n : ℕ =>
        fourierPotential μ i k - regularizedPotentialMap μ n i k) atTop (nhds 0) := by
      have hconst : Tendsto (fun _ : ℕ =>
          globalLinkFourierComponent μ i k / (lam : ℂ)) atTop
          (nhds (globalLinkFourierComponent μ i k / (lam : ℂ))) := tendsto_const_nhds
      simpa [fourierPotential, regularizedPotentialMap, lam] using hconst.sub (hquot i)
    have hcomp :=
      (Complex.continuous_normSq.continuousAt.tendsto).comp hdiff
    convert hcomp using 1
    · rfl
    · rw [Complex.normSq_zero]
  have hsum : Tendsto (fun n : ℕ => ∑ i : Fin 4,
      Complex.normSq (fourierPotential μ i k - regularizedPotentialMap μ n i k))
      atTop (nhds 0) := by
    have hs := tendsto_finsetSum (s := Finset.univ)
      (f := fun i n => Complex.normSq
        (fourierPotential μ i k - regularizedPotentialMap μ n i k))
      (a := fun _ : Fin 4 => 0) (fun i hi => hnormSq i)
    simpa using hs
  have hconstlam : Tendsto (fun _ : ℕ => lam) atTop (nhds lam) := tendsto_const_nhds
  have hmul := hconstlam.mul hsum
  simpa [weightedApproxError, lam] using hmul

private theorem fourierLaplacianSymbol_le_sixteen (k : Torus4) :
    fourierLaplacianSymbol k ≤ 16 := by
  unfold fourierLaplacianSymbol
  have hterm (i : Fin 4) :
      ‖(1 : ℂ) - fourier 1 (torus4Coord k i)‖ ^ 2 ≤ 4 := by
    have hcircle : ‖fourier 1 (torus4Coord k i)‖ = 1 := by
      rw [fourier_one]
      exact Circle.norm_coe _
    have hdist : ‖(1 : ℂ) - fourier 1 (torus4Coord k i)‖ ≤ 2 := by
      calc
        _ ≤ ‖(1 : ℂ)‖ + ‖fourier 1 (torus4Coord k i)‖ := norm_sub_le _ _
        _ = 2 := by norm_num [hcircle]
    have hnonneg : 0 ≤ ‖(1 : ℂ) - fourier 1 (torus4Coord k i)‖ := norm_nonneg _
    nlinarith
  calc
    _ ≤ ∑ i : Fin 4, (4 : ℝ) := Finset.sum_le_sum (fun i hi => hterm i)
    _ = 16 := by norm_num

private theorem weightedApproxError_nonneg (μ : GlobalLinkField) (n : ℕ)
    (k : Torus4) : 0 ≤ weightedApproxError μ n k := by
  unfold weightedApproxError
  exact mul_nonneg (fourierLaplacianSymbol_nonneg k)
    (Finset.sum_nonneg fun i hi => Complex.normSq_nonneg _)

private theorem weightedApproxError_le_four_green (μ : GlobalLinkField) (n : ℕ)
    (k : Torus4) :
    weightedApproxError μ n k ≤ 4 * fourierGreenDensity μ k := by
  let lam := fourierLaplacianSymbol k
  have hlam0 : 0 ≤ lam := fourierLaplacianSymbol_nonneg k
  by_cases hlam : lam = 0
  · simp [weightedApproxError, fourierGreenDensity, lam, hlam]
  · have hlampos : 0 < lam := lt_of_le_of_ne hlam0 (Ne.symm hlam)
    have hterm (i : Fin 4) :
        lam * Complex.normSq (fourierPotential μ i k - regularizedPotentialMap μ n i k) ≤
          4 * (Complex.normSq (globalLinkFourierComponent μ i k) / lam) := by
      have hsub := complex_normSq_sub_le (fourierPotential μ i k)
        (regularizedPotentialMap μ n i k)
      have htarget := scaled_normSq_div_le (globalLinkFourierComponent μ i k)
        hlampos (le_rfl : lam ≤ lam)
      have hδ : 0 < ((n : ℝ) + 1)⁻¹ := by positivity
      have hden : lam ≤ lam + ((n : ℝ) + 1)⁻¹ := by linarith
      have hregularized := scaled_normSq_div_le (globalLinkFourierComponent μ i k)
        hlampos hden
      change lam * Complex.normSq (fourierPotential μ i k) ≤ _ at htarget
      have hmul := mul_le_mul_of_nonneg_left hsub hlam0
      have hpoint : lam * Complex.normSq (regularizedPotentialMap μ n i k) ≤
          Complex.normSq (globalLinkFourierComponent μ i k) / lam := by
        change lam * Complex.normSq
          (globalLinkFourierComponent μ i k /
            ((lam + ((n : ℝ) + 1)⁻¹ : ℝ) : ℂ)) ≤ _
        exact hregularized
      calc
        _ ≤ lam * (2 * Complex.normSq (fourierPotential μ i k) +
            2 * Complex.normSq (regularizedPotentialMap μ n i k)) := hmul
        _ = 2 * (lam * Complex.normSq (fourierPotential μ i k)) +
            2 * (lam * Complex.normSq (regularizedPotentialMap μ n i k)) := by ring
        _ ≤ 4 * (Complex.normSq (globalLinkFourierComponent μ i k) / lam) := by
          nlinarith [htarget, hpoint]
    calc
      weightedApproxError μ n k =
          ∑ i : Fin 4, lam * Complex.normSq
            (fourierPotential μ i k - regularizedPotentialMap μ n i k) := by
        simp [weightedApproxError, lam, Finset.mul_sum]
      _ ≤ ∑ i : Fin 4, 4 *
            (Complex.normSq (globalLinkFourierComponent μ i k) / lam) :=
        Finset.sum_le_sum fun i hi => hterm i
      _ = 4 * fourierGreenDensity μ k := by
        rw [← Finset.mul_sum, ← Finset.sum_div]
        unfold fourierGreenDensity
        rw [← Finset.sum_div]
        rw [show lam = fourierLaplacianSymbol k by rfl]
        have hsum : (∑ i : Fin 4,
            Complex.normSq (globalLinkFourierComponent μ i k)) =
          ∑ i : Fin 4, ‖globalLinkFourierComponent μ i k‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro i hi
          exact Complex.normSq_eq_norm_sq _
        rw [hsum]

private theorem measurable_fourierPotential (μ : GlobalLinkField) (i : Fin 4) :
    Measurable (fun k : Torus4 => fourierPotential μ i k) := by
  have hnum : Measurable (globalLinkFourierComponent μ i) :=
    (continuous_globalLinkFourierComponent_local μ i).measurable
  have hden : Measurable (fun k : Torus4 => (fourierLaplacianSymbol k : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp continuous_fourierLaplacianSymbol_local.measurable
  exact hnum.div hden

private theorem measurable_weightedApproxError (μ : GlobalLinkField) (n : ℕ) :
    Measurable (weightedApproxError μ n) := by
  have hsum : Measurable (fun k : Torus4 => ∑ i : Fin 4,
      Complex.normSq (fourierPotential μ i k - regularizedPotentialMap μ n i k)) :=
    Finset.measurable_sum Finset.univ (fun i hi =>
      Complex.continuous_normSq.measurable.comp
        ((measurable_fourierPotential μ i).sub
          (regularizedPotentialMap μ n i).continuous.measurable))
  exact continuous_fourierLaplacianSymbol_local.measurable.mul hsum

private theorem integrable_weightedApproxError (μ : GlobalLinkField) (n : ℕ) :
    Integrable (weightedApproxError μ n) torus4Haar := by
  have hmajorant : Integrable (fun k : Torus4 => 4 * fourierGreenDensity μ k) torus4Haar :=
    (Fourier.integrable_fourierGreenDensity μ).const_mul 4
  apply hmajorant.mono'
    (measurable_weightedApproxError μ n).aestronglyMeasurable
  filter_upwards with k
  rw [Real.norm_eq_abs, abs_of_nonneg (weightedApproxError_nonneg μ n k)]
  exact weightedApproxError_le_four_green μ n k

theorem integral_weightedApproxError_tendsto_zero (μ : GlobalLinkField) :
    Tendsto (fun n : ℕ => ∫ k : Torus4, weightedApproxError μ n k ∂torus4Haar)
      atTop (nhds 0) := by
  have hbound_integrable :
      Integrable (fun k : Torus4 => 4 * fourierGreenDensity μ k) torus4Haar :=
    (Fourier.integrable_fourierGreenDensity μ).const_mul 4
  have hFmeas : ∀ n : ℕ,
      AEStronglyMeasurable (weightedApproxError μ n) torus4Haar := by
    intro n
    exact (measurable_weightedApproxError μ n).aestronglyMeasurable
  have hbound : ∀ n : ℕ, ∀ᵐ k : Torus4 ∂torus4Haar,
      ‖weightedApproxError μ n k‖ ≤ 4 * fourierGreenDensity μ k := by
    intro n
    filter_upwards with k
    rw [Real.norm_eq_abs, abs_of_nonneg (weightedApproxError_nonneg μ n k)]
    exact weightedApproxError_le_four_green μ n k
  have hlim : ∀ᵐ k : Torus4 ∂torus4Haar,
      Tendsto (fun n : ℕ => weightedApproxError μ n k) atTop (nhds 0) := by
    filter_upwards [FourierVariationalIntegral.ae_symbol_positive] with k hk
    exact weightedApproxError_tendsto_zero μ k hk
  have hDCT := tendsto_integral_of_dominated_convergence
    (fun k : Torus4 => 4 * fourierGreenDensity μ k) hFmeas hbound_integrable hbound hlim
  simpa using hDCT

private theorem weightedPotentialError_le_regularized
    (μ φ : GlobalLinkField) (n : ℕ) (ε : ℝ) (hε : 0 < ε)
    (happrox : ∀ i k,
      ‖globalLinkFourierComponent φ i k - regularizedPotentialMap μ n i k‖ < ε)
    (k : Torus4) :
    weightedPotentialError μ φ k ≤
      2 * weightedApproxError μ n k + 128 * ε ^ 2 := by
  let lam := fourierLaplacianSymbol k
  have hlam0 : 0 ≤ lam := fourierLaplacianSymbol_nonneg k
  have hterm (i : Fin 4) :
      lam * Complex.normSq (globalLinkFourierComponent φ i k - fourierPotential μ i k) ≤
        2 * (lam * Complex.normSq
          (globalLinkFourierComponent φ i k - regularizedPotentialMap μ n i k)) +
        2 * (lam * Complex.normSq
          (fourierPotential μ i k - regularizedPotentialMap μ n i k)) := by
    have hsub := complex_normSq_sub_le
      (globalLinkFourierComponent φ i k - regularizedPotentialMap μ n i k)
      (fourierPotential μ i k - regularizedPotentialMap μ n i k)
    have hmul := mul_le_mul_of_nonneg_left hsub hlam0
    have heq : (globalLinkFourierComponent φ i k - regularizedPotentialMap μ n i k) -
        (fourierPotential μ i k - regularizedPotentialMap μ n i k) =
        globalLinkFourierComponent φ i k - fourierPotential μ i k := by ring
    calc
      _ = lam * Complex.normSq
          ((globalLinkFourierComponent φ i k - regularizedPotentialMap μ n i k) -
            (fourierPotential μ i k - regularizedPotentialMap μ n i k)) := by rw [heq]
      _ ≤ lam * (2 * Complex.normSq
          (globalLinkFourierComponent φ i k - regularizedPotentialMap μ n i k) +
        2 * Complex.normSq (fourierPotential μ i k - regularizedPotentialMap μ n i k)) := hmul
      _ = 2 * (lam * Complex.normSq
          (globalLinkFourierComponent φ i k - regularizedPotentialMap μ n i k)) +
        2 * (lam * Complex.normSq
          (fourierPotential μ i k - regularizedPotentialMap μ n i k)) := by ring
  have hpoly (i : Fin 4) :
      Complex.normSq (globalLinkFourierComponent φ i k -
        regularizedPotentialMap μ n i k) ≤ ε ^ 2 := by
    rw [Complex.normSq_eq_norm_sq]
    have h := happrox i k
    nlinarith [norm_nonneg
      (globalLinkFourierComponent φ i k - regularizedPotentialMap μ n i k)]
  have hsumPoly : (∑ i : Fin 4, Complex.normSq
      (globalLinkFourierComponent φ i k - regularizedPotentialMap μ n i k)) ≤
      4 * ε ^ 2 := by
    calc
      _ ≤ ∑ i : Fin 4, ε ^ 2 := Finset.sum_le_sum (fun i hi => hpoly i)
      _ = 4 * ε ^ 2 := by norm_num
  calc
    weightedPotentialError μ φ k =
        ∑ i : Fin 4, lam * Complex.normSq
          (globalLinkFourierComponent φ i k - fourierPotential μ i k) := by
      simp [weightedPotentialError, lam, Finset.mul_sum]
    _ ≤ ∑ i : Fin 4,
          (2 * (lam * Complex.normSq
            (globalLinkFourierComponent φ i k - regularizedPotentialMap μ n i k)) +
           2 * (lam * Complex.normSq
            (fourierPotential μ i k - regularizedPotentialMap μ n i k))) :=
      Finset.sum_le_sum (fun i hi => hterm i)
    _ = 2 * (lam * ∑ i : Fin 4, Complex.normSq
          (globalLinkFourierComponent φ i k - regularizedPotentialMap μ n i k)) +
        2 * weightedApproxError μ n k := by
      unfold weightedApproxError
      calc
        _ = (∑ i : Fin 4, 2 * (lam * Complex.normSq
              (globalLinkFourierComponent φ i k - regularizedPotentialMap μ n i k))) +
            (∑ i : Fin 4, 2 * (lam * Complex.normSq
              (fourierPotential μ i k - regularizedPotentialMap μ n i k))) := by
          rw [Finset.sum_add_distrib]
        _ = 2 * (∑ i : Fin 4, lam * Complex.normSq
              (globalLinkFourierComponent φ i k - regularizedPotentialMap μ n i k)) +
            2 * (∑ i : Fin 4, lam * Complex.normSq
              (fourierPotential μ i k - regularizedPotentialMap μ n i k)) := by
          have hA : (∑ i : Fin 4, 2 * (lam * Complex.normSq
              (globalLinkFourierComponent φ i k - regularizedPotentialMap μ n i k))) =
              2 * (∑ i : Fin 4, lam * Complex.normSq
                (globalLinkFourierComponent φ i k - regularizedPotentialMap μ n i k)) := by
            exact (Finset.mul_sum Finset.univ
              (fun i : Fin 4 => lam * Complex.normSq
                (globalLinkFourierComponent φ i k - regularizedPotentialMap μ n i k)) 2).symm
          have hB : (∑ i : Fin 4, 2 * (lam * Complex.normSq
              (fourierPotential μ i k - regularizedPotentialMap μ n i k))) =
              2 * (∑ i : Fin 4, lam * Complex.normSq
                (fourierPotential μ i k - regularizedPotentialMap μ n i k)) := by
            exact (Finset.mul_sum Finset.univ
              (fun i : Fin 4 => lam * Complex.normSq
                (fourierPotential μ i k - regularizedPotentialMap μ n i k)) 2).symm
          rw [hA, hB]
        _ = 2 * (lam * ∑ i : Fin 4, Complex.normSq
              (globalLinkFourierComponent φ i k - regularizedPotentialMap μ n i k)) +
            2 * (lam * ∑ i : Fin 4, Complex.normSq
              (fourierPotential μ i k - regularizedPotentialMap μ n i k)) := by
          have hA : (∑ i : Fin 4, lam * Complex.normSq
              (globalLinkFourierComponent φ i k - regularizedPotentialMap μ n i k)) =
              lam * (∑ i : Fin 4, Complex.normSq
                (globalLinkFourierComponent φ i k - regularizedPotentialMap μ n i k)) :=
            (Finset.mul_sum Finset.univ
              (fun i : Fin 4 => Complex.normSq
                (globalLinkFourierComponent φ i k - regularizedPotentialMap μ n i k)) lam).symm
          have hB : (∑ i : Fin 4, lam * Complex.normSq
              (fourierPotential μ i k - regularizedPotentialMap μ n i k)) =
              lam * (∑ i : Fin 4, Complex.normSq
                (fourierPotential μ i k - regularizedPotentialMap μ n i k)) :=
            (Finset.mul_sum Finset.univ
              (fun i : Fin 4 => Complex.normSq
                (fourierPotential μ i k - regularizedPotentialMap μ n i k)) lam).symm
          rw [hA, hB]
        _ = _ := by simp [lam]
    _ ≤ 2 * (lam * (4 * ε ^ 2)) + 2 * weightedApproxError μ n k := by
      gcongr
    _ ≤ 128 * ε ^ 2 + 2 * weightedApproxError μ n k := by
      have hlambound := fourierLaplacianSymbol_le_sixteen k
      have hε2 : 0 ≤ ε ^ 2 := sq_nonneg _
      nlinarith [mul_le_mul_of_nonneg_right hlambound hε2]
    _ = 2 * weightedApproxError μ n k + 128 * ε ^ 2 := by ring

private theorem curlEnergy_eq_pairCurlEnergy (φ : GlobalLinkField) (k : Torus4) :
    fourierFourierCurlEnergy φ k =
      fourierPairCurlEnergy
        (fun i => fourier 1 (torus4Coord k i) - 1)
        (fun i => globalLinkFourierComponent φ i k) := by
  unfold fourierFourierCurlEnergy fourierPairCurlEnergy
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hij : i < j
  · simp only [hij]
    rw [coboundaryFourierComponent_pair φ i j hij k]
    have hneg : -((fourier 1 (torus4Coord k j) - 1) *
          globalLinkFourierComponent φ i k) +
        ((fourier 1 (torus4Coord k i) - 1) *
          globalLinkFourierComponent φ j k) =
        -((fourier 1 (torus4Coord k j) - 1) *
            globalLinkFourierComponent φ i k -
          (fourier 1 (torus4Coord k i) - 1) *
            globalLinkFourierComponent φ j k) := by ring
    rw [hneg, Complex.normSq_neg]
  · simp [hij]

private theorem hodgeSymbol_eq_fourierLaplacian (k : Torus4) :
    fourierHodgeNormSq (fun i => fourier 1 (torus4Coord k i) - 1) =
      fourierLaplacianSymbol k := by
  unfold fourierHodgeNormSq fourierLaplacianSymbol
  apply Finset.sum_congr rfl
  intro i hi
  change Complex.normSq (fourier 1 (torus4Coord k i) - 1) = _
  rw [Complex.normSq_eq_norm_sq]
  have hneg : fourier 1 (torus4Coord k i) - 1 =
      -((1 : ℂ) - fourier 1 (torus4Coord k i)) := by ring
  rw [hneg, norm_neg]

private theorem hodgeGreen_eq_fourierGreen (μ : GlobalLinkField) (k : Torus4) :
    fourierHodgeNormSq (fun i => globalLinkFourierComponent μ i k) /
      fourierLaplacianSymbol k = fourierGreenDensity μ k := by
  unfold fourierGreenDensity
  rw [← Finset.sum_div]
  congr 1
  unfold fourierHodgeNormSq
  apply Finset.sum_congr rfl
  intro i hi
  exact Complex.normSq_eq_norm_sq _

private theorem variationalIntegrand_lower_completion
    (μ φ : GlobalLinkField) (k : Torus4)
    (hpos : 0 < fourierLaplacianSymbol k) :
    2 * (∑ i : Fin 4, globalLinkFourierComponent φ i k *
        conj (globalLinkFourierComponent μ i k)).re - fourierFourierCurlEnergy φ k ≥
      fourierGreenDensity μ k - weightedPotentialError μ φ k := by
  let a : Fin 4 → ℂ := fun i => fourier 1 (torus4Coord k i) - 1
  let u : Fin 4 → ℂ := fun i => globalLinkFourierComponent φ i k
  let m : Fin 4 → ℂ := fun i => globalLinkFourierComponent μ i k
  have hsymbol : fourierHodgeNormSq a = fourierLaplacianSymbol k := by
    exact hodgeSymbol_eq_fourierLaplacian k
  have hlam : 0 < fourierHodgeNormSq a := by rw [hsymbol]; exact hpos
  have hcurl : fourierFourierCurlEnergy φ k = fourierPairCurlEnergy a u := by
    exact curlEnergy_eq_pairCurlEnergy φ k
  have hgreen : fourierHodgeNormSq m / fourierHodgeNormSq a = fourierGreenDensity μ k := by
    rw [hsymbol]
    exact hodgeGreen_eq_fourierGreen μ k
  have hpair : (∑ i : Fin 4, globalLinkFourierComponent φ i k *
      conj (globalLinkFourierComponent μ i k)).re = (fourierHodgePair u m).re := rfl
  have hcomplete := fourierPairCurlEnergy_completion a m u hlam
  rw [hgreen, hsymbol] at hcomplete
  have hnonneg : 0 ≤ Complex.normSq (fourierHodgeInner a u) := Complex.normSq_nonneg _
  have herr : weightedPotentialError μ φ k =
      fourierLaplacianSymbol k * fourierHodgeNormSq
        (fun i => u i - m i / (fourierLaplacianSymbol k : ℂ)) := by
    simp [weightedPotentialError, fourierPotential, fourierHodgeNormSq, u, m]
  rw [herr, hcurl, hpair]
  linarith [hcomplete]

private theorem integrable_fourierVariationalIntegrand (μ φ : GlobalLinkField) :
    Integrable (fun k : Torus4 =>
      2 * (∑ i : Fin 4, globalLinkFourierComponent φ i k *
        conj (globalLinkFourierComponent μ i k)).re -
        fourierFourierCurlEnergy φ k) torus4Haar := by
  have hcomponents (i : Fin 4) :
      Continuous (fun k : Torus4 => globalLinkFourierComponent φ i k *
        conj (globalLinkFourierComponent μ i k)) :=
    (continuous_globalLinkFourierComponent_local φ i).mul
      (continuous_globalLinkFourierComponent_local μ i).star
  have hpair : Continuous (fun k : Torus4 =>
      2 * (∑ i : Fin 4, globalLinkFourierComponent φ i k *
        conj (globalLinkFourierComponent μ i k)).re) := by
    have hsum : Continuous (fun k : Torus4 =>
        ∑ i : Fin 4, globalLinkFourierComponent φ i k *
          conj (globalLinkFourierComponent μ i k)) := by
      apply continuous_finsetSum
      intro i hi
      exact hcomponents i
    exact (Complex.continuous_re.comp hsum).const_mul 2
  have hcurl : Continuous (fourierFourierCurlEnergy φ) := by
    unfold fourierFourierCurlEnergy
    apply continuous_finsetSum
    intro i hi
    apply continuous_finsetSum
    intro j hj
    by_cases hij : i < j
    · simp [hij]
      have hchain := continuous_latticeChainFourierComponent_local
        (globalCoboundary (φ : RealLatticeChain 4)) {i, j}
      have heq : (fun k : Torus4 => Complex.normSq
          (latticeChainFourierComponent
            (globalCoboundary (φ : RealLatticeChain 4)) {i, j} k)) =
          fun k => ‖latticeChainFourierComponent
            (globalCoboundary (φ : RealLatticeChain 4)) {i, j} k‖ ^ 2 := by
        funext k
        exact Complex.normSq_eq_norm_sq _
      rw [heq]
      exact (continuous_norm.comp hchain).pow 2
    · simpa [hij] using (continuous_const : Continuous (fun _ : Torus4 => (0 : ℝ)))
  have hcompact (f : Torus4 → ℝ) (hf : Continuous f) :
      Integrable f torus4Haar := by
    have hrange : IsCompact (Set.range fun k : Torus4 => ‖f k‖) := by
      simpa [Function.comp_def] using isCompact_univ.image (continuous_norm.comp hf)
    rcases hrange.bddAbove with ⟨C, hC⟩
    change ∀ b ∈ Set.range (fun k : Torus4 => ‖f k‖), b ≤ C at hC
    apply Integrable.of_bound hf.measurable.aestronglyMeasurable C
    filter_upwards with k
    exact hC _ ⟨k, rfl⟩
  exact (hcompact _ hpair).sub (hcompact _ hcurl)

private theorem integral_variational_lower_bound
    (μ φ : GlobalLinkField) (n : ℕ) (ε : ℝ) (hε : 0 < ε)
    (happrox : ∀ i k,
      ‖globalLinkFourierComponent φ i k - regularizedPotentialMap μ n i k‖ < ε) :
    fourierGreenQuadratic μ -
        2 * (∫ k : Torus4, weightedApproxError μ n k ∂torus4Haar) -
        128 * ε ^ 2 ≤ globalVariationalObjective μ φ := by
  let f : Torus4 → ℝ := fun k =>
    2 * (∑ i : Fin 4, globalLinkFourierComponent φ i k *
      conj (globalLinkFourierComponent μ i k)).re - fourierFourierCurlEnergy φ k
  let g : Torus4 → ℝ := fun k =>
    fourierGreenDensity μ k -
      (2 * weightedApproxError μ n k + 128 * ε ^ 2)
  have hf : Integrable f torus4Haar := integrable_fourierVariationalIntegrand μ φ
  have hgreen : Integrable (fourierGreenDensity μ) torus4Haar :=
    Fourier.integrable_fourierGreenDensity μ
  have herr : Integrable (weightedApproxError μ n) torus4Haar :=
    integrable_weightedApproxError μ n
  have hconst : Integrable (fun _ : Torus4 => 128 * ε ^ 2) torus4Haar :=
    integrable_const _
  have h2err : Integrable (fun k : Torus4 => 2 * weightedApproxError μ n k)
      torus4Haar := herr.const_mul 2
  have hsum : Integrable (fun k : Torus4 =>
      2 * weightedApproxError μ n k + 128 * ε ^ 2) torus4Haar :=
    h2err.add hconst
  have hg : Integrable g torus4Haar := by
    dsimp [g]
    exact hgreen.sub hsum
  have hpoint : ∀ᵐ k : Torus4 ∂torus4Haar, g k ≤ f k := by
    filter_upwards [FourierVariationalIntegral.ae_symbol_positive] with k hk
    have hcomplete := variationalIntegrand_lower_completion μ φ k hk
    have herror := weightedPotentialError_le_regularized μ φ n ε hε happrox k
    dsimp [f, g]
    nlinarith
  have hint := integral_mono_ae hg hf hpoint
  have hconstInt : (∫ _k : Torus4, 128 * ε ^ 2 ∂torus4Haar) =
      128 * ε ^ 2 := by
    simp [torus4Haar]
  have herrInt : (∫ k : Torus4, 2 * weightedApproxError μ n k ∂torus4Haar) =
      2 * (∫ k : Torus4, weightedApproxError μ n k ∂torus4Haar) := by
    rw [integral_const_mul]
  have hgInt : (∫ k : Torus4, g k ∂torus4Haar) =
      fourierGreenQuadratic μ -
        2 * (∫ k : Torus4, weightedApproxError μ n k ∂torus4Haar) -
        128 * ε ^ 2 := by
    dsimp [g]
    rw [integral_sub hgreen hsum, integral_add h2err hconst, herrInt, hconstInt]
    change fourierGreenQuadratic μ -
      (2 * (∫ k : Torus4, weightedApproxError μ n k ∂torus4Haar) +
        128 * ε ^ 2) = _
    ring
  rw [variational_objective_integral μ φ, ← hgInt]
  exact hint

/-- The regularized Fourier potential, approximated by finite Fourier sums,
attains the Green quadratic in the variational supremum. -/
theorem globallyCoClosed_variational_fourier_lower
    (μ : GlobalLinkField) (hμ : globallyCoClosed μ) :
    fourierGreenQuadratic μ ≤ globalVariationalCovariance μ := by
  apply le_of_forall_pos_le_add
  intro η hη
  have hsmallEvent : ∀ᶠ n : ℕ in atTop,
      (∫ k : Torus4, weightedApproxError μ n k ∂torus4Haar) < η / 8 :=
    (integral_weightedApproxError_tendsto_zero μ).eventually
      (Iio_mem_nhds (by positivity : 0 < η / 8))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hsmallEvent
  let n := N
  have hsmall :
      (∫ k : Torus4, weightedApproxError μ n k ∂torus4Haar) < η / 8 := by
    exact hN N le_rfl
  let ε : ℝ := Real.sqrt (η / 512)
  have hε : 0 < ε := Real.sqrt_pos.2 (by positivity)
  have hεsq : ε ^ 2 = η / 512 := by
    dsimp [ε]
    exact Real.sq_sqrt (by positivity)
  have hconst : 128 * ε ^ 2 = η / 4 := by rw [hεsq]; ring
  obtain ⟨φ, happrox⟩ := exists_globalLinkField_regularizedApprox μ n ε hε
  have hobj := integral_variational_lower_bound μ φ n ε hε happrox
  have hcovUpperSet : BddAbove
      {r : ℝ | ∃ ψ : GlobalLinkField, globalVariationalObjective μ ψ = r} := by
    refine ⟨fourierGreenQuadratic μ, ?_⟩
    rintro r ⟨ψ, rfl⟩
    exact globallyCoClosed_variational_fourier_upper μ ψ hμ
  have hobjLe : globalVariationalObjective μ φ ≤ globalVariationalCovariance μ := by
    rw [globalVariationalCovariance]
    exact le_csSup hcovUpperSet ⟨φ, rfl⟩
  have htarget : fourierGreenQuadratic μ ≤ globalVariationalCovariance μ + η := by
    dsimp [n] at hsmall
    rw [hconst] at hobj
    linarith
  exact htarget

theorem globallyCoClosed_fourier_green_eq_covariance
    (μ : GlobalLinkField) (hμ : globallyCoClosed μ) :
    globalVariationalCovariance μ = fourierGreenQuadratic μ := by
  apply le_antisymm
  · exact globallyCoClosed_covariance_fourier_upper μ hμ
  · exact globallyCoClosed_variational_fourier_lower μ hμ

end FroehlichSpencer.FS82.Infinite.FourierGreenEquality
