/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Gaussian.Fejer
public import FroehlichSpencer.BKT.Gaussian.ExponentialMoment
public import FroehlichSpencer.BKT.Bridge.IntegerGFFMeasure
public import FroehlichSpencer.BKT.Surface.IntegerGFFLaw
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Fejér weighted GFF averages

The averages are the finite-volume quantities in KP §5.1, p. 4. -/

@[expose] public section

namespace FroehlichSpencer.BKT

universe u v

open MeasureTheory Multigraph
open scoped ENNReal

variable {V : Type u} {E : Type v}

/-- The coordinatewise Fejér weight used in the KP §5.1 cell limit. -/
noncomputable def gffFejerWeight [Fintype V] (N : ℕ) (φ : V → ℝ) : ℝ :=
  ∏ j, fejerPolynomial N (φ j)

/-- KP's finite-volume Fejér average, expressed against the candidate rooted
GFF law (KP §5.1, p. 4). -/
noncomputable def gffFejerAverage (G : Multigraph V E) [Fintype V] [Fintype E]
    [DecidableEq V] (hG : G.Connected) (β : ℝ) (hβ : 0 < β) (root : V)
    (g : V → ℝ) (N : ℕ) : ℝ :=
  ∫ φ, Real.exp (pairing φ g) * gffFejerWeight N φ ∂gffMeasure G hG β hβ root

/-- KP's Fourier coefficients have the expected range, including frequencies
outside the degree. -/
theorem fejerFourierCoefficient_mem_unitInterval (N : ℕ) (q : ℤ) :
    fejerFourierCoefficient N q ∈ Set.Icc 0 1 := by
  by_cases hN : N = 0
  · subst N
    by_cases hq : q = 0 <;> simp [fejerFourierCoefficient, hq]
  · have hN' : 0 < N := Nat.pos_of_ne_zero hN
    exact fejerFourierCoefficient_mem_Icc N q hN'

/-- The normalized Fejér polynomial has total mass one on the KP cell. -/
theorem fejerKernel_intervalIntegral (N : ℕ) :
    (1 / (2 * Real.pi)) *
      ∫ x in -Real.pi..Real.pi, fejerPolynomial N x = 1 := by
  rw [fejerPolynomial_intervalIntegral]
  have hpi : (2 * Real.pi) ≠ 0 := ne_of_gt (by positivity)
  field_simp [hpi]

/-- Each KP Fejér polynomial is bounded by a finite constant depending on its
degree. -/
theorem fejerPolynomial_abs_le (N : ℕ) (x : ℝ) :
    |fejerPolynomial N x| ≤ 1 + 2 * N := by
  rw [fejerPolynomial_eq_kp]
  have hsum : |∑ q ∈ Finset.Icc 1 N,
        2 * fejerCosineCoefficient N q * Real.cos ((q : ℝ) * x)| ≤
      ∑ q ∈ Finset.Icc 1 N,
        |2 * fejerCosineCoefficient N q * Real.cos ((q : ℝ) * x)| :=
    Finset.abs_sum_le_sum_abs _ _
  have hterm (q : ℕ) (hq : q ∈ Finset.Icc 1 N) :
      |2 * fejerCosineCoefficient N q * Real.cos ((q : ℝ) * x)| ≤ 2 := by
    have hqN : q ≤ N := (Finset.mem_Icc.mp hq).2
    have hNpos : 0 < N := by
      have hq1 := (Finset.mem_Icc.mp hq).1
      omega
    have hc := fejerCosineCoefficient_mem_Icc N q hNpos hqN
    have hcoef : |fejerCosineCoefficient N q| ≤ 1 := by
      rw [abs_le]
      exact ⟨by linarith [hc.1], hc.2⟩
    have hcos : |Real.cos ((q : ℝ) * x)| ≤ 1 := abs_le.mpr
      ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
    calc
      |2 * fejerCosineCoefficient N q * Real.cos ((q : ℝ) * x)| =
          2 * |fejerCosineCoefficient N q| *
            |Real.cos ((q : ℝ) * x)| := by
              rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      _ ≤ 2 := by
        calc
          2 * |fejerCosineCoefficient N q| *
              |Real.cos ((q : ℝ) * x)| =
              2 * (|fejerCosineCoefficient N q| *
                |Real.cos ((q : ℝ) * x)|) := by ring
          _ ≤ 2 * 1 := mul_le_mul_of_nonneg_left
            (calc
              |fejerCosineCoefficient N q| *
                  |Real.cos ((q : ℝ) * x)| ≤
                  1 * |Real.cos ((q : ℝ) * x)| :=
                    mul_le_mul_of_nonneg_right hcoef (abs_nonneg _)
              _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left hcos (by norm_num)
              _ = 1 := by ring) (by norm_num)
          _ = 2 := by ring
  have hsumle : ∑ q ∈ Finset.Icc 1 N,
      |2 * fejerCosineCoefficient N q * Real.cos ((q : ℝ) * x)| ≤
      2 * N := by
    calc
      _ ≤ ∑ _q ∈ Finset.Icc 1 N, (2 : ℝ) :=
        Finset.sum_le_sum fun q hq => hterm q hq
      _ = 2 * N := by simp; ring
  have hmain := abs_add_le 1
    (∑ q ∈ Finset.Icc 1 N,
      2 * fejerCosineCoefficient N q * Real.cos ((q : ℝ) * x))
  calc
    |1 + ∑ q ∈ Finset.Icc 1 N,
        2 * fejerCosineCoefficient N q * Real.cos ((q : ℝ) * x)| ≤
        1 + |∑ q ∈ Finset.Icc 1 N,
          2 * fejerCosineCoefficient N q * Real.cos ((q : ℝ) * x)| := by
            simpa using hmain
    _ ≤ 1 + 2 * N := by linarith [hsum, hsumle]

/-- The product Fejér weight has a pointwise bound independent of the field. -/
theorem gffFejerWeight_abs_le [Fintype V] (N : ℕ) (φ : V → ℝ) :
    |gffFejerWeight N φ| ≤ (1 + 2 * (N : ℝ)) ^ Fintype.card V := by
  unfold gffFejerWeight
  rw [Finset.abs_prod]
  calc
    ∏ j, |fejerPolynomial N (φ j)| ≤
        ∏ _j : V, ((1 : ℝ) + 2 * (N : ℝ)) := by
      apply Finset.prod_le_prod₀
      · intro j hj
        exact abs_nonneg _
      · intro j hj
        exact fejerPolynomial_abs_le N (φ j)
    _ = (1 + 2 * (N : ℝ)) ^ Fintype.card V := by simp

/-- The arbitrary real observable splits into a zero-sum part and its pinned
root contribution. -/
theorem pairing_eq_zeroSum_root_part [Fintype V] [DecidableEq V]
    (root : V) (g φ : V → ℝ) :
    pairing φ g =
      pairing φ (fun j => g j - if j = root then (∑ k, g k) else 0) +
        φ root * ∑ k, g k := by
  let α : ℝ := ∑ k, g k
  let f : V → ℝ := fun j => g j - if j = root then α else 0
  have hg : g = f + fun j => if j = root then α else 0 := by
    funext j
    by_cases hj : j = root <;> simp [f, hj]
  have hadd (a b : V → ℝ) :
      pairing φ (a + b) = pairing φ a + pairing φ b := by
    unfold pairing
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  have hdelta :
      pairing φ (fun j => if j = root then α else 0) = φ root * α := by
    unfold pairing
    simp [Finset.sum_ite_eq', α]
  calc
    pairing φ g = pairing φ (f + fun j => if j = root then α else 0) := by
      rw [hg]
    _ = pairing φ f + pairing φ (fun j => if j = root then α else 0) := hadd _ _
    _ = pairing φ f + φ root * α := by rw [hdelta]
    _ = pairing φ (fun j => g j - if j = root then (∑ k, g k) else 0) +
          φ root * ∑ k, g k := by simp [f, α]

/-- Removing the root-supported contribution makes an arbitrary observable
zero-sum. -/
theorem sum_rootAdjustedObservable_eq_zero [Fintype V] [DecidableEq V]
    (root : V) (g : V → ℝ) :
    ∑ j, (g j - if j = root then (∑ k, g k) else 0) = 0 := by
  rw [Finset.sum_sub_distrib]
  have hdelta : (∑ j, if j = root then (∑ k, g k) else 0) = ∑ k, g k := by
    simp [Finset.sum_ite_eq']
  rw [hdelta]
  ring

/-- The root exponential, cut off to the KP root interval, is bounded. -/
private theorem rootWindow_exp_bounded [Fintype V] (root : V) (α : ℝ) :
    ∀ φ : V → ℝ,
      ‖(gffRootWindow root).indicator
        (fun ψ => Real.exp (α * ψ root)) φ‖ ≤ Real.exp (|α| * Real.pi) := by
  intro φ
  by_cases hφ : φ ∈ gffRootWindow root
  · have hw : φ ∈ gffRootWindow root := hφ
    change φ root ∈ Set.Ico (-Real.pi) Real.pi at hw
    rw [Set.indicator_of_mem hφ, Real.norm_eq_abs, Real.abs_exp]
    apply Real.exp_le_exp.mpr
    have hwindow := hw
    have hroot : |φ root| ≤ Real.pi := abs_le.mpr
      ⟨hwindow.1, le_of_lt hwindow.2⟩
    calc
      α * φ root ≤ |α * φ root| := le_abs_self _
      _ = |α| * |φ root| := abs_mul _ _
      _ ≤ |α| * Real.pi :=
        mul_le_mul_of_nonneg_left hroot (abs_nonneg _)
  · rw [Set.indicator_of_notMem hφ]
    simp only [Real.norm_eq_abs, abs_zero]
    exact (Real.exp_pos _).le

/-- The density-weighted Fejér integrand is integrable for every real
observable; no neutrality condition on `g` is needed. -/
theorem integrable_gffFejerDensityIntegrand (G : Multigraph V E)
    [Fintype V] [Fintype E] [DecidableEq V] (hG : G.Connected)
    (β : ℝ) (hβ : 0 < β) (root : V) (g : V → ℝ) (N : ℕ) :
    Integrable
      (fun φ => Real.exp (pairing φ g) * gffFejerWeight N φ *
        gffDensity G β root φ)
      (volume : Measure (V → ℝ)) := by
  let α : ℝ := ∑ j, g j
  let f : V → ℝ := fun j => g j - if j = root then α else 0
  have hf : ∑ j, f j = 0 := by
    simp [f, α]
  have hbase := gff_tilted_density_integrable G hG β hβ f hf root
  let r : (V → ℝ) → ℝ := (gffRootWindow root).indicator
    (fun φ => Real.exp (α * φ root))
  let q : (V → ℝ) → ℝ := fun φ => r φ * gffFejerWeight N φ
  have hrmeas : Measurable r := by
    apply Measurable.indicator
    · fun_prop
    · exact measurableSet_Ico.preimage (measurable_pi_apply root)
  have hwmeas : Measurable (fun φ : V → ℝ => gffFejerWeight N φ) := by
    unfold gffFejerWeight fejerPolynomial
    fun_prop
  have hqmeas : Measurable q := by
    exact hrmeas.mul hwmeas
  have hqbound (φ : V → ℝ) :
    ‖q φ‖ ≤ Real.exp (|α| * Real.pi) *
        (1 + 2 * (N : ℝ)) ^ Fintype.card V := by
    dsimp [q]
    rw [abs_mul]
    have hr := rootWindow_exp_bounded root α φ
    rw [Real.norm_eq_abs] at hr
    exact mul_le_mul hr (gffFejerWeight_abs_le N φ)
      (abs_nonneg _) (Real.exp_pos _).le
  have hmul := hbase.mul_bdd hqmeas.aestronglyMeasurable
    (Filter.Eventually.of_forall hqbound)
  exact hmul.congr (ae_of_all _ fun φ => by
    change (Real.exp (pairing φ f) * gffDensity G β root φ) * q φ =
      Real.exp (pairing φ g) * gffFejerWeight N φ * gffDensity G β root φ
    by_cases hφ : φ ∈ gffRootWindow root
    · have hroot : φ root ∈ Set.Ico (-Real.pi) Real.pi := hφ
      dsimp [q, r]
      rw [Set.indicator_of_mem hφ,
        gffDensity_of_root_mem G β root φ hroot]
      have hpair := pairing_eq_zeroSum_root_part root g φ
      dsimp [α, f] at hpair ⊢
      rw [hpair, Real.exp_add]
      ring_nf
    · have hrootnot : φ root ∉ Set.Ico (-Real.pi) Real.pi := by
        exact hφ
      rw [gffDensity_of_root_not_mem G β root φ hrootnot]
      simp [q, r, hφ])

/-- The KP finite-volume Fejér average is integrable under the candidate GFF
law for arbitrary real observables. -/
theorem integrable_gffFejerAverage (G : Multigraph V E)
    [Fintype V] [Fintype E] [DecidableEq V] (hG : G.Connected)
    (β : ℝ) (hβ : 0 < β) (root : V) (g : V → ℝ) (N : ℕ) :
    Integrable (fun φ => Real.exp (pairing φ g) * gffFejerWeight N φ)
      (gffMeasure G hG β hβ root) := by
  apply (integrable_gffMeasure_iff G hG β hβ root
    (fun φ => Real.exp (pairing φ g) * gffFejerWeight N φ)).2
  simpa only [mul_assoc] using
    integrable_gffFejerDensityIntegrand G hG β hβ root g N

/-- The Fejér weight in each coordinate is nonnegative. -/
theorem gffFejerWeight_nonneg [Fintype V] (N : ℕ) (φ : V → ℝ) :
    0 ≤ gffFejerWeight N φ := by
  unfold gffFejerWeight
  apply Finset.prod_nonneg
  intro j hj
  by_cases hN : N = 0
  · subst N
    norm_num [fejerPolynomial]
  · exact fejerPolynomial_nonneg N (Nat.pos_of_ne_zero hN) (φ j)

/-- The Fejér average equals the KP density integral divided by the GFF
partition function, with no omitted cell-volume factor. -/
theorem gffFejerAverage_eq_densityIntegral_div (G : Multigraph V E)
    [Fintype V] [Fintype E] [DecidableEq V] (hG : G.Connected)
    (β : ℝ) (hβ : 0 < β) (root : V) (g : V → ℝ) (N : ℕ) :
    gffFejerAverage G hG β hβ root g N =
      (∫ φ, Real.exp (pairing φ g) * gffFejerWeight N φ *
        gffDensity G β root φ ∂(volume : Measure (V → ℝ))) /
        gffPartitionFunction G β root := by
  exact (gffMeasure_integral_eq_div G hG β hβ root
    (fun φ => Real.exp (pairing φ g) * gffFejerWeight N φ)
    (integrable_gffFejerDensityIntegrand G hG β hβ root g N)).2

/-- The unnormalized zero-observable Fejér integral is strictly positive for
positive degree. -/
theorem gffFejerDensityIntegral_pos (G : Multigraph V E)
    [Fintype V] [Fintype E] [DecidableEq V] (hG : G.Connected)
    (β : ℝ) (hβ : 0 < β) (root : V) (N : ℕ) (hN : 0 < N) :
    0 < ∫ φ, gffFejerWeight N φ * gffDensity G β root φ
      ∂(volume : Measure (V → ℝ)) := by
  have hfi : Integrable
      (fun φ => gffFejerWeight N φ * gffDensity G β root φ)
      (volume : Measure (V → ℝ)) := by
    simpa [pairing] using
      (integrable_gffFejerDensityIntegrand G hG β hβ root (fun _ => 0) N)
  have hnonneg (φ : V → ℝ) :
      0 ≤ gffFejerWeight N φ * gffDensity G β root φ :=
    mul_nonneg (gffFejerWeight_nonneg N φ)
      (gffDensity_nonneg G β root φ)
  apply (integral_pos_iff_support_of_nonneg hnonneg hfi).mpr
  obtain ⟨δ, hδ, hkernel⟩ := exists_fejerPolynomial_pos_radius N hN
  let ε : ℝ := min δ Real.pi / 2
  have hε : 0 < ε := by
    dsimp [ε]
    exact div_pos (lt_min hδ Real.pi_pos) (by norm_num)
  have hεδ : ε ≤ δ := by
    dsimp [ε]
    have := min_le_left δ Real.pi
    linarith
  have hεπ : ε ≤ Real.pi := by
    dsimp [ε]
    have := min_le_right δ Real.pi
    linarith [Real.pi_pos]
  let box : Set (V → ℝ) := Set.univ.pi fun _ : V => Set.Ioo (-ε) ε
  have hbox_pos : 0 < volume box := by
    change 0 < volume (Set.univ.pi fun _ : V => Set.Ioo (-ε) ε)
    rw [Real.volume_pi_Ioo, Finset.prod_const]
    have hwidth : ε - (-ε) = 2 * ε := by ring
    rw [hwidth]
    exact ENNReal.pow_pos (ENNReal.ofReal_pos.mpr (by positivity)) _
  have hbox_support : box ⊆ Function.support
      (fun φ => gffFejerWeight N φ * gffDensity G β root φ) := by
    intro φ hφ
    change gffFejerWeight N φ * gffDensity G β root φ ≠ 0
    have hcoord (j : V) : φ j ∈ Set.Ioo (-ε) ε :=
      (Set.mem_univ_pi.mp hφ) j
    have hcoord_abs (j : V) : |φ j| < ε :=
      abs_lt.mpr (Set.mem_Ioo.mp (hcoord j))
    have hweight : 0 < gffFejerWeight N φ := by
      unfold gffFejerWeight
      apply Finset.prod_pos
      intro j hj
      exact hkernel (φ j) (lt_of_lt_of_le (hcoord_abs j) hεδ)
    have hrootbox : φ root ∈ Set.Ioo (-ε) ε := hcoord root
    have hroot : φ root ∈ Set.Ico (-Real.pi) Real.pi := by
      rcases Set.mem_Ioo.mp hrootbox with ⟨hl, hu⟩
      exact Set.mem_Ico.mpr ⟨by linarith [hεπ], by linarith [hεπ]⟩
    have hdensity : 0 < gffDensity G β root φ := by
      rw [gffDensity_of_root_mem G β root φ hroot]
      exact Real.exp_pos _
    exact ne_of_gt (mul_pos hweight hdensity)
  have hsupp : 0 < volume (Function.support
      (fun φ => gffFejerWeight N φ * gffDensity G β root φ)) :=
    lt_of_lt_of_le hbox_pos (measure_mono hbox_support)
  exact hsupp

/-- The denominator `A_N(0)` in the KP Fejér cell limit is positive for every
positive degree. -/
theorem gffFejerAverage_zero_pos (G : Multigraph V E)
    [Fintype V] [Fintype E] [DecidableEq V] (hG : G.Connected)
    (β : ℝ) (hβ : 0 < β) (root : V) (N : ℕ) (hN : 0 < N) :
    0 < gffFejerAverage G hG β hβ root (fun _ => 0) N := by
  rw [gffFejerAverage_eq_densityIntegral_div G hG β hβ root (fun _ => 0) N]
  apply div_pos
  · simpa [pairing] using gffFejerDensityIntegral_pos G hG β hβ root N hN
  · exact gffPartitionFunction_pos G hG β hβ root

/-- The KP ratio in the finite-dimensional Fejér cell limit. -/
noncomputable def gffFejerRatio (G : Multigraph V E) [Fintype V]
    [Fintype E] [DecidableEq V] (hG : G.Connected) (β : ℝ) (hβ : 0 < β)
    (root : V) (g : V → ℝ) (N : ℕ) : ℝ :=
  gffFejerAverage G hG β hβ root g N /
    gffFejerAverage G hG β hβ root (fun _ => 0) N

/-- For the zero observable, the KP Fejér ratio is exactly one at every
positive degree. -/
theorem gffFejerRatio_zero (G : Multigraph V E) [Fintype V]
    [Fintype E] [DecidableEq V] (hG : G.Connected) (β : ℝ) (hβ : 0 < β)
    (root : V) (N : ℕ) (hN : 0 < N) :
    gffFejerRatio G hG β hβ root (fun _ => 0) N = 1 := by
  unfold gffFejerRatio
  exact div_self (ne_of_gt (gffFejerAverage_zero_pos G hG β hβ root N hN))

/-- The product Fejér weight is periodic under independent integer multiples
of `2π` in the coordinates. -/
theorem gffFejerWeight_add_two_pi_int [Fintype V] (N : ℕ) (m : V → ℤ)
    (φ : V → ℝ) :
    gffFejerWeight N (fun j => φ j + 2 * Real.pi * m j) =
      gffFejerWeight N φ := by
  unfold gffFejerWeight
  apply Finset.prod_congr rfl
  intro j hj
  exact fejerPolynomial_add_two_pi_int N (m j) (φ j)

/-- The KP integer-field exponential moment selected by the Fejér cell limit,
at inverse temperature `(2π)² β` and observable `2π g` (KP §5.1, p. 4). -/
noncomputable def gffFejerIGFFTarget (G : Multigraph V E) [Fintype V]
    [Fintype E] [DecidableEq V] (hG : G.Connected) (β : ℝ) (hβ : 0 < β)
    (root : V) (g : V → ℝ) : ℝ :=
  igffExpectation G hG ((2 * Real.pi) ^ 2 * β)
    (mul_pos (sq_pos_of_ne_zero (by positivity)) hβ) root
    (fun m => Real.exp (pairing (fun j => (m.1 j : ℝ))
      (fun j => 2 * Real.pi * g j)))

/-- The candidate internal target is exactly the rooted IGFF expectation of
`exp (2π ⟨m,g⟩)` at inverse temperature `(2π)² β`. -/
theorem gffFejerIGFFTarget_eq_kp (G : Multigraph V E) [Fintype V]
    [Fintype E] [DecidableEq V] (hG : G.Connected) (β : ℝ) (hβ : 0 < β)
    (root : V) (g : V → ℝ) :
    gffFejerIGFFTarget G hG β hβ root g =
      igffExpectation G hG ((2 * Real.pi) ^ 2 * β)
        (mul_pos (sq_pos_of_ne_zero (by positivity)) hβ) root
        (fun m => Real.exp (2 * Real.pi * pairing
          (fun j => (m.1 j : ℝ)) g)) := by
  unfold gffFejerIGFFTarget
  congr 1
  funext m
  congr 1
  unfold pairing
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/--
The same KP target written as an ENNReal integral against the
`integerGFFLaw` carrier.
-/
noncomputable def gffFejerSourceTarget (G : Multigraph V E) [Fintype V]
    [Fintype E] [DecidableEq V] (hG : G.Connected) (β : ℝ) (hβ : 0 < β)
    (root : V) (g : V → ℝ) : ENNReal :=
  ∫⁻ m, ENNReal.ofReal (Real.exp (2 * Real.pi *
    pairing (fun j => (m j : ℝ)) g)) ∂integerGFFLaw G hG
      ((2 * Real.pi) ^ 2 * β)
      (mul_pos (sq_pos_of_ne_zero (by positivity)) hβ) root

/--
The carrier target is definitionally the KP exponential moment
integral with the source normalization `(2π)² β`.
-/
theorem gffFejerSourceTarget_eq_kp (G : Multigraph V E) [Fintype V]
    [Fintype E] [DecidableEq V] (hG : G.Connected) (β : ℝ) (hβ : 0 < β)
    (root : V) (g : V → ℝ) :
    gffFejerSourceTarget G hG β hβ root g =
      ∫⁻ m, ENNReal.ofReal (Real.exp (2 * Real.pi *
        pairing (fun j => (m j : ℝ)) g)) ∂integerGFFLaw G hG
          ((2 * Real.pi) ^ 2 * β)
          (mul_pos (sq_pos_of_ne_zero (by positivity)) hβ) root := rfl

/-- The finite-volume Fejér average is exactly the GFF expectation from the
definition; this characterization fixes the KP normalization. -/
theorem gffFejerAverage_eq_integral (G : Multigraph V E) [Fintype V]
    [Fintype E] [DecidableEq V] (hG : G.Connected) (β : ℝ) (hβ : 0 < β)
    (root : V) (g : V → ℝ) (N : ℕ) :
    gffFejerAverage G hG β hβ root g N =
      ∫ φ, Real.exp (pairing φ g) *
        ∏ j, fejerPolynomial N (φ j) ∂gffMeasure G hG β hβ root := by
  rfl

end FroehlichSpencer.BKT

end
