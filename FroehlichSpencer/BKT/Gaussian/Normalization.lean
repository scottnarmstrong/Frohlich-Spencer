/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Gaussian.FreeField
public import FroehlichSpencer.BKT.Gaussian.OneDimensionalIntegral
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Normalization of the rooted finite-volume Gaussian free field

The proofs use the connected-graph Poincaré estimate to dominate the rooted
density by a product of one-dimensional Gaussian functions.
-/

@[expose] public section

namespace FroehlichSpencer.BKT

universe u v

open MeasureTheory Multigraph
open Real

variable {V : Type u} {E : Type v}

/-- The Poincaré constant used for the Gaussian majorant. -/
noncomputable def gffPoincareConstant (V : Type u) [Fintype V] : ℝ :=
  (Fintype.card V : ℝ) * (4 : ℝ) ^ Fintype.card V

/-- The Gaussian decay rate obtained from the Poincaré inequality. -/
noncomputable def gffGaussianRate (V : Type u) [Fintype V] (β : ℝ) : ℝ :=
  β / (4 * gffPoincareConstant V)

/-- The multiplicative constant accounting for the bounded root coordinate. -/
noncomputable def gffGaussianConstant (V : Type u) [Fintype V] (β : ℝ) : ℝ :=
  Real.exp (β * (Fintype.card V : ℝ) * Real.pi ^ 2 /
    (2 * gffPoincareConstant V))

/-- An integrable product-Gaussian majorant for the rooted density. -/
noncomputable def gffGaussianMajorant (V : Type u) [Fintype V] (β : ℝ)
    (φ : V → ℝ) : ℝ :=
  gffGaussianConstant V β *
    ∏ j, Real.exp (-gffGaussianRate V β * (φ j) ^ 2)

/-- The sum of the coordinate Gaussian exponents is the corresponding
quadratic exponential. -/
theorem prod_gff_exp_eq_exp_sum (V : Type u) [Fintype V] (a : ℝ)
    (φ : V → ℝ) :
    ∏ j, Real.exp (-a * (φ j) ^ 2) =
      Real.exp (-a * ∑ j, (φ j) ^ 2) := by
  rw [← Real.exp_sum]
  congr 1
  rw [Finset.mul_sum]

/-- The product-Gaussian majorant is nonnegative. -/
theorem gffGaussianMajorant_nonneg (V : Type u) [Fintype V]
    (β : ℝ) (φ : V → ℝ) : 0 ≤ gffGaussianMajorant V β φ := by
  unfold gffGaussianMajorant
  exact mul_nonneg (Real.exp_pos _).le
    (Finset.prod_nonneg fun _ _ => (Real.exp_pos _).le)

/-- The product-Gaussian majorant is integrable with respect to Lebesgue
measure on the finite product `V → ℝ`. -/
theorem integrable_gffGaussianMajorant (V : Type u) [Fintype V]
    (hV : Nonempty V) (β : ℝ) (hβ : 0 < β) :
    Integrable (gffGaussianMajorant V β) (volume : Measure (V → ℝ)) := by
  have hcard : 0 < gffPoincareConstant V := by
    dsimp [gffPoincareConstant]
    exact mul_pos (by exact_mod_cast Fintype.card_pos_iff.mpr hV)
      (pow_pos (by norm_num) _)
  have ha : 0 < gffGaussianRate V β :=
    div_pos hβ (mul_pos (by norm_num) hcard)
  rw [MeasureTheory.volume_pi]
  unfold gffGaussianMajorant
  exact (Integrable.fintype_prod fun _ : V =>
    integrableRealGaussian ha).const_mul (gffGaussianConstant V β)

/-- On a connected graph and inside the root window, the energy exponent is
bounded by the product-Gaussian exponent. -/
theorem gff_exponent_le_majorant (G : Multigraph V E) [Fintype V]
    [Fintype E] [DecidableEq V] (hG : G.Connected) (β : ℝ) (hβ : 0 < β)
    (root : V) (φ : V → ℝ)
    (hroot : φ root ∈ Set.Ico (-Real.pi) Real.pi) :
    -(β / 2) * G.energy φ ≤
      β * (Fintype.card V : ℝ) * Real.pi ^ 2 /
          (2 * gffPoincareConstant V) -
        gffGaussianRate V β * ∑ j, (φ j) ^ 2 := by
  let C : ℝ := gffPoincareConstant V
  have hn : 0 < (Fintype.card V : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr hG.nonempty
  have hC : 0 < C := by
    dsimp [C, gffPoincareConstant]
    exact mul_pos hn (pow_pos (by norm_num) _)
  have hP := G.poincare_bound hG root φ
  change (∑ j, (φ j - φ root) ^ 2) ≤ C * G.energy φ at hP
  have hwindow : -Real.pi ≤ φ root ∧ φ root < Real.pi := hroot
  have hrootAbs : |φ root| ≤ Real.pi := abs_le.mpr
    ⟨hwindow.1, le_of_lt hwindow.2⟩
  have hrootSq : (φ root) ^ 2 ≤ Real.pi ^ 2 := by
    have hprod := mul_nonneg (sub_nonneg.mpr hrootAbs)
      (add_nonneg (le_of_lt Real.pi_pos) (abs_nonneg (φ root)))
    nlinarith [sq_abs (φ root)]
  have hcoord :
      (∑ j, (φ j) ^ 2) / 2 - (Fintype.card V : ℝ) * (φ root) ^ 2 ≤
        ∑ j, (φ j - φ root) ^ 2 := by
    calc
      (∑ j, (φ j) ^ 2) / 2 - (Fintype.card V : ℝ) * (φ root) ^ 2 =
          ∑ j, ((φ j) ^ 2 / 2 - (φ root) ^ 2) := by
            rw [Finset.sum_sub_distrib, Finset.sum_div, Finset.sum_const]
            simp only [Finset.card_univ, nsmul_eq_mul]
      _ ≤ ∑ j, (φ j - φ root) ^ 2 :=
        Finset.sum_le_sum fun j _ => by
          nlinarith [sq_nonneg (φ j - 2 * φ root)]
  have hrootTerm :
      (Fintype.card V : ℝ) * (φ root) ^ 2 ≤
        (Fintype.card V : ℝ) * Real.pi ^ 2 :=
    mul_le_mul_of_nonneg_left hrootSq hn.le
  have hsum : (∑ j, (φ j) ^ 2) ≤
      2 * (C * G.energy φ + (Fintype.card V : ℝ) * Real.pi ^ 2) := by
    linarith only [hcoord, hP, hrootTerm]
  let a : ℝ := β / (4 * C)
  have ha : 0 < a := by
    dsimp [a]
    exact div_pos hβ (mul_pos (by norm_num) hC)
  have hmul := mul_le_mul_of_nonneg_left hsum ha.le
  have heq : a * (2 * (C * G.energy φ +
      (Fintype.card V : ℝ) * Real.pi ^ 2)) =
      β / 2 * G.energy φ + β * (Fintype.card V : ℝ) * Real.pi ^ 2 /
        (2 * C) := by
    dsimp [a]
    field_simp [ne_of_gt hC]
    ring
  change -(β / 2) * G.energy φ ≤
    β * (Fintype.card V : ℝ) * Real.pi ^ 2 / (2 * C) -
      (β / (4 * C)) * ∑ j, (φ j) ^ 2
  rw [heq] at hmul
  linarith only [hmul]

/-- On a connected graph, the rooted density is pointwise below the
product-Gaussian majorant. -/
theorem gffDensity_le_gaussianMajorant (G : Multigraph V E) [Fintype V]
    [Fintype E] [DecidableEq V] (hG : G.Connected) (β : ℝ) (hβ : 0 < β)
    (root : V) (φ : V → ℝ) :
    gffDensity G β root φ ≤ gffGaussianMajorant V β φ := by
  by_cases hroot : φ root ∈ Set.Ico (-Real.pi) Real.pi
  · rw [gffDensity_of_root_mem G β root φ hroot, gffGaussianMajorant,
      prod_gff_exp_eq_exp_sum, gffGaussianConstant, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have he := gff_exponent_le_majorant G hG β hβ root φ hroot
    dsimp [gffGaussianRate, gffPoincareConstant] at he ⊢
    linarith only [he]
  · rw [gffDensity_of_root_not_mem G β root φ hroot]
    exact gffGaussianMajorant_nonneg V β φ

/-- The rooted density is pointwise nonnegative. -/
theorem gffDensity_nonneg (G : Multigraph V E) [Fintype E]
    [DecidableEq V] (β : ℝ) (root : V) (φ : V → ℝ) :
    0 ≤ gffDensity G β root φ := by
  by_cases hφ : φ root ∈ Set.Ico (-Real.pi) Real.pi
  · rw [gffDensity_of_root_mem G β root φ hφ]
    exact (Real.exp_pos _).le
  · rw [gffDensity_of_root_not_mem G β root φ hφ]

/-- The candidate rooted density is measurable. -/
theorem measurable_gffDensity (G : Multigraph V E) [Fintype V]
    [Fintype E] [DecidableEq V] (β : ℝ) (root : V) :
    Measurable (gffDensity G β root) := by
  have henergy : Measurable (fun φ : V → ℝ => G.energy φ) := by
    unfold energy grad
    fun_prop
  have hwindow : MeasurableSet (gffRootWindow root) := by
    unfold gffRootWindow
    exact measurableSet_Ico.preimage (measurable_pi_apply root)
  have hweight : Measurable (fun φ : V → ℝ =>
      Real.exp (-(β / 2) * G.energy φ)) :=
    (measurable_const.mul henergy).exp
  exact hweight.indicator hwindow

/-- The rooted density is integrable on a connected finite graph, KP (1.3),
p. 2. -/
theorem integrable_gffDensity (G : Multigraph V E) [Fintype V]
    [Fintype E] [DecidableEq V] (hG : G.Connected) (β : ℝ) (hβ : 0 < β)
    (root : V) :
    Integrable (gffDensity G β root) (volume : Measure (V → ℝ)) := by
  have hmajor := integrable_gffGaussianMajorant V hG.nonempty β hβ
  refine hmajor.mono' (measurable_gffDensity G β root).aestronglyMeasurable ?_
  filter_upwards [] with φ
  rw [Real.norm_eq_abs, abs_of_nonneg (gffDensity_nonneg G β root φ)]
  exact gffDensity_le_gaussianMajorant G hG β hβ root φ

/-- The rooted partition function is strictly positive on a connected graph,
KP (1.3), p. 2. -/
theorem gffPartitionFunction_pos (G : Multigraph V E) [Fintype V]
    [Fintype E] [DecidableEq V] (hG : G.Connected) (β : ℝ) (hβ : 0 < β)
    (root : V) : 0 < gffPartitionFunction G β root := by
  rw [gffPartitionFunction_eq_integral]
  apply (integral_pos_iff_support_of_nonneg
    (fun φ => gffDensity_nonneg G β root φ)
    (integrable_gffDensity G hG β hβ root)).mpr
  let box : Set (V → ℝ) := Set.univ.pi fun _ : V =>
    Set.Ioo (-Real.pi / 2) (Real.pi / 2)
  have hbox_pos : 0 < volume box := by
    change 0 < volume (Set.univ.pi fun _ : V =>
      Set.Ioo (-Real.pi / 2) (Real.pi / 2))
    rw [Real.volume_pi_Ioo]
    rw [Finset.prod_const]
    have hwidth : Real.pi / 2 - (-Real.pi / 2) = Real.pi := by ring
    rw [hwidth]
    rw [← ENNReal.ofReal_pow Real.pi_pos.le]
    exact ENNReal.ofReal_pos.mpr (pow_pos Real.pi_pos _)
  have hbox_support : box ⊆ Function.support (gffDensity G β root) := by
    intro φ hφ
    change gffDensity G β root φ ≠ 0
    have hrootbox : φ root ∈ Set.Ioo (-Real.pi / 2) (Real.pi / 2) :=
      (Set.mem_univ_pi.mp hφ) root
    have hroot : φ root ∈ Set.Ico (-Real.pi) Real.pi := by
      rcases Set.mem_Ioo.mp hrootbox with ⟨hl, hu⟩
      exact Set.mem_Ico.mpr ⟨by linarith [Real.pi_pos], by linarith⟩
    rw [gffDensity_of_root_mem G β root φ hroot]
    exact (Real.exp_pos _).ne'
  have hsupport_pos :
      0 < volume (Function.support (gffDensity G β root)) :=
    lt_of_lt_of_le hbox_pos (measure_mono hbox_support)
  exact hsupport_pos

/-- The unnormalized measure associated with the rooted KP density (1.3),
p. 2. -/
noncomputable def gffDensityMeasure (G : Multigraph V E) [Fintype V]
    [Fintype E] [DecidableEq V] (β : ℝ) (root : V) : Measure (V → ℝ) :=
  volume.withDensity (fun φ => ENNReal.ofReal (gffDensity G β root φ))

/-- The mass of the unnormalized density measure is the KP partition integral
(1.3), p. 2. -/
theorem gffDensityMeasure_univ (G : Multigraph V E) [Fintype V]
    [Fintype E] [DecidableEq V] (hG : G.Connected) (β : ℝ) (hβ : 0 < β)
    (root : V) :
    gffDensityMeasure G β root Set.univ =
      ENNReal.ofReal (gffPartitionFunction G β root) := by
  rw [gffDensityMeasure, withDensity_apply _ MeasurableSet.univ]
  simpa [gffPartitionFunction] using
    (ofReal_integral_eq_lintegral_ofReal
      (integrable_gffDensity G hG β hβ root)
      (ae_of_all _ fun φ => gffDensity_nonneg G β root φ)).symm

/-- The normalized rooted Gaussian free field law, KP (1.3), p. 2. -/
noncomputable def gffMeasure (G : Multigraph V E) [Fintype V] [Fintype E]
    [DecidableEq V] (_hG : G.Connected) (β : ℝ) (_hβ : 0 < β) (root : V) :
    Measure (V → ℝ) :=
  (ENNReal.ofReal (gffPartitionFunction G β root))⁻¹ •
    gffDensityMeasure G β root

/-- The candidate rooted Gaussian free field is a probability measure. -/
instance gffMeasure_isProbabilityMeasure (G : Multigraph V E) [Fintype V]
    [Fintype E] [DecidableEq V] (hG : G.Connected) (β : ℝ) (hβ : 0 < β)
    (root : V) : IsProbabilityMeasure (gffMeasure G hG β hβ root) := by
  apply isProbabilityMeasure_iff.mpr
  rw [gffMeasure, Measure.smul_apply,
    gffDensityMeasure_univ G hG β hβ root]
  exact ENNReal.inv_mul_cancel
    (ENNReal.ofReal_ne_zero_iff.mpr (gffPartitionFunction_pos G hG β hβ root))
    ENNReal.ofReal_ne_top

/-- Integrability under the normalized candidate law is equivalent to
integrability after multiplying by its density. -/
theorem integrable_gffMeasure_iff (G : Multigraph V E) [Fintype V]
    [Fintype E] [DecidableEq V] (hG : G.Connected) (β : ℝ) (hβ : 0 < β)
    (root : V) (F : (V → ℝ) → ℝ) :
    Integrable F (gffMeasure G hG β hβ root) ↔
      Integrable (fun φ => F φ * gffDensity G β root φ)
        (volume : Measure (V → ℝ)) := by
  rw [gffMeasure,
    integrable_inv_smul_measure
      (ENNReal.ofReal_ne_zero_iff.mpr (gffPartitionFunction_pos G hG β hβ root))
      ENNReal.ofReal_ne_top,
    gffDensityMeasure]
  have hweight_lt : ∀ᵐ φ ∂(volume : Measure (V → ℝ)),
      ENNReal.ofReal (gffDensity G β root φ) < ⊤ := by
    filter_upwards [] with φ
    exact lt_top_iff_ne_top.mpr ENNReal.ofReal_ne_top
  rw [integrable_withDensity_iff
    ((measurable_gffDensity G β root).ennreal_ofReal) hweight_lt]
  have hdensity (φ : V → ℝ) :
      (ENNReal.ofReal (gffDensity G β root φ)).toReal =
        gffDensity G β root φ :=
    ENNReal.toReal_ofReal (gffDensity_nonneg G β root φ)
  have hfun : (fun φ => F φ *
      (ENNReal.ofReal (gffDensity G β root φ)).toReal) =
      (fun φ => F φ * gffDensity G β root φ) := by
    funext φ
    rw [hdensity]
  rw [hfun]

/-- Integrating an integrable function against the normalized candidate law
is integration against the KP density divided by its partition function. -/
theorem gffMeasure_integral_eq_div (G : Multigraph V E) [Fintype V]
    [Fintype E] [DecidableEq V] (hG : G.Connected) (β : ℝ) (hβ : 0 < β)
    (root : V) (F : (V → ℝ) → ℝ)
    (hF : Integrable (fun φ => F φ * gffDensity G β root φ)
      (volume : Measure (V → ℝ))) :
    Integrable F (gffMeasure G hG β hβ root) ∧
    ∫ φ, F φ ∂gffMeasure G hG β hβ root =
      (∫ φ, F φ * gffDensity G β root φ ∂(volume : Measure (V → ℝ))) /
        gffPartitionFunction G β root := by
  constructor
  · exact (integrable_gffMeasure_iff G hG β hβ root F).2 hF
  · have hweight_lt : ∀ᵐ φ ∂(volume : Measure (V → ℝ)),
        ENNReal.ofReal (gffDensity G β root φ) < ⊤ := by
      filter_upwards [] with φ
      exact lt_top_iff_ne_top.mpr ENNReal.ofReal_ne_top
    have hcoe : ∀ φ : V → ℝ,
        (ENNReal.ofReal (gffDensity G β root φ)).toReal =
          gffDensity G β root φ :=
      fun φ => ENNReal.toReal_ofReal (gffDensity_nonneg G β root φ)
    rw [gffMeasure, integral_smul_measure, gffDensityMeasure,
      integral_withDensity_eq_integral_toReal_smul
        ((measurable_gffDensity G β root).ennreal_ofReal) hweight_lt F]
    rw [integral_congr_ae (ae_of_all _ fun φ => by
      rw [hcoe φ, smul_eq_mul, mul_comm])]
    rw [ENNReal.toReal_inv, ENNReal.toReal_ofReal
      (le_of_lt (gffPartitionFunction_pos G hG β hβ root))]
    simp only [smul_eq_mul]
    rw [div_eq_mul_inv]
    ring

end FroehlichSpencer.BKT
