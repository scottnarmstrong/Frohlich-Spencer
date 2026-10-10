/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Clock.Disorder.GridLocalFactor
public import FroehlichSpencer.BKT.Clock.Disorder.GridOffsetLaw
public import FroehlichSpencer.BKT.Generic.Moment.Branch
import Mathlib.Tactic

/-!
# The branch bound of the real shift on the compact clock box

The compact analogue of `Generic/Moment/Branch.lean`'s `integral_shiftProduct_ge` (FS81
(6.28)–(6.39)), for the clock weight `w = exp(β cos(z/n))` on the compact box measure
`gridBoxMeasure`. For one ensemble `N` of renormalized densities, with waves `b(ϱ)` and activities
`|z(ϱ)| ≤ 1/8`, the branch bound (`integral_gridShiftProduct_ge`) is

`e^{−κ‖θ‖² − ∑_ϱ err(ϱ)} ∫ ρ₀ Π₀ dν ≤ ∫ ρ_θ Π₁ dν`,

with `ρ_θ = compactClockBondProduct (· ) θ` and `Π_t = shiftProduct … t`. The proof is the
generic one:
* the curvature shift of the edge weights (`clockDensity_shift_lower`);
* the per-factor Taylor step for the local strip weight (`one_add_mul_lineFactor_ge_loc`);
* odd-exponent symmetrization under the inversion-invariant box measure
  (`integral_ge_of_odd_exponent_of_negInvariant`).
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Clock.Disorder

open MeasureTheory Complex
open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Clock.Periodic
open FroehlichSpencer.BKT.Clock.Compact
open FroehlichSpencer.BKT.Generic

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V]

omit [DecidableEq V] in
/-- The clock local factor is continuous in the edge argument and the phase. -/
theorem continuous_localFactor_clock (β n : ℝ) (b : E → ℝ)
    {X : Type*} [TopologicalSpace X] {x : X → E → ℝ} (hx : Continuous x) {ph : X → ℝ}
    (hph : Continuous ph) :
    Continuous fun p => localFactor (clockEdgeWeight β n) (clockShiftCost β n) b (x p) (ph p) := by
  have hθc : Continuous fun p => ((ph p : ℝ) : ℂ) := Complex.continuous_ofReal.comp hph
  unfold localFactor normalizedEdgeRatio
  refine Continuous.div_const (Continuous.add ?_ ?_) 2
  · exact (Complex.continuous_exp.comp (continuous_const.mul hθc)).mul
      (((continuous_edgeRatio_clock β n b).comp hx).mul continuous_const)
  · exact (Complex.continuous_exp.comp (continuous_const.mul hθc).neg).mul
      (((continuous_edgeRatio_clock β n (-b)).comp hx).mul continuous_const)

omit [DecidableEq V] in
theorem continuous_lineFactor_clock (β n : ℝ) (G : Multigraph V E) (b : E → ℝ) (θ : E → ℝ)
    (ϱ : V → ℤ) (s t : ℝ) :
    Continuous fun φ : V → ℝ =>
      lineFactor (clockEdgeWeight β n) (clockShiftCost β n) b (G.grad φ) θ
        (∑ j, φ j * (ϱ j : ℝ)) s t := by
  unfold lineFactor
  refine Complex.continuous_re.comp (continuous_localFactor_clock β n b ?_ ?_)
  · refine continuous_pi fun e => ?_
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Multigraph.grad]
    exact ((continuous_apply (G.src e)).sub (continuous_apply (G.tgt e))).add continuous_const
  · exact (continuous_finsetSum _ fun j _ => (continuous_apply j).mul continuous_const).add
      continuous_const

theorem abs_lineFactor_clock_le_one {β n W : ℝ} (hβ : 0 ≤ β) (hn : 0 < n) (hW : 0 ≤ W)
    (b : E → ℝ) (hb : ∀ e, |b e| ≤ W) (x y : E → ℝ) (ph s t : ℝ) :
    |lineFactor (clockEdgeWeight β n) (clockShiftCost β n) b x y ph s t| ≤ 1 :=
  (Complex.abs_re_le_norm _).trans
    (norm_localFactor_le_one (clockEdgeWeight_isLocalStripWeight hβ hn hW).ratio_le b _ hb _)

theorem one_add_mul_lineFactor_clock_ge {β n W : ℝ} (hβ : 0 ≤ β) (hn : 0 < n) (hW : 0 ≤ W)
    (b : E → ℝ) (hb : ∀ e, |b e| ≤ W) {z : ℝ} (hz : |z| ≤ 1 / 8) (x y : E → ℝ) (ph s t : ℝ) :
    7 / 8 ≤ 1 + z * lineFactor (clockEdgeWeight β n) (clockShiftCost β n) b x y ph s t := by
  have h1 := abs_lineFactor_clock_le_one hβ hn hW b hb x y ph s t
  have h2 : |z * lineFactor (clockEdgeWeight β n) (clockShiftCost β n) b x y ph s t| ≤ 1 / 8 := by
    rw [abs_mul]
    calc _ ≤ 1 / 8 * 1 := mul_le_mul hz h1 (abs_nonneg _) (by norm_num)
      _ = 1 / 8 := mul_one _
  linarith [neg_abs_le (z * lineFactor (clockEdgeWeight β n) (clockShiftCost β n) b x y ph s t)]

omit [DecidableEq V] in
theorem shiftProduct_clock_pos {β n W : ℝ} (hβ : 0 ≤ β) (hn : 0 < n) (hW : 0 ≤ W)
    (G : Multigraph V E) (N : Finset (V → ℤ)) (b : (V → ℤ) → E → ℝ)
    (hb : ∀ ϱ ∈ N, ∀ e, |b ϱ e| ≤ W) (z : (V → ℤ) → ℝ) (hz : ∀ ϱ ∈ N, |z ϱ| ≤ 1 / 8)
    (θ : E → ℝ) (s : (V → ℤ) → ℝ) (t : ℝ) (φ : V → ℝ) :
    0 < shiftProduct G (clockEdgeWeight β n) (clockShiftCost β n) N b z θ s t φ :=
  Finset.prod_pos fun ϱ hϱ => lt_of_lt_of_le (by norm_num)
    (one_add_mul_lineFactor_clock_ge hβ hn hW (b ϱ) (hb ϱ hϱ) (hz ϱ hϱ) _ _ _ _ _)

omit [DecidableEq V] in
theorem abs_shiftProduct_clock_le {β n W : ℝ} (hβ : 0 ≤ β) (hn : 0 < n) (hW : 0 ≤ W)
    (G : Multigraph V E) (N : Finset (V → ℤ)) (b : (V → ℤ) → E → ℝ)
    (hb : ∀ ϱ ∈ N, ∀ e, |b ϱ e| ≤ W) (z : (V → ℤ) → ℝ) (hz : ∀ ϱ ∈ N, |z ϱ| ≤ 1 / 8)
    (θ : E → ℝ) (s : (V → ℤ) → ℝ) (t : ℝ) (φ : V → ℝ) :
    |shiftProduct G (clockEdgeWeight β n) (clockShiftCost β n) N b z θ s t φ| ≤
      (9 / 8 : ℝ) ^ N.card := by
  unfold shiftProduct
  rw [Finset.abs_prod, ← Finset.prod_const]
  refine Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun ϱ hϱ => ?_
  have h1 := abs_lineFactor_clock_le_one hβ hn hW (b ϱ) (hb ϱ hϱ) (G.grad φ) θ
    (∑ j, φ j * (ϱ j : ℝ)) (s ϱ) t
  have h2 : |z ϱ * lineFactor (clockEdgeWeight β n) (clockShiftCost β n) (b ϱ) (G.grad φ) θ
      (∑ j, φ j * (ϱ j : ℝ)) (s ϱ) t| ≤ 1 / 8 := by
    rw [abs_mul]
    calc _ ≤ 1 / 8 * 1 := mul_le_mul (hz ϱ hϱ) h1 (abs_nonneg _) (by norm_num)
      _ = 1 / 8 := mul_one _
  calc _ ≤ |(1 : ℝ)| + |z ϱ * lineFactor (clockEdgeWeight β n) (clockShiftCost β n) (b ϱ)
        (G.grad φ) θ (∑ j, φ j * (ϱ j : ℝ)) (s ϱ) t| := abs_add_le _ _
    _ ≤ 9 / 8 := by rw [abs_one]; linarith

omit [DecidableEq V] in
theorem continuous_shiftProduct_clock (β n : ℝ) (G : Multigraph V E) (N : Finset (V → ℤ))
    (b : (V → ℤ) → E → ℝ) (z : (V → ℤ) → ℝ) (θ : E → ℝ) (s : (V → ℤ) → ℝ) (t : ℝ) :
    Continuous (shiftProduct G (clockEdgeWeight β n) (clockShiftCost β n) N b z θ s t) := by
  unfold shiftProduct
  exact continuous_finsetProd _ fun ϱ _ => continuous_const.add (continuous_const.mul
    (continuous_lineFactor_clock β n G (b ϱ) θ ϱ (s ϱ) t))

omit [DecidableEq V] in
/-- A bounded continuous multiple of the offset density is integrable on the box. -/
theorem integrable_bondProduct_mul_shiftProduct {β n W : ℝ} (hβ : 0 ≤ β) (hn : 0 < n)
    (hW : 0 ≤ W) (G : Multigraph V E) (r : E → ℝ) (N : Finset (V → ℤ)) (b : (V → ℤ) → E → ℝ)
    (hb : ∀ ϱ ∈ N, ∀ e, |b ϱ e| ≤ W) (z : (V → ℤ) → ℝ) (hz : ∀ ϱ ∈ N, |z ϱ| ≤ 1 / 8)
    (θ : E → ℝ) (s : (V → ℤ) → ℝ) (t : ℝ) :
    Integrable (fun φ => compactClockBondProduct G β n φ r *
      shiftProduct G (clockEdgeWeight β n) (clockShiftCost β n) N b z θ s t φ)
      (gridBoxMeasure n V) := by
  refine Integrable.of_bound
    (((continuous_compactClockBondProduct G β n r).mul
      (continuous_shiftProduct_clock β n G N b z θ s t)).aestronglyMeasurable)
    (Real.exp (β * Fintype.card E) * (9 / 8 : ℝ) ^ N.card) (ae_of_all _ fun φ => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (compactClockBondProduct_pos G β n φ r)]
  exact mul_le_mul (compactClockBondProduct_le G hβ n φ r)
    (abs_shiftProduct_clock_le hβ hn hW G N b hb z hz θ s t φ) (abs_nonneg _) (Real.exp_pos _).le

omit [DecidableEq V] in
theorem shiftProduct_clock_zero_neg {β n W : ℝ} (hβ : 0 ≤ β) (hn : 0 < n) (hW : 0 ≤ W)
    (G : Multigraph V E) (N : Finset (V → ℤ)) (b : (V → ℤ) → E → ℝ)
    (hb : ∀ ϱ ∈ N, ∀ e, |b ϱ e| ≤ W) (z : (V → ℤ) → ℝ) (θ : E → ℝ) (s : (V → ℤ) → ℝ)
    (φ : V → ℝ) :
    shiftProduct G (clockEdgeWeight β n) (clockShiftCost β n) N b z θ s 0 (-φ) =
      shiftProduct G (clockEdgeWeight β n) (clockShiftCost β n) N b z θ s 0 φ := by
  have hw := clockEdgeWeight_isLocalStripWeight hβ hn hW
  unfold shiftProduct
  refine Finset.prod_congr rfl fun ϱ hϱ => ?_
  rw [grad_neg', sum_neg_mul', lineFactor_neg hw.even hw.cost_even (b ϱ) _ θ (hb ϱ hϱ),
    neg_zero]

/-- The first-order exponent of one ensemble for the clock weight. -/
def gridShiftExponent (G : Multigraph V E) (β n : ℝ) (N : Finset (V → ℤ))
    (b : (V → ℤ) → E → ℝ) (z : (V → ℤ) → ℝ) (θ : E → ℝ) (s : (V → ℤ) → ℝ) (φ : V → ℝ) : ℝ :=
  compactClockShiftExponent G β n θ φ + ∑ ϱ ∈ N,
    z ϱ * deriv (lineFactor (clockEdgeWeight β n) (clockShiftCost β n) (b ϱ) (G.grad φ) θ
      (∑ j, φ j * (ϱ j : ℝ)) (s ϱ)) 0 /
      (1 + z ϱ * lineFactor (clockEdgeWeight β n) (clockShiftCost β n) (b ϱ) (G.grad φ) θ
        (∑ j, φ j * (ϱ j : ℝ)) (s ϱ) 0)

omit [DecidableEq V] in
theorem gridShiftExponent_neg {β n W : ℝ} (hβ : 0 ≤ β) (hn : 0 < n) (hW : 0 ≤ W)
    (G : Multigraph V E) (N : Finset (V → ℤ)) (b : (V → ℤ) → E → ℝ)
    (hb : ∀ ϱ ∈ N, ∀ e, |b ϱ e| ≤ W) (z : (V → ℤ) → ℝ) (θ : E → ℝ) (s : (V → ℤ) → ℝ)
    (φ : V → ℝ) :
    gridShiftExponent G β n N b z θ s (-φ) = -gridShiftExponent G β n N b z θ s φ := by
  have hw := clockEdgeWeight_isLocalStripWeight hβ hn hW
  unfold gridShiftExponent
  rw [compactClockShiftExponent_neg, neg_add, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun ϱ hϱ => ?_
  rw [grad_neg', sum_neg_mul', deriv_lineFactor_neg hw.even hw.cost_even (b ϱ) _ θ (hb ϱ hϱ),
    lineFactor_neg hw.even hw.cost_even (b ϱ) _ θ (hb ϱ hϱ), neg_zero, mul_neg, neg_div]

/-- **The branch bound on the compact clock box** (FS81 (6.28)–(6.39), one ensemble). -/
theorem integral_gridShiftProduct_ge (G : Multigraph V E) {β n : ℝ} (hβ : 0 ≤ β) (hn : 0 < n)
    {W : ℝ} (hW : 0 ≤ W) {M : ℝ → ℝ} (hlog : HasLogDerivBounds (clockEdgeWeight β n) W M)
    {κ : ℝ} (hcurv : HasCurvatureBound (clockEdgeWeight β n) κ)
    (N : Finset (V → ℤ)) (b : (V → ℤ) → E → ℝ) (z : (V → ℤ) → ℝ) (A m : ℝ)
    (hbA : ∀ ϱ ∈ N, ∀ e, |b ϱ e| ≤ A) (hAW : A ≤ W) (hm0 : 0 ≤ m) (hm1 : m ≤ 1)
    (hM : ∀ u : ℝ, |u| ≤ A → M u ≤ m) (hz : ∀ ϱ ∈ N, |z ϱ| ≤ 1 / 8) (θ : E → ℝ)
    (s T : (V → ℤ) → ℝ) (hθT : ∀ ϱ ∈ N, ∀ e, b ϱ e ≠ 0 → |θ e| ≤ T ϱ) :
    Real.exp (-(κ * ∑ e, θ e ^ 2 + ∑ ϱ ∈ N, 8 * |z ϱ| *
        (s ϱ ^ 2 + (((Finset.univ.filter fun e => b ϱ e ≠ 0).card : ℝ) * m * T ϱ) ^ 2 +
          ((Finset.univ.filter fun e => b ϱ e ≠ 0).card : ℝ) ^ 2 * m * T ϱ ^ 2))) *
        ∫ φ, compactClockBondProduct G β n φ 0 *
          shiftProduct G (clockEdgeWeight β n) (clockShiftCost β n) N b z θ s 0 φ
          ∂gridBoxMeasure n V ≤
      ∫ φ, compactClockBondProduct G β n φ θ *
          shiftProduct G (clockEdgeWeight β n) (clockShiftCost β n) N b z θ s 1 φ
          ∂gridBoxMeasure n V := by
  have hw := clockEdgeWeight_isLocalStripWeight hβ hn hW
  have hnzero : ∀ z : ℂ, |z.im| ≤ W → clockEdgeWeight β n z ≠ 0 :=
    fun z _ => clockEdgeWeight_ne_zero β n z
  have hbW : ∀ ϱ ∈ N, ∀ e, |b ϱ e| ≤ W := fun ϱ hϱ e => (hbA ϱ hϱ e).trans hAW
  set err : (V → ℤ) → ℝ := fun ϱ => 8 * |z ϱ| *
    (s ϱ ^ 2 + (((Finset.univ.filter fun e => b ϱ e ≠ 0).card : ℝ) * m * T ϱ) ^ 2 +
      ((Finset.univ.filter fun e => b ϱ e ≠ 0).card : ℝ) ^ 2 * m * T ϱ ^ 2) with herr
  have hbase : ∀ φ : V → ℝ, compactClockBondProduct G β n φ 0 = clockDensity β n G φ := by
    intro φ
    unfold compactClockBondProduct clockDensity
    simp only [Pi.zero_apply, add_zero]
  refine integral_ge_of_odd_exponent_of_negInvariant (H := gridShiftExponent G β n N b z θ s) _
    (measurePreserving_neg_gridBoxMeasure n)
    (integrable_bondProduct_mul_shiftProduct hβ hn hW G θ N b hbW z hz θ s 1)
    (integrable_bondProduct_mul_shiftProduct hβ hn hW G 0 N b hbW z hz θ s 0)
    (fun φ => mul_nonneg (compactClockBondProduct_pos G β n φ 0).le
      (shiftProduct_clock_pos hβ hn hW G N b hbW z hz θ s 0 φ).le) ?_
    (gridShiftExponent_neg hβ hn hW G N b hbW z θ s) fun φ => ?_
  · refine ae_of_all _ fun φ => ?_
    simp only [hbase]
    rw [clockDensity_neg, shiftProduct_clock_zero_neg hβ hn hW G N b hbW z θ s φ]
  -- the edge weights
  have hρ : compactClockBondProduct G β n φ 0 *
      Real.exp (compactClockShiftExponent G β n θ φ - κ * ∑ e, θ e ^ 2) ≤
      compactClockBondProduct G β n φ θ := by
    rw [hbase]
    exact clockDensity_shift_lower G hcurv φ θ
  -- the factors
  have hfac := prod_mul_exp_le_prod N
    (fun ϱ => 1 + z ϱ * lineFactor (clockEdgeWeight β n) (clockShiftCost β n) (b ϱ) (G.grad φ) θ
      (∑ j, φ j * (ϱ j : ℝ)) (s ϱ) 0)
    (fun ϱ => 1 + z ϱ * lineFactor (clockEdgeWeight β n) (clockShiftCost β n) (b ϱ) (G.grad φ) θ
      (∑ j, φ j * (ϱ j : ℝ)) (s ϱ) 1)
    (fun ϱ => z ϱ * deriv (lineFactor (clockEdgeWeight β n) (clockShiftCost β n) (b ϱ)
      (G.grad φ) θ (∑ j, φ j * (ϱ j : ℝ)) (s ϱ)) 0)
    err (fun ϱ hϱ => lt_of_lt_of_le (by norm_num)
      (one_add_mul_lineFactor_clock_ge hβ hn hW (b ϱ) (hbW ϱ hϱ) (hz ϱ hϱ) _ _ _ _ _))
    fun ϱ hϱ => one_add_mul_lineFactor_ge_loc hw hnzero hlog (b ϱ) (G.grad φ) θ
      (∑ j, φ j * (ϱ j : ℝ)) (s ϱ) (z ϱ) A (T ϱ) m (hbA ϱ hϱ) hAW (hθT ϱ hϱ) hm0 hm1 hM (hz ϱ hϱ)
  exact exp_mul_le_of_le (compactClockBondProduct_pos G β n φ 0).le
    (shiftProduct_clock_pos hβ hn hW G N b hbW z hz θ s 0 φ).le hρ hfac

end FroehlichSpencer.BKT.Clock.Disorder

end
