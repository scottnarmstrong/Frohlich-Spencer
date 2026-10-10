/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.Moment.Offset
public import FroehlichSpencer.BKT.Generic.Moment.Taylor
public import FroehlichSpencer.BKT.Generic.Moment.RealShift
public import FroehlichSpencer.BKT.Generic.Moment.Even
public import FroehlichSpencer.BKT.Generic.Moment.ProdAlg

/-!
# The branch bound of the non-Gaussian real shift (generic core)

This is the
non-Gaussian replacement of KP's branch bound (`ExpMoment.integral_prod_cos_shift_ge`; KP

One ensemble `N` of renormalized densities, with wave gradients `b(ϱ)` and activities `z(ϱ)`, is
followed along the real shift `t ↦ (∇φ + tθ, ⟨φ, ϱ⟩ + t s(ϱ))` (`shiftProduct`).

At `t = 0` it is
the unshifted product; at `t = 1` it is the product with the edge field `θ` and the phase shifts
`s`.

The branch bound (`integral_shiftProduct_ge`) is

`e^{−κ‖θ‖² − ∑_ϱ err(ϱ)} ∫ ρ₀ · Π₀ ≤ ∫ ρ_θ · Π₁`,

with `ρ₀ = edgeDensity`, `ρ_θ = offsetEdgeDensity θ` and
`err(ϱ) = 8|z(ϱ)| (s(ϱ)² + (N m T)² + N² m T²)` from the per-factor Taylor step.

The proof:

* the real shift of the edge weights (`prod_re_shift_ge`, FS81 (6.28)) gives
  `ρ_θ ≥ ρ₀ e^{H₀ − κ‖θ‖²}`;
* each factor satisfies `1 + z F(1) ≥ (1 + z F(0)) e^{z F'(0)/(1 + z F(0)) − err}`
  (`one_add_mul_lineFactor_ge`, FS81 (6.30)–(6.37));
* the exponent `H = H₀ + ∑ z F'(0)/(1 + z F(0))` is odd in `φ` and the base `ρ₀ Π₀` is even, so
  symmetrization (`integral_ge_of_odd_exponent`, FS81 (6.38)–(6.39)) removes `e^{H}`.

Positivity is used only after renormalization (`|z| ≤ 1/8`, `|F| ≤ 1`), as in KP  and
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic

open MeasureTheory Complex

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] {w : ℂ → ℂ} {W : ℝ}
  {c : ℝ → ℝ}

/-! ## Continuity and bounds of the local factor -/

omit [Fintype V] [DecidableEq V] in
/-- The local factor along continuous gradients and phases is continuous. -/
theorem continuous_localFactor (hw : IsStripWeight w W c) (b : E → ℝ) (hb : ∀ e, |b e| ≤ W)
    {X : Type*} [TopologicalSpace X] {x : X → E → ℝ} (hx : Continuous x) {θ : X → ℝ}
    (hθ : Continuous θ) : Continuous fun p => localFactor w c b (x p) (θ p) := by
  have hb' : ∀ e, |(-b) e| ≤ W := fun e => by rw [Pi.neg_apply, abs_neg]; exact hb e
  have hθc : Continuous fun p => ((θ p : ℝ) : ℂ) := Complex.continuous_ofReal.comp hθ
  unfold localFactor normalizedEdgeRatio
  refine Continuous.div_const (Continuous.add ?_ ?_) 2
  · exact (Complex.continuous_exp.comp (continuous_const.mul hθc)).mul
      ((continuous_edgeRatio hw b hb hx).mul continuous_const)
  · exact (Complex.continuous_exp.comp (continuous_const.mul hθc).neg).mul
      ((continuous_edgeRatio hw (-b) hb' hx).mul continuous_const)

omit [Fintype V] [DecidableEq V] in
/-- `|F| ≤ 1` along the line. -/
theorem abs_lineFactor_le_one (hw : IsStripWeight w W c) (b : E → ℝ) (hb : ∀ e, |b e| ≤ W)
    (x y : E → ℝ) (ph s t : ℝ) : |lineFactor w c b x y ph s t| ≤ 1 :=
  (Complex.abs_re_le_norm _).trans (norm_localFactor_le_one hw.ratio_le b _ hb _)

omit [DecidableEq V] in
/-- The line factor, as a function of the field `φ`, is continuous. -/
theorem continuous_lineFactor_field (hw : IsStripWeight w W c) (G : Multigraph V E)
    (b : E → ℝ) (hb : ∀ e, |b e| ≤ W) (θ : E → ℝ) (ϱ : V → ℤ) (s t : ℝ) :
    Continuous fun φ : V → ℝ =>
      lineFactor w c b (G.grad φ) θ (∑ j, φ j * (ϱ j : ℝ)) s t := by
  unfold lineFactor
  refine Complex.continuous_re.comp (continuous_localFactor hw b hb ?_ ?_)
  · refine continuous_pi fun e => ?_
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Multigraph.grad]
    exact ((continuous_apply (G.src e)).sub (continuous_apply (G.tgt e))).add continuous_const
  · exact (continuous_finsetSum _ fun j _ => (continuous_apply j).mul continuous_const).add
      continuous_const

/-! ## The renormalized product along the shift -/

/-- The renormalized product of one ensemble along the real shift: at time `t` the edge gradients
are `∇φ + tθ` and the phase of `ϱ` is `⟨φ, ϱ⟩ + t s(ϱ)`. -/
def shiftProduct (G : Multigraph V E) (w : ℂ → ℂ) (c : ℝ → ℝ) (N : Finset (V → ℤ))
    (b : (V → ℤ) → E → ℝ) (z : (V → ℤ) → ℝ) (θ : E → ℝ) (s : (V → ℤ) → ℝ) (t : ℝ)
    (φ : V → ℝ) : ℝ :=
  ∏ ϱ ∈ N, (1 + z ϱ * lineFactor w c (b ϱ) (G.grad φ) θ (∑ j, φ j * (ϱ j : ℝ)) (s ϱ) t)

omit [DecidableEq V] in
theorem continuous_shiftProduct (hw : IsStripWeight w W c) (G : Multigraph V E)
    (N : Finset (V → ℤ)) (b : (V → ℤ) → E → ℝ) (hb : ∀ ϱ ∈ N, ∀ e, |b ϱ e| ≤ W)
    (z : (V → ℤ) → ℝ) (θ : E → ℝ) (s : (V → ℤ) → ℝ) (t : ℝ) :
    Continuous (shiftProduct G w c N b z θ s t) := by
  unfold shiftProduct
  exact continuous_finsetProd _ fun ϱ hϱ => continuous_const.add (continuous_const.mul
    (continuous_lineFactor_field hw G (b ϱ) (hb ϱ hϱ) θ ϱ (s ϱ) t))

omit [DecidableEq V] in
/-- Every factor is at least `7/8`. -/
theorem one_add_mul_lineFactor_ge_seven_eighths (hw : IsStripWeight w W c) (b : E → ℝ)
    (hb : ∀ e, |b e| ≤ W) {z : ℝ} (hz : |z| ≤ 1 / 8) (x y : E → ℝ) (ph s t : ℝ) :
    7 / 8 ≤ 1 + z * lineFactor w c b x y ph s t := by
  have h1 := abs_lineFactor_le_one hw b hb x y ph s t
  have h2 : |z * lineFactor w c b x y ph s t| ≤ 1 / 8 := by
    rw [abs_mul]
    calc |z| * |lineFactor w c b x y ph s t| ≤ 1 / 8 * 1 :=
          mul_le_mul hz h1 (abs_nonneg _) (by norm_num)
      _ = 1 / 8 := mul_one _
  linarith [neg_abs_le (z * lineFactor w c b x y ph s t)]

omit [DecidableEq V] in
theorem shiftProduct_pos (hw : IsStripWeight w W c) (G : Multigraph V E)
    (N : Finset (V → ℤ)) (b : (V → ℤ) → E → ℝ) (hb : ∀ ϱ ∈ N, ∀ e, |b ϱ e| ≤ W)
    (z : (V → ℤ) → ℝ) (hz : ∀ ϱ ∈ N, |z ϱ| ≤ 1 / 8) (θ : E → ℝ) (s : (V → ℤ) → ℝ) (t : ℝ)
    (φ : V → ℝ) : 0 < shiftProduct G w c N b z θ s t φ :=
  Finset.prod_pos fun ϱ hϱ => lt_of_lt_of_le (by norm_num)
    (one_add_mul_lineFactor_ge_seven_eighths hw (b ϱ) (hb ϱ hϱ) (hz ϱ hϱ) _ _ _ _ _)

omit [DecidableEq V] in
theorem abs_shiftProduct_le (hw : IsStripWeight w W c) (G : Multigraph V E)
    (N : Finset (V → ℤ)) (b : (V → ℤ) → E → ℝ) (hb : ∀ ϱ ∈ N, ∀ e, |b ϱ e| ≤ W)
    (z : (V → ℤ) → ℝ) (hz : ∀ ϱ ∈ N, |z ϱ| ≤ 1 / 8) (θ : E → ℝ) (s : (V → ℤ) → ℝ) (t : ℝ)
    (φ : V → ℝ) : |shiftProduct G w c N b z θ s t φ| ≤ (9 / 8 : ℝ) ^ N.card := by
  unfold shiftProduct
  rw [Finset.abs_prod, ← Finset.prod_const]
  refine Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun ϱ hϱ => ?_
  have h1 := abs_lineFactor_le_one hw (b ϱ) (hb ϱ hϱ) (G.grad φ) θ
    (∑ j, φ j * (ϱ j : ℝ)) (s ϱ) t
  have h2 : |z ϱ * lineFactor w c (b ϱ) (G.grad φ) θ (∑ j, φ j * (ϱ j : ℝ)) (s ϱ) t| ≤ 1 / 8 := by
    rw [abs_mul]
    calc _ ≤ 1 / 8 * 1 := mul_le_mul (hz ϱ hϱ) h1 (abs_nonneg _) (by norm_num)
      _ = 1 / 8 := mul_one _
  calc _ ≤ |(1 : ℝ)| + |z ϱ * lineFactor w c (b ϱ) (G.grad φ) θ (∑ j, φ j * (ϱ j : ℝ)) (s ϱ) t| :=
        abs_add_le _ _
    _ ≤ 9 / 8 := by rw [abs_one]; linarith

omit [DecidableEq V] in
/-- A bounded continuous multiple of an integrable density is integrable. -/
theorem integrable_mul_shiftProduct (hw : IsStripWeight w W c) (G : Multigraph V E)
    {ρ : (V → ℝ) → ℝ} (hρ : Integrable ρ)
    (N : Finset (V → ℤ)) (b : (V → ℤ) → E → ℝ) (hb : ∀ ϱ ∈ N, ∀ e, |b ϱ e| ≤ W)
    (z : (V → ℤ) → ℝ) (hz : ∀ ϱ ∈ N, |z ϱ| ≤ 1 / 8) (θ : E → ℝ) (s : (V → ℤ) → ℝ) (t : ℝ) :
    Integrable fun φ => ρ φ * shiftProduct G w c N b z θ s t φ :=
  hρ.mul_bdd (continuous_shiftProduct hw G N b hb z θ s t).aestronglyMeasurable
    (Filter.Eventually.of_forall fun φ => by
      rw [Real.norm_eq_abs]; exact abs_shiftProduct_le hw G N b hb z hz θ s t φ)

omit [Fintype V] [Fintype E] [DecidableEq V] in
lemma grad_neg' (G : Multigraph V E) (φ : V → ℝ) : G.grad (-φ) = -G.grad φ := by
  funext e; simp only [Multigraph.grad, Pi.neg_apply]; ring

omit [DecidableEq V] in
lemma sum_neg_mul' (φ : V → ℝ) (ϱ : V → ℤ) :
    ∑ j, (-φ) j * (ϱ j : ℝ) = -∑ j, φ j * (ϱ j : ℝ) := by
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun j _ => by rw [Pi.neg_apply, neg_mul]

omit [DecidableEq V] in
/-- The unshifted product is even in the field. -/
theorem shiftProduct_zero_neg (hw : IsStripWeight w W c) (G : Multigraph V E)
    (N : Finset (V → ℤ)) (b : (V → ℤ) → E → ℝ) (hb : ∀ ϱ ∈ N, ∀ e, |b ϱ e| ≤ W)
    (z : (V → ℤ) → ℝ) (θ : E → ℝ) (s : (V → ℤ) → ℝ) (φ : V → ℝ) :
    shiftProduct G w c N b z θ s 0 (-φ) = shiftProduct G w c N b z θ s 0 φ := by
  unfold shiftProduct
  refine Finset.prod_congr rfl fun ϱ hϱ => ?_
  rw [grad_neg', sum_neg_mul', lineFactor_neg hw.even hw.cost_even (b ϱ) _ θ (hb ϱ hϱ),
    neg_zero]

/-! ## The branch bound -/

/-- The first-order exponent of one ensemble: `H(φ) = H₀(φ) + ∑_ϱ z F'(0)/(1 + z F(0))`. -/
def shiftExponent (G : Multigraph V E) (w : ℂ → ℂ) (c : ℝ → ℝ) (N : Finset (V → ℤ))
    (b : (V → ℤ) → E → ℝ) (z : (V → ℤ) → ℝ) (θ : E → ℝ) (s : (V → ℤ) → ℝ) (φ : V → ℝ) : ℝ :=
  edgeShiftExponent G w θ φ + ∑ ϱ ∈ N,
    z ϱ * deriv (lineFactor w c (b ϱ) (G.grad φ) θ (∑ j, φ j * (ϱ j : ℝ)) (s ϱ)) 0 /
      (1 + z ϱ * lineFactor w c (b ϱ) (G.grad φ) θ (∑ j, φ j * (ϱ j : ℝ)) (s ϱ) 0)

omit [DecidableEq V] in
/-- `H` is odd in the field (FS81 Theorem 6.1 (2) for the first-order term). -/
theorem shiftExponent_neg (hw : IsStripWeight w W c) (hW : 0 < W) (G : Multigraph V E)
    (N : Finset (V → ℤ)) (b : (V → ℤ) → E → ℝ) (hb : ∀ ϱ ∈ N, ∀ e, |b ϱ e| ≤ W)
    (z : (V → ℤ) → ℝ) (θ : E → ℝ) (s : (V → ℤ) → ℝ) (φ : V → ℝ) :
    shiftExponent G w c N b z θ s (-φ) = -shiftExponent G w c N b z θ s φ := by
  unfold shiftExponent
  rw [edgeShiftExponent_neg hw hW, neg_add, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun ϱ hϱ => ?_
  rw [grad_neg', sum_neg_mul', deriv_lineFactor_neg hw.even hw.cost_even (b ϱ) _ θ (hb ϱ hϱ),
    lineFactor_neg hw.even hw.cost_even (b ϱ) _ θ (hb ϱ hϱ), neg_zero, mul_neg, neg_div]

omit [Fintype V] [Fintype E] [DecidableEq V] in
/-- The algebra of the pointwise comparison. -/
lemma exp_mul_le_of_le {r₀ r₁ P₀ P₁ H₀ S K R : ℝ} (hr₀ : 0 ≤ r₀) (hP₀ : 0 ≤ P₀)
    (hρ : r₀ * Real.exp (H₀ - K) ≤ r₁) (hP : P₀ * Real.exp (S - R) ≤ P₁) :
    Real.exp (-(K + R)) * (r₀ * P₀ * Real.exp (H₀ + S)) ≤ r₁ * P₁ := by
  have h : Real.exp (-(K + R)) * (r₀ * P₀ * Real.exp (H₀ + S)) =
      (r₀ * Real.exp (H₀ - K)) * (P₀ * Real.exp (S - R)) := by
    rw [mul_mul_mul_comm, ← Real.exp_add, mul_comm (Real.exp (-(K + R))), mul_assoc,
      ← Real.exp_add]
    ring_nf
  rw [h]
  exact mul_le_mul hρ hP (mul_nonneg hP₀ (Real.exp_pos _).le)
    ((mul_nonneg hr₀ (Real.exp_pos _).le).trans hρ)

/-- **The branch bound** (FS81 (6.28)–(6.39), one ensemble). With `|b(ϱ)| ≤ A ≤ W`,
`M ≤ m ≤ 1` on `[−A, A]`, `|z| ≤ 1/8` and `|θ| ≤ T(ϱ)` on the support of `b(ϱ)`:
`e^{−κ‖θ‖² − ∑ err} ∫ ρ₀ Π₀ ≤ ∫ ρ_θ Π₁`. -/
theorem integral_shiftProduct_ge (G : Multigraph V E) (hG : G.toSimpleGraph.Connected) (v : V)
    (hw : IsStripWeight w W c) (hW : 0 < W) (hnzero : ∀ z : ℂ, |z.im| ≤ W → w z ≠ 0)
    {M : ℝ → ℝ} (hlog : HasLogDerivBounds w W M) {κ : ℝ} (hcurv : HasCurvatureBound w κ)
    (N : Finset (V → ℤ)) (b : (V → ℤ) → E → ℝ) (z : (V → ℤ) → ℝ) (A m : ℝ)
    (hbA : ∀ ϱ ∈ N, ∀ e, |b ϱ e| ≤ A) (hAW : A ≤ W) (hm0 : 0 ≤ m) (hm1 : m ≤ 1)
    (hM : ∀ u : ℝ, |u| ≤ A → M u ≤ m) (hz : ∀ ϱ ∈ N, |z ϱ| ≤ 1 / 8) (θ : E → ℝ)
    (s T : (V → ℤ) → ℝ) (hθT : ∀ ϱ ∈ N, ∀ e, b ϱ e ≠ 0 → |θ e| ≤ T ϱ) :
    Real.exp (-(κ * ∑ e, θ e ^ 2 + ∑ ϱ ∈ N, 8 * |z ϱ| *
        (s ϱ ^ 2 + (((Finset.univ.filter fun e => b ϱ e ≠ 0).card : ℝ) * m * T ϱ) ^ 2 +
          ((Finset.univ.filter fun e => b ϱ e ≠ 0).card : ℝ) ^ 2 * m * T ϱ ^ 2))) *
        ∫ φ, edgeDensity G w v φ * shiftProduct G w c N b z θ s 0 φ ≤
      ∫ φ, offsetEdgeDensity G w θ v φ * shiftProduct G w c N b z θ s 1 φ := by
  have hbW : ∀ ϱ ∈ N, ∀ e, |b ϱ e| ≤ W := fun ϱ hϱ e => (hbA ϱ hϱ e).trans hAW
  set err : (V → ℤ) → ℝ := fun ϱ => 8 * |z ϱ| *
    (s ϱ ^ 2 + (((Finset.univ.filter fun e => b ϱ e ≠ 0).card : ℝ) * m * T ϱ) ^ 2 +
      ((Finset.univ.filter fun e => b ϱ e ≠ 0).card : ℝ) ^ 2 * m * T ϱ ^ 2) with herr
  refine integral_ge_of_odd_exponent (H := shiftExponent G w c N b z θ s) _
    (integrable_mul_shiftProduct hw G (integrable_offsetEdgeDensity G hG hw θ v) N b hbW z hz θ s 1)
    (integrable_mul_shiftProduct hw G (integrable_edgeDensity G hG hw v) N b hbW z hz θ s 0)
    (fun φ => mul_nonneg (edgeDensity_nonneg G hw v φ)
      (shiftProduct_pos hw G N b hbW z hz θ s 0 φ).le) ?_
    (shiftExponent_neg hw hW G N b hbW z θ s) fun φ => ?_
  · filter_upwards [edgeDensity_neg_ae G hw v] with φ hφ
    rw [hφ, shiftProduct_zero_neg hw G N b hbW z θ s φ]
  -- the pointwise comparison: the edge weights
  have hρ : edgeDensity G w v φ *
      Real.exp (edgeShiftExponent G w θ φ - κ * ∑ e, θ e ^ 2) ≤
      offsetEdgeDensity G w θ v φ := by
    unfold edgeDensity offsetEdgeDensity edgeShiftExponent
    have hind : 0 ≤ (Set.Ico (-Real.pi) Real.pi).indicator (1 : ℝ → ℝ) (φ v) := by
      by_cases h : φ v ∈ Set.Ico (-Real.pi) Real.pi <;> simp [h]
    rw [mul_right_comm]
    exact mul_le_mul_of_nonneg_right (prod_re_shift_ge hw hcurv (G.grad φ) θ) hind
  -- the factors
  have hfac := prod_mul_exp_le_prod N
    (fun ϱ => 1 + z ϱ * lineFactor w c (b ϱ) (G.grad φ) θ (∑ j, φ j * (ϱ j : ℝ)) (s ϱ) 0)
    (fun ϱ => 1 + z ϱ * lineFactor w c (b ϱ) (G.grad φ) θ (∑ j, φ j * (ϱ j : ℝ)) (s ϱ) 1)
    (fun ϱ => z ϱ * deriv (lineFactor w c (b ϱ) (G.grad φ) θ (∑ j, φ j * (ϱ j : ℝ)) (s ϱ)) 0)
    err (fun ϱ hϱ => lt_of_lt_of_le (by norm_num)
      (one_add_mul_lineFactor_ge_seven_eighths hw (b ϱ) (hbW ϱ hϱ) (hz ϱ hϱ) _ _ _ _ _))
    fun ϱ hϱ => one_add_mul_lineFactor_ge hw hnzero hlog (b ϱ) (G.grad φ) θ
      (∑ j, φ j * (ϱ j : ℝ)) (s ϱ) (z ϱ) A (T ϱ) m (hbA ϱ hϱ) hAW (hθT ϱ hϱ) hm0 hm1 hM (hz ϱ hϱ)
  exact exp_mul_le_of_le (edgeDensity_nonneg G hw v φ)
    (shiftProduct_pos hw G N b hbW z hz θ s 0 φ).le hρ hfac

end FroehlichSpencer.BKT.Generic

end
