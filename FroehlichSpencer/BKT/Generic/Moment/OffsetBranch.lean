/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.Moment.Assembly
public import FroehlichSpencer.BKT.Rotator.Periodic.SectorTools

/-!
# The paired-offset exponential-moment branch bound

The branch estimate for one rooted edge law cannot be symmetrized when its background offset is
nonzero. Pairing the laws at offsets `r` and `-r` restores the inversion used in FS81 (6.38)–(6.39).
The result compares the sum of the two unmarked integrals with the sum of their marked integrals,
with the same error as the zero-background branch estimate and uniformly in `r`.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic

open MeasureTheory Complex

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V]
  {w : ℂ → ℂ} {W : ℝ} {c : ℝ → ℝ}

/-- The exponential-moment product along a line based at the offset edge field `r`. -/
def offsetShiftProduct (G : Multigraph V E) (w : ℂ → ℂ) (c : ℝ → ℝ)
    (N : Finset (V → ℤ)) (b : (V → ℤ) → E → ℝ) (z : (V → ℤ) → ℝ)
    (r θ : E → ℝ) (s : (V → ℤ) → ℝ) (t : ℝ) (φ : V → ℝ) : ℝ :=
  ∏ ϱ ∈ N, (1 + z ϱ * lineFactor w c (b ϱ) (G.grad φ + r) θ
    (∑ j, φ j * (ϱ j : ℝ)) (s ϱ) t)

/-- The edge-weight part of the first-order exponent, evaluated at `∇φ + r`. -/
def offsetEdgeShiftExponent (G : Multigraph V E) (w : ℂ → ℂ) (r θ : E → ℝ)
    (φ : V → ℝ) : ℝ :=
  ∑ e, (logDeriv w (((G.grad φ e + r e : ℝ) : ℂ))).re * θ e

/-- The first-order exponent for the exponential-moment line based at `r`. -/
def offsetShiftExponent (G : Multigraph V E) (w : ℂ → ℂ) (c : ℝ → ℝ)
    (N : Finset (V → ℤ)) (b : (V → ℤ) → E → ℝ) (z : (V → ℤ) → ℝ)
    (r θ : E → ℝ) (s : (V → ℤ) → ℝ) (φ : V → ℝ) : ℝ :=
  offsetEdgeShiftExponent G w r θ φ +
    ∑ ϱ ∈ N,
      z ϱ * deriv (lineFactor w c (b ϱ) (G.grad φ + r) θ
        (∑ j, φ j * (ϱ j : ℝ)) (s ϱ)) 0 /
        (1 + z ϱ * lineFactor w c (b ϱ) (G.grad φ + r) θ
          (∑ j, φ j * (ϱ j : ℝ)) (s ϱ) 0)

omit [DecidableEq V] in
theorem offsetShiftProduct_pos (hw : IsStripWeight w W c) (G : Multigraph V E)
    (N : Finset (V → ℤ)) (b : (V → ℤ) → E → ℝ) (hb : ∀ ϱ ∈ N, ∀ e, |b ϱ e| ≤ W)
    (z : (V → ℤ) → ℝ) (hz : ∀ ϱ ∈ N, |z ϱ| ≤ 1 / 8) (r θ : E → ℝ)
    (s : (V → ℤ) → ℝ) (t : ℝ) (φ : V → ℝ) : 0 < offsetShiftProduct G w c N b z r θ s t φ :=
  Finset.prod_pos fun ϱ hϱ => lt_of_lt_of_le (by norm_num)
    (one_add_mul_lineFactor_ge_seven_eighths hw (b ϱ) (hb ϱ hϱ) (hz ϱ hϱ)
      (G.grad φ + r) θ (∑ j, φ j * (ϱ j : ℝ)) (s ϱ) t)

omit [DecidableEq V] in
theorem abs_offsetShiftProduct_le (hw : IsStripWeight w W c) (G : Multigraph V E)
    (N : Finset (V → ℤ)) (b : (V → ℤ) → E → ℝ) (hb : ∀ ϱ ∈ N, ∀ e, |b ϱ e| ≤ W)
    (z : (V → ℤ) → ℝ) (hz : ∀ ϱ ∈ N, |z ϱ| ≤ 1 / 8) (r θ : E → ℝ)
    (s : (V → ℤ) → ℝ) (t : ℝ) (φ : V → ℝ) :
    |offsetShiftProduct G w c N b z r θ s t φ| ≤ (9 / 8 : ℝ) ^ N.card := by
  unfold offsetShiftProduct
  rw [Finset.abs_prod, ← Finset.prod_const]
  refine Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun ϱ hϱ => ?_
  have h1 := abs_lineFactor_le_one hw (b ϱ) (hb ϱ hϱ) (G.grad φ + r) θ
    (∑ j, φ j * (ϱ j : ℝ)) (s ϱ) t
  have h2 : |z ϱ * lineFactor w c (b ϱ) (G.grad φ + r) θ
      (∑ j, φ j * (ϱ j : ℝ)) (s ϱ) t| ≤ 1 / 8 := by
    rw [abs_mul]
    calc
      _ ≤ 1 / 8 * 1 := mul_le_mul (hz ϱ hϱ) h1 (abs_nonneg _) (by norm_num)
      _ = 1 / 8 := mul_one _
  calc
    _ ≤ |(1 : ℝ)| + |z ϱ * lineFactor w c (b ϱ) (G.grad φ + r) θ
        (∑ j, φ j * (ϱ j : ℝ)) (s ϱ) t| := abs_add_le _ _
    _ ≤ 9 / 8 := by rw [abs_one]; linarith

omit [DecidableEq V] in
theorem continuous_offsetShiftProduct (hw : IsStripWeight w W c) (G : Multigraph V E)
    (N : Finset (V → ℤ)) (b : (V → ℤ) → E → ℝ) (hb : ∀ ϱ ∈ N, ∀ e, |b ϱ e| ≤ W)
    (z : (V → ℤ) → ℝ) (r θ : E → ℝ) (s : (V → ℤ) → ℝ) (t : ℝ) :
    Continuous (offsetShiftProduct G w c N b z r θ s t) := by
  unfold offsetShiftProduct
  refine continuous_finsetProd _ fun ϱ hϱ => continuous_const.add (continuous_const.mul ?_)
  refine Complex.continuous_re.comp (continuous_localFactor hw (b ϱ) (hb ϱ hϱ) ?_ ?_)
  · refine continuous_pi fun e => ?_
    simp only [Pi.add_apply, Multigraph.grad]
    fun_prop
  · exact (continuous_finsetSum _ fun j _ => (continuous_apply j).mul continuous_const).add
      continuous_const

omit [DecidableEq V] in
theorem integrable_mul_offsetShiftProduct (hw : IsStripWeight w W c) (G : Multigraph V E)
    {ρ : (V → ℝ) → ℝ} (hρ : Integrable ρ)
    (N : Finset (V → ℤ)) (b : (V → ℤ) → E → ℝ) (hb : ∀ ϱ ∈ N, ∀ e, |b ϱ e| ≤ W)
    (z : (V → ℤ) → ℝ) (hz : ∀ ϱ ∈ N, |z ϱ| ≤ 1 / 8) (r θ : E → ℝ)
    (s : (V → ℤ) → ℝ) (t : ℝ) :
    Integrable fun φ => ρ φ * offsetShiftProduct G w c N b z r θ s t φ :=
  hρ.mul_bdd (continuous_offsetShiftProduct hw G N b hb z r θ s t).aestronglyMeasurable
    (Filter.Eventually.of_forall fun φ => by
      rw [Real.norm_eq_abs]
      exact abs_offsetShiftProduct_le hw G N b hb z hz r θ s t φ)

omit [Fintype V] [Fintype E] [DecidableEq V] in
lemma grad_neg_offset (G : Multigraph V E) (φ : V → ℝ) : G.grad (-φ) = -G.grad φ := by
  funext e
  simp only [Multigraph.grad, Pi.neg_apply]
  ring

omit [DecidableEq V] in
lemma sum_neg_mul_offset (φ : V → ℝ) (ϱ : V → ℤ) :
    ∑ j, (-φ) j * (ϱ j : ℝ) = -∑ j, φ j * (ϱ j : ℝ) := by
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun j _ => by rw [Pi.neg_apply, neg_mul]

omit [DecidableEq V] in
theorem offsetShiftProduct_neg (hw : IsStripWeight w W c) (G : Multigraph V E)
    (N : Finset (V → ℤ)) (b : (V → ℤ) → E → ℝ) (hb : ∀ ϱ ∈ N, ∀ e, |b ϱ e| ≤ W)
    (z : (V → ℤ) → ℝ) (r θ : E → ℝ) (s : (V → ℤ) → ℝ) (φ : V → ℝ) :
    offsetShiftProduct G w c N b z r θ s 0 (-φ) =
      offsetShiftProduct G w c N b z (-r) θ s 0 φ := by
  classical
  unfold offsetShiftProduct
  refine Finset.prod_congr rfl fun ϱ hϱ => ?_
  have hx : G.grad (-φ) + r = -(G.grad φ + -r) := by
    funext e
    rw [grad_neg_offset]
    simp only [Pi.neg_apply, Pi.add_apply]
    ring_nf
  rw [hx, sum_neg_mul_offset, lineFactor_neg hw.even hw.cost_even (b ϱ)
    (G.grad φ + -r) θ (hb ϱ hϱ) _ (s ϱ) 0, neg_zero]

omit [DecidableEq V] in
theorem offsetShiftExponent_neg (hw : IsStripWeight w W c) (hW : 0 < W)
    (G : Multigraph V E) (N : Finset (V → ℤ)) (b : (V → ℤ) → E → ℝ)
    (hb : ∀ ϱ ∈ N, ∀ e, |b ϱ e| ≤ W) (z : (V → ℤ) → ℝ) (r θ : E → ℝ)
    (s : (V → ℤ) → ℝ) (φ : V → ℝ) :
    offsetShiftExponent G w c N b z r θ s (-φ) =
      -offsetShiftExponent G w c N b z (-r) θ s φ := by
  unfold offsetShiftExponent
  have hEdge : offsetEdgeShiftExponent G w r θ (-φ) =
      -offsetEdgeShiftExponent G w (-r) θ φ := by
    unfold offsetEdgeShiftExponent
    rw [grad_neg_offset]
    simp only [Pi.neg_apply]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun e he => ?_
    have hx : -G.grad φ e + r e = -(G.grad φ e - r e) := by ring
    rw [hx, logDeriv_neg_ofReal hw hW, Complex.neg_re]
    ring_nf
  have hFactors :
      (∑ ϱ ∈ N, z ϱ * deriv (lineFactor w c (b ϱ) (G.grad (-φ) + r) θ
        (∑ j, (-φ) j * (ϱ j : ℝ)) (s ϱ)) 0 /
        (1 + z ϱ * lineFactor w c (b ϱ) (G.grad (-φ) + r) θ
          (∑ j, (-φ) j * (ϱ j : ℝ)) (s ϱ) 0)) =
      -(∑ ϱ ∈ N, z ϱ * deriv (lineFactor w c (b ϱ) (G.grad φ + -r) θ
        (∑ j, φ j * (ϱ j : ℝ)) (s ϱ)) 0 /
        (1 + z ϱ * lineFactor w c (b ϱ) (G.grad φ + -r) θ
          (∑ j, φ j * (ϱ j : ℝ)) (s ϱ) 0)) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun ϱ hϱ => ?_
    have hx : G.grad (-φ) + r = -(G.grad φ + -r) := by
      funext e
      simp only [grad_neg_offset, Pi.neg_apply, Pi.add_apply]
      ring
    rw [hx, sum_neg_mul_offset,
      deriv_lineFactor_neg hw.even hw.cost_even (b ϱ) (G.grad φ + -r) θ (hb ϱ hϱ)
        (∑ j, φ j * (ϱ j : ℝ)) (s ϱ),
      lineFactor_neg hw.even hw.cost_even (b ϱ) (G.grad φ + -r) θ (hb ϱ hϱ)
        (∑ j, φ j * (ϱ j : ℝ)) (s ϱ), neg_zero]
    simp only [mul_neg, neg_div]
  rw [hEdge, hFactors]
  ring_nf

theorem integral_ge_of_paired_odd_exponents {fPlus fMinus iPlus iMinus hPlus hMinus : (V → ℝ) → ℝ}
    (R : ℝ) (hiPlus : Integrable iPlus) (hiMinus : Integrable iMinus)
    (hfPlus : Integrable fPlus) (hfMinus : Integrable fMinus)
    (hfPlus0 : ∀ φ, 0 ≤ fPlus φ) (hfMinus0 : ∀ φ, 0 ≤ fMinus φ)
    (hf_pair : ∀ᵐ φ, fPlus (-φ) = fMinus φ ∧ fMinus (-φ) = fPlus φ)
    (hH_pair : ∀ φ, hPlus (-φ) = -hMinus φ ∧ hMinus (-φ) = -hPlus φ)
    (hlePlus : ∀ φ, Real.exp (-R) * (fPlus φ * Real.exp (hPlus φ)) ≤ iPlus φ)
    (hleMinus : ∀ φ, Real.exp (-R) * (fMinus φ * Real.exp (hMinus φ)) ≤ iMinus φ) :
    Real.exp (-R) * ((∫ φ, fPlus φ) + (∫ φ, fMinus φ)) ≤
      (∫ φ, iPlus φ) + (∫ φ, iMinus φ) := by
  have hInegPlus : Integrable fun φ => iPlus (-φ) :=
    (measurePreserving_neg_pi).integrable_comp_emb
      (Homeomorph.neg (V → ℝ)).measurableEmbedding |>.mpr hiPlus
  have hInegMinus : Integrable fun φ => iMinus (-φ) :=
    (measurePreserving_neg_pi).integrable_comp_emb
      (Homeomorph.neg (V → ℝ)).measurableEmbedding |>.mpr hiMinus
  have hneg : (∫ φ, iPlus (-φ) + iMinus (-φ)) = (∫ φ, iPlus φ + iMinus φ) :=
    integral_comp_neg_pi (fun φ => iPlus φ + iMinus φ)
  have hsumR : (∫ φ, (iPlus φ + iMinus φ) + (iPlus (-φ) + iMinus (-φ))) =
      (∫ φ, iPlus φ + iMinus φ) + (∫ φ, iPlus (-φ) + iMinus (-φ)) :=
    integral_add (hiPlus.add hiMinus) (hInegPlus.add hInegMinus)
  have hsym : (∫ φ, iPlus φ + iMinus φ) = (1 / 2 : ℝ) *
      (∫ φ, (iPlus φ + iMinus φ) + (iPlus (-φ) + iMinus (-φ))) := by
    rw [hsumR, hneg]
    ring
  have hleft : Real.exp (-R) * ((∫ φ, fPlus φ) + (∫ φ, fMinus φ)) =
      ∫ φ, Real.exp (-R) * (fPlus φ + fMinus φ) := by
    rw [← integral_add hfPlus hfMinus, ← integral_const_mul]
  have hright : (∫ φ, iPlus φ) + (∫ φ, iMinus φ) =
      (1 / 2 : ℝ) * (∫ φ, (iPlus φ + iMinus φ) + (iPlus (-φ) + iMinus (-φ))) := by
    rw [← integral_add hiPlus hiMinus, hsym]
  rw [hleft, hright, ← integral_const_mul]
  refine integral_mono_ae
    ((hfPlus.add hfMinus).const_mul (Real.exp (-R)))
    (((hiPlus.add hiMinus).add (hInegPlus.add hInegMinus)).const_mul (1 / 2 : ℝ)) ?_
  filter_upwards [hf_pair] with φ hpair
  have h₁ := hlePlus φ
  have h₂ := hleMinus φ
  have h₃ := hlePlus (-φ)
  have h₄ := hleMinus (-φ)
  rcases hH_pair φ with ⟨hhPlus, hhMinus⟩
  rw [hpair.1, hhPlus] at h₃
  rw [hpair.2, hhMinus] at h₄
  have hcPlus : 2 ≤ Real.exp (hPlus φ) + Real.exp (-hPlus φ) := by
    linarith [Real.add_one_le_exp (hPlus φ), Real.add_one_le_exp (-hPlus φ)]
  have hcMinus : 2 ≤ Real.exp (hMinus φ) + Real.exp (-hMinus φ) := by
    linarith [Real.add_one_le_exp (hMinus φ), Real.add_one_le_exp (-hMinus φ)]
  have hsum := add_le_add (add_le_add h₁ h₂) (add_le_add h₃ h₄)
  have hR : 0 < Real.exp (-R) := Real.exp_pos _
  have hbase' : fPlus φ * 2 + fMinus φ * 2 ≤
      fPlus φ * (Real.exp (hPlus φ) + Real.exp (-hPlus φ)) +
        fMinus φ * (Real.exp (hMinus φ) + Real.exp (-hMinus φ)) := by
    exact add_le_add (mul_le_mul_of_nonneg_left hcPlus (hfPlus0 φ))
      (mul_le_mul_of_nonneg_left hcMinus (hfMinus0 φ))
  have hbase : 2 * (fPlus φ + fMinus φ) ≤
      fPlus φ * (Real.exp (hPlus φ) + Real.exp (-hPlus φ)) +
        fMinus φ * (Real.exp (hMinus φ) + Real.exp (-hMinus φ)) := by
    calc
      2 * (fPlus φ + fMinus φ) = fPlus φ * 2 + fMinus φ * 2 := by ring
      _ ≤ _ := hbase'
  have hpoint : Real.exp (-R) * (fPlus φ + fMinus φ) ≤
      (1 / 2 : ℝ) * (iPlus φ + iMinus φ + (iPlus (-φ) + iMinus (-φ))) := by
    nlinarith [hsum, hbase, hR]
  exact hpoint

/-! ## Paired-offset branch estimate -/

variable {G : Multigraph V E}

omit [DecidableEq V] in
/-- The one-side pointwise estimate, with an arbitrary background offset. -/
theorem offsetBranch_pointwise (v : V)
    (hw : IsStripWeight w W c) (hnzero : ∀ z : ℂ, |z.im| ≤ W → w z ≠ 0)
    {M : ℝ → ℝ} (hlog : HasLogDerivBounds w W M) {κ : ℝ} (hcurv : HasCurvatureBound w κ)
    (N : Finset (V → ℤ)) (b : (V → ℤ) → E → ℝ) (z : (V → ℤ) → ℝ) (A m : ℝ)
    (hbA : ∀ ϱ ∈ N, ∀ e, |b ϱ e| ≤ A) (hAW : A ≤ W) (hm0 : 0 ≤ m) (hm1 : m ≤ 1)
    (hM : ∀ u : ℝ, |u| ≤ A → M u ≤ m) (hz : ∀ ϱ ∈ N, |z ϱ| ≤ 1 / 8)
    (r θ : E → ℝ) (s T : (V → ℤ) → ℝ)
    (hθT : ∀ ϱ ∈ N, ∀ e, b ϱ e ≠ 0 → |θ e| ≤ T ϱ) (φ : V → ℝ) :
    Real.exp (-(κ * ∑ e, θ e ^ 2 + ∑ ϱ ∈ N, 8 * |z ϱ| *
        (s ϱ ^ 2 + (((Finset.univ.filter fun e => b ϱ e ≠ 0).card : ℝ) * m * T ϱ) ^ 2 +
          ((Finset.univ.filter fun e => b ϱ e ≠ 0).card : ℝ) ^ 2 * m * T ϱ ^ 2))) *
        (offsetEdgeDensity G w r v φ * offsetShiftProduct G w c N b z r θ s 0 φ *
          Real.exp (offsetShiftExponent G w c N b z r θ s φ)) ≤
      offsetEdgeDensity G w (r + θ) v φ * offsetShiftProduct G w c N b z r θ s 1 φ := by
  have hbW : ∀ ϱ ∈ N, ∀ e, |b ϱ e| ≤ W := fun ϱ hϱ e => (hbA ϱ hϱ e).trans hAW
  have hρ : offsetEdgeDensity G w r v φ * Real.exp
      (offsetEdgeShiftExponent G w r θ φ - κ * ∑ e, θ e ^ 2) ≤
        offsetEdgeDensity G w (r + θ) v φ := by
    unfold offsetEdgeDensity offsetEdgeShiftExponent
    have hind : 0 ≤ (Set.Ico (-Real.pi) Real.pi).indicator (1 : ℝ → ℝ) (φ v) := by
      by_cases h : φ v ∈ Set.Ico (-Real.pi) Real.pi <;> simp [h]
    rw [mul_right_comm]
    apply mul_le_mul_of_nonneg_right _ hind
    have hprod := prod_re_shift_ge hw hcurv (G.grad φ + r) θ
    simpa only [Pi.add_apply, add_assoc] using hprod
  have hfac := prod_mul_exp_le_prod N
    (fun ϱ => 1 + z ϱ * lineFactor w c (b ϱ) (G.grad φ + r) θ
      (∑ j, φ j * (ϱ j : ℝ)) (s ϱ) 0)
    (fun ϱ => 1 + z ϱ * lineFactor w c (b ϱ) (G.grad φ + r) θ
      (∑ j, φ j * (ϱ j : ℝ)) (s ϱ) 1)
    (fun ϱ => z ϱ * deriv (lineFactor w c (b ϱ) (G.grad φ + r) θ
      (∑ j, φ j * (ϱ j : ℝ)) (s ϱ)) 0)
    (fun ϱ => 8 * |z ϱ| * (s ϱ ^ 2 +
      (((Finset.univ.filter fun e => b ϱ e ≠ 0).card : ℝ) * m * T ϱ) ^ 2 +
      ((Finset.univ.filter fun e => b ϱ e ≠ 0).card : ℝ) ^ 2 * m * T ϱ ^ 2))
    (fun ϱ hϱ => lt_of_lt_of_le (by norm_num)
      (one_add_mul_lineFactor_ge_seven_eighths hw (b ϱ) (hbW ϱ hϱ) (hz ϱ hϱ)
        (G.grad φ + r) θ (∑ j, φ j * (ϱ j : ℝ)) (s ϱ) 0))
    (fun ϱ hϱ => one_add_mul_lineFactor_ge hw hnzero hlog (b ϱ) (G.grad φ + r) θ
      (∑ j, φ j * (ϱ j : ℝ)) (s ϱ) (z ϱ) A (T ϱ) m (hbA ϱ hϱ) hAW
      (hθT ϱ hϱ) hm0 hm1 hM (hz ϱ hϱ))
  have hExp : offsetEdgeShiftExponent G w r θ φ +
        ∑ ϱ ∈ N, z ϱ * deriv (lineFactor w c (b ϱ) (G.grad φ + r) θ
          (∑ j, φ j * (ϱ j : ℝ)) (s ϱ)) 0 /
          (1 + z ϱ * lineFactor w c (b ϱ) (G.grad φ + r) θ
            (∑ j, φ j * (ϱ j : ℝ)) (s ϱ) 0) =
      offsetShiftExponent G w c N b z r θ s φ := rfl
  have hP := exp_mul_le_of_le
    (offsetEdgeDensity_nonneg G hw r v φ)
    (offsetShiftProduct_pos hw G N b (fun ϱ hϱ e => hbW ϱ hϱ e) z hz r θ s 0 φ).le
    hρ hfac
  rw [hExp] at hP
  simpa only [offsetShiftProduct] using hP

/-- **Paired-offset exponential-moment branch estimate.** The constants and error are independent of the
background `r`. Both laws are marked by the same edge and phase shifts. -/
theorem integral_shiftProduct_ge_oppositeOffsetPair (hG : G.toSimpleGraph.Connected) (v : V)
    (hw : IsStripWeight w W c) (hW : 0 < W) (hnzero : ∀ z : ℂ, |z.im| ≤ W → w z ≠ 0)
    {M : ℝ → ℝ} (hlog : HasLogDerivBounds w W M) {κ : ℝ} (hcurv : HasCurvatureBound w κ)
    (N : Finset (V → ℤ)) (b : (V → ℤ) → E → ℝ) (z : (V → ℤ) → ℝ) (A m : ℝ)
    (hbA : ∀ ϱ ∈ N, ∀ e, |b ϱ e| ≤ A) (hAW : A ≤ W) (hm0 : 0 ≤ m) (hm1 : m ≤ 1)
    (hM : ∀ u : ℝ, |u| ≤ A → M u ≤ m) (hz : ∀ ϱ ∈ N, |z ϱ| ≤ 1 / 8)
    (r θ : E → ℝ) (s T : (V → ℤ) → ℝ)
    (hθT : ∀ ϱ ∈ N, ∀ e, b ϱ e ≠ 0 → |θ e| ≤ T ϱ) :
    Real.exp (-(κ * ∑ e, θ e ^ 2 + ∑ ϱ ∈ N, 8 * |z ϱ| *
        (s ϱ ^ 2 + (((Finset.univ.filter fun e => b ϱ e ≠ 0).card : ℝ) * m * T ϱ) ^ 2 +
          ((Finset.univ.filter fun e => b ϱ e ≠ 0).card : ℝ) ^ 2 * m * T ϱ ^ 2))) *
        ((∫ φ, offsetEdgeDensity G w r v φ *
            offsetShiftProduct G w c N b z r θ s 0 φ) +
          (∫ φ, offsetEdgeDensity G w (-r) v φ *
            offsetShiftProduct G w c N b z (-r) θ s 0 φ)) ≤
      ((∫ φ, offsetEdgeDensity G w (r + θ) v φ *
          offsetShiftProduct G w c N b z r θ s 1 φ) +
        (∫ φ, offsetEdgeDensity G w (-r + θ) v φ *
          offsetShiftProduct G w c N b z (-r) θ s 1 φ)) := by
  have hbW : ∀ ϱ ∈ N, ∀ e, |b ϱ e| ≤ W := fun ϱ hϱ e => (hbA ϱ hϱ e).trans hAW
  let fPlus : (V → ℝ) → ℝ := fun φ => offsetEdgeDensity G w r v φ *
    offsetShiftProduct G w c N b z r θ s 0 φ
  let fMinus : (V → ℝ) → ℝ := fun φ => offsetEdgeDensity G w (-r) v φ *
    offsetShiftProduct G w c N b z (-r) θ s 0 φ
  let iPlus : (V → ℝ) → ℝ := fun φ => offsetEdgeDensity G w (r + θ) v φ *
    offsetShiftProduct G w c N b z r θ s 1 φ
  let iMinus : (V → ℝ) → ℝ := fun φ => offsetEdgeDensity G w (-r + θ) v φ *
    offsetShiftProduct G w c N b z (-r) θ s 1 φ
  let hPlus : (V → ℝ) → ℝ := offsetShiftExponent G w c N b z r θ s
  let hMinus : (V → ℝ) → ℝ := offsetShiftExponent G w c N b z (-r) θ s
  have hiPlus : Integrable iPlus := integrable_mul_offsetShiftProduct hw G
    (integrable_offsetEdgeDensity G hG hw (r + θ) v) N b hbW z hz r θ s 1
  have hiMinus : Integrable iMinus := integrable_mul_offsetShiftProduct hw G
    (integrable_offsetEdgeDensity G hG hw (-r + θ) v) N b hbW z hz (-r) θ s 1
  have hfPlus : Integrable fPlus := integrable_mul_offsetShiftProduct hw G
    (integrable_offsetEdgeDensity G hG hw r v) N b hbW z hz r θ s 0
  have hfMinus : Integrable fMinus := integrable_mul_offsetShiftProduct hw G
    (integrable_offsetEdgeDensity G hG hw (-r) v) N b hbW z hz (-r) θ s 0
  have hfPlus0 : ∀ φ, 0 ≤ fPlus φ := fun φ => mul_nonneg
    (offsetEdgeDensity_nonneg G hw r v φ)
    (offsetShiftProduct_pos hw G N b hbW z hz r θ s 0 φ).le
  have hfMinus0 : ∀ φ, 0 ≤ fMinus φ := fun φ => mul_nonneg
    (offsetEdgeDensity_nonneg G hw (-r) v φ)
    (offsetShiftProduct_pos hw G N b hbW z hz (-r) θ s 0 φ).le
  have hf_pair : ∀ᵐ φ, fPlus (-φ) = fMinus φ ∧ fMinus (-φ) = fPlus φ := by
    filter_upwards [offsetEdgeDensity_neg_eq_negOffset_ae G hw r v,
      offsetEdgeDensity_neg_eq_negOffset_ae G hw (-r) v] with φ hRhoPlus hRhoMinus
    constructor
    · dsimp [fPlus, fMinus]
      rw [hRhoPlus, offsetShiftProduct_neg hw G N b hbW z r θ s φ]
    · dsimp [fPlus, fMinus]
      rw [hRhoMinus, offsetShiftProduct_neg hw G N b hbW z (-r) θ s φ]
      simp only [neg_neg]
  have hH_pair : ∀ φ, hPlus (-φ) = -hMinus φ ∧ hMinus (-φ) = -hPlus φ := by
    intro φ
    constructor
    · exact offsetShiftExponent_neg hw hW G N b hbW z r θ s φ
    · simpa only [neg_neg] using offsetShiftExponent_neg hw hW G N b hbW z (-r) θ s φ
  have hlePlus : ∀ φ, Real.exp (-(κ * ∑ e, θ e ^ 2 + ∑ ϱ ∈ N, 8 * |z ϱ| *
      (s ϱ ^ 2 + (((Finset.univ.filter fun e => b ϱ e ≠ 0).card : ℝ) * m * T ϱ) ^ 2 +
        ((Finset.univ.filter fun e => b ϱ e ≠ 0).card : ℝ) ^ 2 * m * T ϱ ^ 2))) *
      (fPlus φ * Real.exp (hPlus φ)) ≤ iPlus φ := by
    intro φ
    exact offsetBranch_pointwise v hw hnzero hlog hcurv N b z A m hbA hAW hm0 hm1 hM hz
      r θ s T hθT φ
  have hleMinus : ∀ φ, Real.exp (-(κ * ∑ e, θ e ^ 2 + ∑ ϱ ∈ N, 8 * |z ϱ| *
      (s ϱ ^ 2 + (((Finset.univ.filter fun e => b ϱ e ≠ 0).card : ℝ) * m * T ϱ) ^ 2 +
        ((Finset.univ.filter fun e => b ϱ e ≠ 0).card : ℝ) ^ 2 * m * T ϱ ^ 2))) *
      (fMinus φ * Real.exp (hMinus φ)) ≤ iMinus φ := by
    intro φ
    exact offsetBranch_pointwise v hw hnzero hlog hcurv N b z A m hbA hAW hm0 hm1 hM hz
      (-r) θ s T hθT φ
  have hpair := integral_ge_of_paired_odd_exponents
    (κ * ∑ e, θ e ^ 2 + ∑ ϱ ∈ N, 8 * |z ϱ| *
      (s ϱ ^ 2 + (((Finset.univ.filter fun e => b ϱ e ≠ 0).card : ℝ) * m * T ϱ) ^ 2 +
        ((Finset.univ.filter fun e => b ϱ e ≠ 0).card : ℝ) ^ 2 * m * T ϱ ^ 2))
    hiPlus hiMinus hfPlus hfMinus hfPlus0 hfMinus0 hf_pair hH_pair hlePlus hleMinus
  simpa only [fPlus, fMinus, iPlus, iMinus] using hpair

end FroehlichSpencer.BKT.Generic

end
