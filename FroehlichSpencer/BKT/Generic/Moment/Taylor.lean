/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.LocalFactorBounds
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Second-order Taylor bound for one renormalized factor along the real shift (generic core)

Along the
real shift every renormalized factor `1 + z F` is followed on the line
`t ↦ (x + t y, ph + t s)`: edge gradients move by `t y` (the edge field `θ` of FS81 (6.10)–(6.13))
and the phase moves by `t s` (the reduced phase `[σ(ϱ)]_{2π}`).

This module proves

This is the second-order Taylor bound for `log(1 + z f)`, using `|f| ≤ 1` (so `1 + z f ≥ 7/8`),
  `|f'| ≤ 2(N m T + |s|)` and `|f''| ≤ 4 N² m T² + 4 |s| N m T + 2 s²`;
* `lineFactor_neg`, `deriv_lineFactor_neg`: the parity that makes the first-order term odd in the
  field (FS81 Theorem 6.1 (2));
* `localFactor_add_two_pi_mul`: the local factor only sees the phase modulo `2π`.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic

open Complex

/-! ## The real second-order Taylor bound -/

/-- **Second-order Taylor lower bound** on `[0, 1]`: `g(0) + g'(0) − M/2 ≤ g(1)` when
`|g''| ≤ M`. -/
theorem taylor_lower_bound {g g' g'' : ℝ → ℝ} {M : ℝ}
    (hg : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt g (g' t) t)
    (hg' : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt g' (g'' t) t)
    (hM : ∀ t ∈ Set.Icc (0 : ℝ) 1, |g'' t| ≤ M) : g 0 + g' 0 - M / 2 ≤ g 1 := by
  have hmvt := norm_image_sub_le_of_norm_deriv_le_segment' (f := g') (f' := g'') (a := 0)
    (b := 1) (fun t ht => (hg' t ht).hasDerivWithinAt) (fun t ht => by
      rw [Real.norm_eq_abs]; exact hM t (Set.Ico_subset_Icc_self ht))
  set φ : ℝ → ℝ := fun t => g t - (g 0 + g' 0 * t - M / 2 * t ^ 2) with hφ
  have hpoly : ∀ t : ℝ, HasDerivAt (fun t : ℝ => g 0 + g' 0 * t - M / 2 * t ^ 2)
      (g' 0 - M * t) t := by
    intro t
    exact ((((hasDerivAt_id t).const_mul (g' 0)).const_add (g 0)).sub
      ((hasDerivAt_pow 2 t).const_mul (M / 2))).congr_deriv (by norm_num; ring)
  have hmono : MonotoneOn φ (Set.Icc 0 1) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 1) (f' := fun t =>
      g' t - (g' 0 - M * t)) ?_ ?_ ?_
    · intro t ht
      exact ((hg t ht).continuousAt.sub (hpoly t).continuousAt).continuousWithinAt
    · intro t ht
      exact ((hg t (interior_subset ht)).sub (hpoly t)).hasDerivWithinAt
    · intro t ht
      have ht' : t ∈ Set.Icc (0 : ℝ) 1 := interior_subset ht
      have hb := hmvt t ht'
      rw [Real.norm_eq_abs, sub_zero] at hb
      have := neg_abs_le (g' t - g' 0)
      show 0 ≤ g' t - (g' 0 - M * t)
      linarith
  have h01 := hmono (Set.left_mem_Icc.mpr zero_le_one) (Set.right_mem_Icc.mpr zero_le_one)
    zero_le_one
  simp only [hφ] at h01
  linarith

/-! ## The local factor along a line -/

variable {E : Type*} [Fintype E] {w : ℂ → ℂ} {W : ℝ} {c M : ℝ → ℝ}

/-- The (real) local factor along the line `t ↦ (x + t y, ph + t s)`. -/
def lineFactor (w : ℂ → ℂ) (c : ℝ → ℝ) (b x y : E → ℝ) (ph s t : ℝ) : ℝ :=
  (localFactor w c b (x + t • y) (ph + t * s)).re

/-- The normalized edge ratio is the product of the normalized edge factors. -/
lemma normalizedEdgeRatio_eq_prod (w : ℂ → ℂ) (c : ℝ → ℝ) (b x : E → ℝ) :
    normalizedEdgeRatio w c b x = ∏ e, normalizedEdgeFactor w c (b e) (x e) := by
  unfold normalizedEdgeRatio edgeRatio normalizedEdgeFactor
  rw [Complex.ofReal_sum, ← Finset.sum_neg_distrib, Complex.exp_sum, ← Finset.prod_mul_distrib]

/-- On a line, the normalized edge ratio is the generic edge product over any superset of the
support of the shift. -/
lemma normalizedEdgeRatio_line_eq (hc0 : c 0 = 0) (hw0 : ∀ t : ℝ, w t ≠ 0) (b x y : E → ℝ)
    (t : ℝ) (S : Finset E) (hS : ∀ e, e ∉ S → b e = 0) :
    normalizedEdgeRatio w c b (x + t • y) = genericEdgeProduct w c S b x y t := by
  rw [normalizedEdgeRatio_eq_prod]
  unfold genericEdgeProduct
  symm
  refine Finset.prod_subset (Finset.subset_univ S) fun e _ he => ?_
  rw [hS e he]
  unfold normalizedEdgeFactor
  rw [Complex.ofReal_zero, zero_mul, add_zero, div_self (hw0 _), hc0, Complex.ofReal_zero,
    neg_zero, Complex.exp_zero, one_mul]


theorem localFactor_line_eq (hc0 : c 0 = 0) (hw0 : ∀ t : ℝ, w t ≠ 0) (b x y : E → ℝ)
    (t θ' : ℝ) :
    localFactor w c b (x + t • y) θ' =
      genericLocalF₂ w c (Finset.univ.filter fun e => b e ≠ 0) b x y t * (Real.cos θ' : ℂ) +
        genericLocalF₁ w c (Finset.univ.filter fun e => b e ≠ 0) b x y t *
          (Real.sin θ' : ℂ) := by
  set S := Finset.univ.filter fun e => b e ≠ 0 with hSdef
  have hS : ∀ e, e ∉ S → b e = 0 := fun e he => by
    by_contra h
    exact he (Finset.mem_filter.mpr ⟨Finset.mem_univ e, h⟩)
  have hS' : ∀ e, e ∉ S → (-b) e = 0 := fun e he => by rw [Pi.neg_apply, hS e he, neg_zero]
  unfold localFactor genericLocalF₁ genericLocalF₂
  rw [normalizedEdgeRatio_line_eq hc0 hw0 b x y t S hS,
    normalizedEdgeRatio_line_eq hc0 hw0 (-b) x y t S hS']
  have h1 : Complex.exp (I * θ') = Complex.cos θ' + Complex.sin θ' * I := by
    rw [mul_comm, Complex.exp_mul_I]
  have h2 : Complex.exp (-(I * θ')) = Complex.cos θ' - Complex.sin θ' * I := by
    rw [show -(I * (θ' : ℂ)) = ((-θ' : ℝ) : ℂ) * I by push_cast; ring, Complex.exp_mul_I]
    push_cast
    rw [Complex.cos_neg, Complex.sin_neg]
    ring
  rw [h1, h2, Complex.ofReal_cos, Complex.ofReal_sin]
  ring

/-- The phase only matters modulo `2π`. -/
theorem localFactor_add_two_pi_mul (b x : E → ℝ) (θ' : ℝ) (n : ℤ) :
    localFactor w c b x (θ' + n * (2 * Real.pi)) = localFactor w c b x θ' := by
  unfold localFactor
  have hp : Complex.exp (I * ((θ' + n * (2 * Real.pi) : ℝ) : ℂ)) = Complex.exp (I * θ') := by
    rw [show I * ((θ' + n * (2 * Real.pi) : ℝ) : ℂ) = I * θ' + n * (2 * Real.pi * I) by
      push_cast; ring, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  have hm : Complex.exp (-(I * ((θ' + n * (2 * Real.pi) : ℝ) : ℂ))) =
      Complex.exp (-(I * θ')) := by
    rw [show -(I * ((θ' + n * (2 * Real.pi) : ℝ) : ℂ)) = -(I * θ') + (-n : ℤ) * (2 * Real.pi * I)
      by push_cast; ring, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  rw [hp, hm]

/-- **Parity along the line** (FS81 Theorem 6.1 (2)). -/
theorem lineFactor_neg (heven : ∀ z : ℂ, |z.im| ≤ W → w (-z) = w z) (hc : ∀ u, c (-u) = c u)
    (b x y : E → ℝ) (hb : ∀ e, |b e| ≤ W) (ph s t : ℝ) :
    lineFactor w c b (-x) y (-ph) s t = lineFactor w c b x y ph s (-t) := by
  unfold lineFactor
  have h := localFactor_neg heven hc b (x + (-t) • y) hb (ph + -t * s)
  have hx : -(x + (-t) • y) = -x + t • y := by
    funext e; simp only [Pi.neg_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  have hph : -(ph + -t * s) = -ph + t * s := by ring
  rw [hx, hph] at h
  rw [h]

/-- The first-order coefficient along the line is odd in the base point. -/
theorem deriv_lineFactor_neg (heven : ∀ z : ℂ, |z.im| ≤ W → w (-z) = w z)
    (hc : ∀ u, c (-u) = c u) (b x y : E → ℝ) (hb : ∀ e, |b e| ≤ W) (ph s : ℝ) :
    deriv (lineFactor w c b (-x) y (-ph) s) 0 = -deriv (lineFactor w c b x y ph s) 0 := by
  have hfun : lineFactor w c b (-x) y (-ph) s = fun t => lineFactor w c b x y ph s (-t) :=
    funext fun t => lineFactor_neg heven hc b x y hb ph s t
  rw [hfun, deriv_comp_neg, neg_zero]

/-! ## The comparison of one factor -/

omit [Fintype E] in
/-- The real part of a differentiable complex curve. -/
lemma hasDerivAt_re_of_hasDerivAt {f : ℝ → ℂ} {f' : ℂ} {t : ℝ} (h : HasDerivAt f f' t) :
    HasDerivAt (fun t => (f t).re) f'.re t := by
  exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt t h


theorem lineFactor_derivs (hw : IsStripWeight w W c)
    (hnzero : ∀ z : ℂ, |z.im| ≤ W → w z ≠ 0) (hlog : HasLogDerivBounds w W M)
    (b x y : E → ℝ) (ph s A T m : ℝ) (hbA : ∀ e, |b e| ≤ A) (hAW : A ≤ W)
    (hyT : ∀ e, b e ≠ 0 → |y e| ≤ T) (hm0 : 0 ≤ m) (hm1 : m ≤ 1)
    (hM : ∀ u : ℝ, |u| ≤ A → M u ≤ m) :
    ∃ f' f'' : ℝ → ℝ,
      (∀ t, HasDerivAt (lineFactor w c b x y ph s) (f' t) t) ∧
      (∀ t, HasDerivAt f' (f'' t) t) ∧
      (∀ t, |lineFactor w c b x y ph s t| ≤ 1) ∧
      (∀ t, |f' t| ≤ 2 * ((Finset.univ.filter fun e => b e ≠ 0).card * m * T) + 2 * |s|) ∧
      ∀ t, |f'' t| ≤ 4 * ((Finset.univ.filter fun e => b e ≠ 0).card ^ 2 * m * T ^ 2) +
        4 * |s| * ((Finset.univ.filter fun e => b e ≠ 0).card * m * T) + 2 * s ^ 2 := by
  classical
  set S := Finset.univ.filter fun e => b e ≠ 0 with hSdef
  set N : ℝ := (S.card : ℝ) with hN
  have hbW : ∀ e, |b e| ≤ W := fun e => (hbA e).trans hAW
  have haS : ∀ e ∈ S, |b e| ≤ W := fun e _ => hbW e
  have haA : ∀ e ∈ S, |b e| ≤ A := fun e _ => hbA e
  have hθT : ∀ e ∈ S, |y e| ≤ T := fun e he => hyT e (Finset.mem_filter.mp he).2
  set F₁ := genericLocalF₁ w c S b x y with hF₁
  set F₂ := genericLocalF₂ w c S b x y with hF₂
  -- first and second derivatives of the complex local functionals
  have hd₁ : ∀ t, HasDerivAt F₁ (deriv F₁ t) t := fun t =>
    (hasDerivAt_genericLocalF₁ hw hnzero b x y haS t).differentiableAt.hasDerivAt
  have hd₂ : ∀ t, HasDerivAt F₂ (deriv F₂ t) t := fun t =>
    (hasDerivAt_genericLocalF₂ hw hnzero b x y haS t).differentiableAt.hasDerivAt
  have hbneg : ∀ e ∈ S, |(-b) e| ≤ W := fun e he => by rw [Pi.neg_apply, abs_neg]; exact haS e he
  have hdd₁ : ∀ t, HasDerivAt (deriv F₁) (deriv (deriv F₁) t) t := by
    intro t
    have hp := hasDerivAt_deriv_genericEdgeProduct hw hnzero b x y haS t
    have hm := hasDerivAt_deriv_genericEdgeProduct hw hnzero (-b) x y hbneg t
    have hd : DifferentiableAt ℝ (deriv F₁) t := by
      rw [hF₁, deriv_genericLocalF₁ hw hnzero b x y haS]
      exact (((hp.sub hm).const_mul I).div_const 2).differentiableAt
    exact hd.hasDerivAt
  have hdd₂ : ∀ t, HasDerivAt (deriv F₂) (deriv (deriv F₂) t) t := by
    intro t
    have hp := hasDerivAt_deriv_genericEdgeProduct hw hnzero b x y haS t
    have hm := hasDerivAt_deriv_genericEdgeProduct hw hnzero (-b) x y hbneg t
    have hd : DifferentiableAt ℝ (deriv F₂) t := by
      rw [hF₂, deriv_genericLocalF₂ hw hnzero b x y haS]
      exact ((hp.add hm).div_const 2).differentiableAt
    exact hd.hasDerivAt
  have hbd := fun t => genericLocalF_bounds hw hnzero hlog b x y A T m t haA hAW hθT hm0 hm1 hM
  -- the real functions
  set f₁ : ℝ → ℝ := fun t => (F₁ t).re
  set f₂ : ℝ → ℝ := fun t => (F₂ t).re
  set d₁ : ℝ → ℝ := fun t => (deriv F₁ t).re
  set d₂ : ℝ → ℝ := fun t => (deriv F₂ t).re
  set e₁ : ℝ → ℝ := fun t => (deriv (deriv F₁) t).re
  set e₂ : ℝ → ℝ := fun t => (deriv (deriv F₂) t).re
  have hf₁ : ∀ t, HasDerivAt f₁ (d₁ t) t := fun t => hasDerivAt_re_of_hasDerivAt (hd₁ t)
  have hf₂ : ∀ t, HasDerivAt f₂ (d₂ t) t := fun t => hasDerivAt_re_of_hasDerivAt (hd₂ t)
  have hg₁ : ∀ t, HasDerivAt d₁ (e₁ t) t := fun t => hasDerivAt_re_of_hasDerivAt (hdd₁ t)
  have hg₂ : ∀ t, HasDerivAt d₂ (e₂ t) t := fun t => hasDerivAt_re_of_hasDerivAt (hdd₂ t)
  have hlin : ∀ t : ℝ, HasDerivAt (fun t : ℝ => ph + t * s) s t := fun t => by
    have := ((hasDerivAt_id t).mul_const s).const_add ph
    simpa using this
  have hcos : ∀ t : ℝ, HasDerivAt (fun t : ℝ => Real.cos (ph + t * s))
      (-Real.sin (ph + t * s) * s) t := fun t => (Real.hasDerivAt_cos _).comp t (hlin t)
  have hsin : ∀ t : ℝ, HasDerivAt (fun t : ℝ => Real.sin (ph + t * s))
      (Real.cos (ph + t * s) * s) t := fun t => (Real.hasDerivAt_sin _).comp t (hlin t)
  -- the line factor through the bridge
  have hline : lineFactor w c b x y ph s = fun t =>
      f₂ t * Real.cos (ph + t * s) + f₁ t * Real.sin (ph + t * s) := by
    funext t
    unfold lineFactor
    rw [localFactor_line_eq hw.cost_zero hw.ofReal_ne_zero b x y t]
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
      sub_zero, f₁, f₂, F₁, F₂, hSdef]
  set f' : ℝ → ℝ := fun t => d₂ t * Real.cos (ph + t * s) + f₂ t * (-Real.sin (ph + t * s) * s) +
    (d₁ t * Real.sin (ph + t * s) + f₁ t * (Real.cos (ph + t * s) * s)) with hf'
  set f'' : ℝ → ℝ := fun t =>
    e₂ t * Real.cos (ph + t * s) + d₂ t * (-Real.sin (ph + t * s) * s) +
      (d₂ t * (-Real.sin (ph + t * s) * s) + f₂ t * (-(Real.cos (ph + t * s) * s) * s)) +
    (e₁ t * Real.sin (ph + t * s) + d₁ t * (Real.cos (ph + t * s) * s) +
      (d₁ t * (Real.cos (ph + t * s) * s) + f₁ t * (-Real.sin (ph + t * s) * s * s))) with hf''
  refine ⟨f', f'', fun t => ?_, fun t => ?_, fun t => ?_, fun t => ?_, fun t => ?_⟩
  · rw [hline]
    exact ((hf₂ t).mul (hcos t)).add ((hf₁ t).mul (hsin t))
  · have hc' : HasDerivAt (fun t : ℝ => -Real.sin (ph + t * s) * s)
        (-(Real.cos (ph + t * s) * s) * s) t := ((hsin t).neg).mul_const s
    have hs' : HasDerivAt (fun t : ℝ => Real.cos (ph + t * s) * s)
        (-Real.sin (ph + t * s) * s * s) t := (hcos t).mul_const s
    exact (((hg₂ t).mul (hcos t)).add ((hf₂ t).mul hc')).add
      (((hg₁ t).mul (hsin t)).add ((hf₁ t).mul hs'))
  · unfold lineFactor
    exact (Complex.abs_re_le_norm _).trans
      (norm_localFactor_le_one hw.ratio_le b _ hbW _)
  · obtain ⟨⟨hF₁b, hF₂b⟩, ⟨hD₁b, hD₂b⟩, -⟩ := hbd t
    have a1 : |f₁ t| ≤ 1 := (Complex.abs_re_le_norm _).trans hF₁b
    have a2 : |f₂ t| ≤ 1 := (Complex.abs_re_le_norm _).trans hF₂b
    have b1 : |d₁ t| ≤ N * m * T := (Complex.abs_re_le_norm _).trans hD₁b
    have b2 : |d₂ t| ≤ N * m * T := (Complex.abs_re_le_norm _).trans hD₂b
    have cc := Real.abs_cos_le_one (ph + t * s)
    have ss := Real.abs_sin_le_one (ph + t * s)
    have hs0 := abs_nonneg s
    simp only [hf']
    calc |d₂ t * Real.cos (ph + t * s) + f₂ t * (-Real.sin (ph + t * s) * s) +
          (d₁ t * Real.sin (ph + t * s) + f₁ t * (Real.cos (ph + t * s) * s))|
        ≤ |d₂ t| * |Real.cos (ph + t * s)| + |f₂ t| * (|Real.sin (ph + t * s)| * |s|) +
          (|d₁ t| * |Real.sin (ph + t * s)| + |f₁ t| * (|Real.cos (ph + t * s)| * |s|)) := by
          refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans ?_)
            ((abs_add_le _ _).trans ?_))
          · rw [abs_mul, abs_mul, abs_mul, abs_neg]
          · rw [abs_mul, abs_mul, abs_mul]
      _ ≤ N * m * T * 1 + 1 * (1 * |s|) + (N * m * T * 1 + 1 * (1 * |s|)) := by
          have hB : 0 ≤ N * m * T := (abs_nonneg _).trans b1
          have j1 := mul_le_mul b2 cc (abs_nonneg _) hB
          have j2 := mul_le_mul a2 (mul_le_mul ss le_rfl hs0 zero_le_one) (by positivity)
            zero_le_one
          have j3 := mul_le_mul b1 ss (abs_nonneg _) hB
          have j4 := mul_le_mul a1 (mul_le_mul cc le_rfl hs0 zero_le_one) (by positivity)
            zero_le_one
          linarith
      _ = 2 * (N * m * T) + 2 * |s| := by ring
  · obtain ⟨⟨hF₁b, hF₂b⟩, ⟨hD₁b, hD₂b⟩, ⟨hE₁b, hE₂b⟩⟩ := hbd t
    have a1 : |f₁ t| ≤ 1 := (Complex.abs_re_le_norm _).trans hF₁b
    have a2 : |f₂ t| ≤ 1 := (Complex.abs_re_le_norm _).trans hF₂b
    have b1 : |d₁ t| ≤ N * m * T := (Complex.abs_re_le_norm _).trans hD₁b
    have b2 : |d₂ t| ≤ N * m * T := (Complex.abs_re_le_norm _).trans hD₂b
    have c1 : |e₁ t| ≤ 2 * N ^ 2 * m * T ^ 2 := (Complex.abs_re_le_norm _).trans hE₁b
    have c2 : |e₂ t| ≤ 2 * N ^ 2 * m * T ^ 2 := (Complex.abs_re_le_norm _).trans hE₂b
    have cc := Real.abs_cos_le_one (ph + t * s)
    have ss := Real.abs_sin_le_one (ph + t * s)
    have hs0 := abs_nonneg s
    have hB : 0 ≤ N * m * T := (abs_nonneg _).trans b1
    simp only [hf'']
    set C := Real.cos (ph + t * s)
    set Sn := Real.sin (ph + t * s)
    have key : |e₂ t * C + d₂ t * (-Sn * s) + (d₂ t * (-Sn * s) + f₂ t * (-(C * s) * s)) +
        (e₁ t * Sn + d₁ t * (C * s) + (d₁ t * (C * s) + f₁ t * (-Sn * s * s)))| ≤
        |e₂ t| * |C| + |d₂ t| * (|Sn| * |s|) + (|d₂ t| * (|Sn| * |s|) + |f₂ t| * (|C| * |s| * |s|)) +
        (|e₁ t| * |Sn| + |d₁ t| * (|C| * |s|) + (|d₁ t| * (|C| * |s|) +
          |f₁ t| * (|Sn| * |s| * |s|))) := by
      have t1 : |e₂ t * C| = |e₂ t| * |C| := abs_mul _ _
      have t2 : |d₂ t * (-Sn * s)| = |d₂ t| * (|Sn| * |s|) := by
        rw [abs_mul, abs_mul, abs_neg]
      have t3 : |f₂ t * (-(C * s) * s)| = |f₂ t| * (|C| * |s| * |s|) := by
        rw [abs_mul, abs_mul, abs_neg, abs_mul]
      have t4 : |e₁ t * Sn| = |e₁ t| * |Sn| := abs_mul _ _
      have t5 : |d₁ t * (C * s)| = |d₁ t| * (|C| * |s|) := by rw [abs_mul, abs_mul]
      have t6 : |f₁ t * (-Sn * s * s)| = |f₁ t| * (|Sn| * |s| * |s|) := by
        rw [abs_mul, abs_mul, abs_mul, abs_neg]
      calc _ ≤ |e₂ t * C + d₂ t * (-Sn * s) + (d₂ t * (-Sn * s) + f₂ t * (-(C * s) * s))| +
            |e₁ t * Sn + d₁ t * (C * s) + (d₁ t * (C * s) + f₁ t * (-Sn * s * s))| :=
            abs_add_le _ _
        _ ≤ (|e₂ t * C| + |d₂ t * (-Sn * s)| + (|d₂ t * (-Sn * s)| +
              |f₂ t * (-(C * s) * s)|)) +
            (|e₁ t * Sn| + |d₁ t * (C * s)| + (|d₁ t * (C * s)| +
              |f₁ t * (-Sn * s * s)|)) := by
            refine add_le_add ?_ ?_
            · refine (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) (abs_add_le _ _))
            · refine (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) (abs_add_le _ _))
        _ = _ := by rw [t1, t2, t3, t4, t5, t6]
    refine key.trans ?_
    have hC := abs_nonneg C
    have hSn := abs_nonneg Sn
    have i1 : |e₂ t| * |C| ≤ 2 * N ^ 2 * m * T ^ 2 :=
      (mul_le_mul c2 cc hC ((abs_nonneg _).trans c2)).trans (le_of_eq (mul_one _))
    have i2 : |e₁ t| * |Sn| ≤ 2 * N ^ 2 * m * T ^ 2 :=
      (mul_le_mul c1 ss hSn ((abs_nonneg _).trans c1)).trans (le_of_eq (mul_one _))
    have i3 : |d₂ t| * (|Sn| * |s|) ≤ N * m * T * |s| :=
      mul_le_mul b2 (by nlinarith) (by positivity) hB
    have i4 : |d₁ t| * (|C| * |s|) ≤ N * m * T * |s| :=
      mul_le_mul b1 (by nlinarith) (by positivity) hB
    have i5 : |f₂ t| * (|C| * |s| * |s|) ≤ s ^ 2 := by
      have : |C| * |s| * |s| ≤ s ^ 2 := by
        rw [← sq_abs s]; nlinarith
      calc |f₂ t| * (|C| * |s| * |s|) ≤ 1 * s ^ 2 :=
            mul_le_mul a2 this (by positivity) zero_le_one
        _ = s ^ 2 := one_mul _
    have i6 : |f₁ t| * (|Sn| * |s| * |s|) ≤ s ^ 2 := by
      have : |Sn| * |s| * |s| ≤ s ^ 2 := by
        rw [← sq_abs s]; nlinarith
      calc |f₁ t| * (|Sn| * |s| * |s|) ≤ 1 * s ^ 2 :=
            mul_le_mul a1 this (by positivity) zero_le_one
        _ = s ^ 2 := one_mul _
    nlinarith

/-- **One factor along the real shift** (FS81 (6.35)–(6.37)): for `|z| ≤ 1/8`,
`(1 + z f(0)) exp(z f'(0)/(1 + z f(0)) − 8|z|(s² + (N m T)² + N² m T²)) ≤ 1 + z f(1)`, with
`f = lineFactor` and `N` the number of edges carrying the shift. -/
theorem one_add_mul_lineFactor_ge (hw : IsStripWeight w W c)
    (hnzero : ∀ z : ℂ, |z.im| ≤ W → w z ≠ 0) (hlog : HasLogDerivBounds w W M)
    (b x y : E → ℝ) (ph s z A T m : ℝ) (hbA : ∀ e, |b e| ≤ A) (hAW : A ≤ W)
    (hyT : ∀ e, b e ≠ 0 → |y e| ≤ T) (hm0 : 0 ≤ m) (hm1 : m ≤ 1)
    (hM : ∀ u : ℝ, |u| ≤ A → M u ≤ m) (hz : |z| ≤ 1 / 8) :
    (1 + z * lineFactor w c b x y ph s 0) *
        Real.exp (z * deriv (lineFactor w c b x y ph s) 0 /
            (1 + z * lineFactor w c b x y ph s 0) -
          8 * |z| * (s ^ 2 + ((Finset.univ.filter fun e => b e ≠ 0).card * m * T) ^ 2 +
            (Finset.univ.filter fun e => b e ≠ 0).card ^ 2 * m * T ^ 2)) ≤
      1 + z * lineFactor w c b x y ph s 1 := by
  obtain ⟨f', f'', hf, hf', hf0, hf'b, hf''b⟩ :=
    lineFactor_derivs hw hnzero hlog b x y ph s A T m hbA hAW hyT hm0 hm1 hM
  set f := lineFactor w c b x y ph s with hfdef
  set N : ℝ := ((Finset.univ.filter fun e => b e ≠ 0).card : ℝ)
  set B := N * m * T with hBdef
  set Q := s ^ 2 + B ^ 2 + N ^ 2 * m * T ^ 2 with hQ
  have hQ2 : 0 ≤ N ^ 2 * m * T ^ 2 := by positivity
  have hz0 := abs_nonneg z
  have hD : ∀ t, 7 / 8 ≤ 1 + z * f t := by
    intro t
    have h1 : |z * f t| ≤ 1 / 8 := by
      rw [abs_mul]
      calc |z| * |f t| ≤ 1 / 8 * 1 := mul_le_mul hz (hf0 t) (abs_nonneg _) (by norm_num)
        _ = 1 / 8 := mul_one _
    linarith [neg_abs_le (z * f t)]
  have hDpos : ∀ t, 0 < 1 + z * f t := fun t => by linarith [hD t]
  -- `g = log (1 + z f)` and its derivatives
  set g : ℝ → ℝ := fun t => Real.log (1 + z * f t) with hg
  set g' : ℝ → ℝ := fun t => z * f' t / (1 + z * f t) with hg'
  set g'' : ℝ → ℝ := fun t =>
    (z * f'' t * (1 + z * f t) - z * f' t * (z * f' t)) / (1 + z * f t) ^ 2 with hg''
  have hgd : ∀ t, HasDerivAt g (g' t) t := by
    intro t
    have h := ((hf t).const_mul z).const_add 1
    exact ((Real.hasDerivAt_log (hDpos t).ne').comp t h).congr_deriv (by
      show (1 + z * f t)⁻¹ * (z * f' t) = z * f' t / (1 + z * f t)
      rw [div_eq_inv_mul])
  have hg'd : ∀ t, HasDerivAt g' (g'' t) t := by
    intro t
    have hn := (hf' t).const_mul z
    have hd := ((hf t).const_mul z).const_add 1
    have h := hn.div hd (hDpos t).ne'
    convert h using 1
  have hbound : ∀ t ∈ Set.Icc (0 : ℝ) 1, |g'' t| ≤ 16 * |z| * Q := by
    intro t _
    have hDt := hD t
    have hDp := hDpos t
    have h1 := hf'b t
    have h2 := hf''b t
    have hs := abs_nonneg s
    have hsplit : g'' t = z * f'' t / (1 + z * f t) - (z * f' t) ^ 2 / (1 + z * f t) ^ 2 := by
      simp only [hg'']
      field_simp
    rw [hsplit]
    have a1 : |z * f'' t / (1 + z * f t)| ≤ 8 / 7 * (|z| * |f'' t|) := by
      rw [abs_div, abs_mul, abs_of_pos hDp, div_le_iff₀ hDp]
      nlinarith [mul_nonneg hz0 (abs_nonneg (f'' t))]
    have a2 : |(z * f' t) ^ 2 / (1 + z * f t) ^ 2| ≤ 64 / 49 * (z ^ 2 * f' t ^ 2) := by
      rw [abs_div, abs_of_nonneg (sq_nonneg _), abs_of_pos (by positivity),
        div_le_iff₀ (by positivity)]
      have hD2 : (7 / 8 : ℝ) ^ 2 ≤ (1 + z * f t) ^ 2 := by
        exact pow_le_pow_left₀ (by norm_num) hDt 2
      have : 0 ≤ z ^ 2 * f' t ^ 2 := by positivity
      nlinarith
    have hzz : z ^ 2 ≤ |z| / 8 := by
      rw [← sq_abs]
      nlinarith
    have hf'sq : f' t ^ 2 ≤ 8 * B ^ 2 + 8 * s ^ 2 := by
      have : |f' t| ^ 2 ≤ (2 * B + 2 * |s|) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) h1 2
      rw [sq_abs] at this
      nlinarith [sq_abs s, sq_nonneg (B - |s|)]
    have hf''b' : |f'' t| ≤ 4 * (N ^ 2 * m * T ^ 2) + 2 * B ^ 2 + 4 * s ^ 2 := by
      nlinarith [sq_abs s, sq_nonneg (B - |s|)]
    calc |z * f'' t / (1 + z * f t) - (z * f' t) ^ 2 / (1 + z * f t) ^ 2|
        ≤ |z * f'' t / (1 + z * f t)| + |(z * f' t) ^ 2 / (1 + z * f t) ^ 2| :=
          abs_sub _ _
      _ ≤ 8 / 7 * (|z| * |f'' t|) + 64 / 49 * (z ^ 2 * f' t ^ 2) := add_le_add a1 a2
      _ ≤ 8 / 7 * (|z| * (4 * (N ^ 2 * m * T ^ 2) + 2 * B ^ 2 + 4 * s ^ 2)) +
          64 / 49 * (|z| / 8 * (8 * B ^ 2 + 8 * s ^ 2)) := by
          gcongr
      _ ≤ 16 * |z| * Q := by
          simp only [hQ]
          nlinarith [mul_nonneg hz0 hQ2, mul_nonneg hz0 (sq_nonneg B),
            mul_nonneg hz0 (sq_nonneg s)]
  have htay := taylor_lower_bound (fun t _ => hgd t) (fun t _ => hg'd t) hbound
  have hderiv : deriv f 0 = f' 0 := (hf 0).deriv
  rw [hderiv]
  have hexp1 : Real.exp (g 1) = 1 + z * f 1 := Real.exp_log (hDpos 1)
  have hexp0 : Real.exp (g 0) = 1 + z * f 0 := Real.exp_log (hDpos 0)
  calc (1 + z * f 0) * Real.exp (z * f' 0 / (1 + z * f 0) - 8 * |z| * Q)
      = Real.exp (g 0 + g' 0 - 16 * |z| * Q / 2) := by
        show _ = Real.exp (g 0 + z * f' 0 / (1 + z * f 0) - 16 * |z| * Q / 2)
        rw [show g 0 + z * f' 0 / (1 + z * f 0) - 16 * |z| * Q / 2 =
            g 0 + (z * f' 0 / (1 + z * f 0) - 8 * |z| * Q) by ring, Real.exp_add, hexp0]
    _ ≤ Real.exp (g 1) := Real.exp_le_exp.mpr htay
    _ = 1 + z * f 1 := hexp1

end FroehlichSpencer.BKT.Generic

end
