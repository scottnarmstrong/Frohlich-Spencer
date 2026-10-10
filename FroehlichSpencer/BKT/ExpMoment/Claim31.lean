/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Algebra.Order.ToIntervalMod
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# KP Claim 3.1

KP Claim 3.1, p. 14 (Kharash–Peled, first version).

The constant is the explicit `D₄ = 2`. The form `claim31_prod` includes the ensemble product
omitted in the printed proof.
The extra `z` in the printed expression `cos x cos y − z sin x sin y` is omitted: the
product identity uses `cos x cos y − sin x sin y`.
-/

@[expose] public section

namespace FroehlichSpencer.BKT

/-- The denominator in KP Claim 3.1 stays above `7/8`. -/
theorem claim31_denominator_ge (x z : ℝ) (hz : |z| < 1 / 8) : 7 / 8 < 1 + z * Real.cos x := by
  have h1 : |z * Real.cos x| ≤ |z| := by
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one x)
  have := (abs_le.mp h1).1
  linarith only [hz, this]

private lemma exp_sub_two_sq_le (t : ℝ) (ht : -1 / 2 ≤ t) :
    Real.exp (t - 2 * t ^ 2) ≤ 1 + t := by
  have h1 : 1 + (2 * t ^ 2 - t) ≤ Real.exp (2 * t ^ 2 - t) := by
    have := Real.add_one_le_exp (2 * t ^ 2 - t); linarith only [this]
  have hpos : 0 < Real.exp (2 * t ^ 2 - t) := Real.exp_pos _
  have h2 : Real.exp (t - 2 * t ^ 2) = (Real.exp (2 * t ^ 2 - t))⁻¹ := by
    rw [← Real.exp_neg]; congr 1; ring
  rw [h2, inv_le_iff_one_le_mul₀ hpos]
  have h3 : 1 ≤ (1 + t) * (1 + (2 * t ^ 2 - t)) := by
    nlinarith [sq_nonneg t, mul_nonneg (sq_nonneg t) (by linarith : 0 ≤ 1 + 2 * t)]
  have h4 : 0 ≤ 1 + t := by linarith only [ht]
  calc (1 : ℝ) ≤ (1 + t) * (1 + (2 * t ^ 2 - t)) := h3
    _ ≤ (1 + t) * Real.exp (2 * t ^ 2 - t) := mul_le_mul_of_nonneg_left h1 h4

private lemma claim31_msq (c s cy sy y2 : ℝ) (hc2 : c ^ 2 ≤ 1) (hs2 : s ^ 2 ≤ 1)
    (hcs : cy ^ 2 + sy ^ 2 = 1) (hu : 1 - cy ≤ y2 / 2) :
    (c * (cy - 1) - s * sy) ^ 2 ≤ 2 * y2 := by
  have e1 : (c * (cy - 1)) ^ 2 ≤ (1 - cy) ^ 2 := by
    rw [mul_pow]
    nlinarith only [hc2, sq_nonneg (cy - 1)]
  have e2 : (s * sy) ^ 2 ≤ sy ^ 2 := by
    rw [mul_pow]
    nlinarith only [hs2, sq_nonneg sy]
  have e3 : (1 - cy) ^ 2 + sy ^ 2 = 2 * (1 - cy) := by nlinarith only [hcs]
  nlinarith only [hu, e1, e2, e3, sq_nonneg (c * (cy - 1) + s * sy)]

private lemma claim31_wsq (z w : ℝ) (hwabs : |w| ≤ 8 / 7 * |z|) :
    w ^ 2 ≤ 64 / 49 * z ^ 2 := by
  have : w ^ 2 = |w| ^ 2 := (sq_abs w).symm
  rw [this]
  have : z ^ 2 = |z| ^ 2 := (sq_abs z).symm
  rw [this]
  nlinarith only [hwabs, abs_nonneg w]

private lemma claim31_aux (z c s cy sy y2 : ℝ) (hz : |z| < 1 / 8) (hc : |c| ≤ 1) (hs : |s| ≤ 1)
    (hcs : cy ^ 2 + sy ^ 2 = 1) (hu : 1 - cy ≤ y2 / 2) (hcy : cy ≤ 1) (hD : 7 / 8 < 1 + z * c) :
    -(z * s * sy) / (1 + z * c) - 2 * |z| * y2 ≤
        z / (1 + z * c) * (c * (cy - 1) - s * sy) -
          2 * (z / (1 + z * c) * (c * (cy - 1) - s * sy)) ^ 2 ∧
      -1 / 2 ≤ z / (1 + z * c) * (c * (cy - 1) - s * sy) := by
  set D := 1 + z * c with hDdef
  have hDpos : 0 < D := by linarith only [hD]
  set w := z / D with hw
  have hwabs : |w| ≤ 8 / 7 * |z| := by
    rw [hw, abs_div, abs_of_pos hDpos, div_le_iff₀ hDpos]
    nlinarith only [hD, abs_nonneg z]
  have hzn := abs_nonneg z
  have hc2 : c ^ 2 ≤ 1 := by
    have := sq_le_one_iff_abs_le_one c; exact this.mpr hc
  have hs2 : s ^ 2 ≤ 1 := by
    have := sq_le_one_iff_abs_le_one s; exact this.mpr hs
  have hu0 : 0 ≤ 1 - cy := by linarith only [hcy]
  have hy2 : 0 ≤ y2 := by linarith only [hu, hcy]
  have hcy1 : -1 ≤ cy := by nlinarith only [hcs, sq_nonneg sy]
  have hsy2 : sy ^ 2 ≤ 1 := by nlinarith only [hcs, sq_nonneg cy]
  have hsyabs : |sy| ≤ 1 := abs_le_one_iff_mul_self_le_one.mpr (by nlinarith only [hsy2])
  -- bound on m
  have hA : |c * (cy - 1)| ≤ 1 - cy := by
    rw [abs_mul, abs_sub_comm, abs_of_nonneg hu0]
    exact mul_le_of_le_one_left hu0 hc
  have hB : |s * sy| ≤ 1 := by
    rw [abs_mul]
    calc |s| * |sy| ≤ 1 * 1 := mul_le_mul hs hsyabs (abs_nonneg _) zero_le_one
      _ = 1 := by norm_num
  have hm : |c * (cy - 1) - s * sy| ≤ 3 := by
    calc |c * (cy - 1) - s * sy| ≤ |c * (cy - 1)| + |s * sy| := abs_sub _ _
      _ ≤ 3 := by linarith only [hcy1, hA, hB]
  have ht : |w * (c * (cy - 1) - s * sy)| ≤ 3 / 7 := by
    rw [abs_mul]
    calc |w| * |c * (cy - 1) - s * sy| ≤ (8 / 7 * |z|) * 3 :=
          mul_le_mul hwabs hm (abs_nonneg _) (by positivity)
      _ ≤ 3 / 7 := by linarith only [hz]
  have ht1 : -1 / 2 ≤ w * (c * (cy - 1) - s * sy) := by
    have := (abs_le.mp ht).1; linarith only [this]
  refine ⟨?_, ht1⟩
  -- quadratic bound
  have hm2 := claim31_msq c s cy sy y2 hc2 hs2 hcs hu
  have hw2 := claim31_wsq z w hwabs
  have hz2 : z ^ 2 ≤ |z| / 8 := by
    rw [← sq_abs z]; nlinarith only [hz, hzn]
  have ht2 : (w * (c * (cy - 1) - s * sy)) ^ 2 ≤ 2 * (64 / 49 * z ^ 2) * y2 := by
    rw [mul_pow]
    have := mul_le_mul hw2 hm2 (sq_nonneg _) (by positivity)
    nlinarith only [this]
  have hAb : |w * (c * (cy - 1))| ≤ 4 / 7 * |z| * y2 := by
    rw [abs_mul]
    calc |w| * |c * (cy - 1)| ≤ (8 / 7 * |z|) * (1 - cy) :=
          mul_le_mul hwabs hA (abs_nonneg _) (by positivity)
      _ ≤ (8 / 7 * |z|) * (y2 / 2) := mul_le_mul_of_nonneg_left hu (by positivity)
      _ = 4 / 7 * |z| * y2 := by ring
  have hAl := (abs_le.mp hAb).1
  have hsplit : w * (c * (cy - 1) - s * sy) = w * (c * (cy - 1)) + -(z * s * sy) / D := by
    rw [hw]; field_simp; ring
  have hzy : z ^ 2 * y2 ≤ |z| / 8 * y2 := mul_le_mul_of_nonneg_right hz2 hy2
  have hzy' : 0 ≤ |z| * y2 := mul_nonneg hzn hy2
  rw [hsplit] at ht2 ⊢
  generalize w * (c * (cy - 1)) = A at *
  generalize -(z * s * sy) / D = B at *
  have h7 : z ^ 2 * y2 ≤ |z| * y2 / 8 := by linarith only [hzy]
  have h8 : (A + B) ^ 2 ≤ 128 / 49 * (z ^ 2 * y2) :=
    ht2.trans_eq (by ring)
  have h9 : 2 * (A + B) ^ 2 ≤ 32 / 49 * (|z| * y2) := by linarith only [h7, h8]
  have h10 : -(4 / 7 * |z| * y2) = -(4 / 7 * (|z| * y2)) := by ring
  have h11 : 2 * |z| * y2 = 2 * (|z| * y2) := by ring
  linarith only [h9, h10, h11, hAl, hzy', ht2]

/-- KP Claim 3.1 (p. 14) with the explicit absolute constant `D₄ = 2`, for every `|z| < 1/8`. -/
theorem claim31 (x y z : ℝ) (hz : |z| < 1 / 8) :
    Real.exp (-(z * Real.sin x * Real.sin y) / (1 + z * Real.cos x) - 2 * |z| * y ^ 2) *
        (1 + z * Real.cos x) ≤ 1 + z * Real.cos (x + y) := by
  have hD := claim31_denominator_ge x z hz
  have hDpos : 0 < 1 + z * Real.cos x := by linarith only [hD]
  obtain ⟨h1, h2⟩ := claim31_aux z (Real.cos x) (Real.sin x) (Real.cos y) (Real.sin y) (y ^ 2) hz
    (Real.abs_cos_le_one x) (Real.abs_sin_le_one x)
    (by rw [add_comm]; exact Real.sin_sq_add_cos_sq y)
    (by linarith only [Real.one_sub_sq_div_two_le_cos (x := y)]) (Real.cos_le_one y) hD
  have h3 := exp_sub_two_sq_le _ h2
  have h4 : Real.exp (-(z * Real.sin x * Real.sin y) / (1 + z * Real.cos x) - 2 * |z| * y ^ 2) ≤
      1 + z / (1 + z * Real.cos x) * (Real.cos x * (Real.cos y - 1) - Real.sin x * Real.sin y) :=
    (Real.exp_le_exp.mpr h1).trans h3
  have h5 : (1 + z * Real.cos x) *
      (1 + z / (1 + z * Real.cos x) * (Real.cos x * (Real.cos y - 1) -
        Real.sin x * Real.sin y)) = 1 + z * Real.cos (x + y) := by
    rw [Real.cos_add]; field_simp; ring
  calc _ ≤ (1 + z / (1 + z * Real.cos x) * (Real.cos x * (Real.cos y - 1) -
        Real.sin x * Real.sin y)) * (1 + z * Real.cos x) := mul_le_mul_of_nonneg_right h4 hDpos.le
    _ = _ := by rw [mul_comm]; exact h5

/-- KP Claim 3.1 in its printed quantifier form: an absolute constant `D₄ > 0`. -/
theorem exists_claim31_const : ∃ D₄ : ℝ, 0 < D₄ ∧ ∀ x y z : ℝ, 0 < |z| → |z| < 1 / 8 →
    Real.exp (-(z * Real.sin x * Real.sin y) / (1 + z * Real.cos x) - D₄ * |z| * y ^ 2) *
        (1 + z * Real.cos x) ≤ 1 + z * Real.cos (x + y) :=
  ⟨2, by norm_num, fun x y z _ hz => claim31 x y z hz⟩

/-- KP Claim 3.1 multiplied over a finite family (the ensemble product of KP p. 15). -/
theorem claim31_prod {ι : Type*} (s : Finset ι) (x y z : ι → ℝ) (hz : ∀ i ∈ s, |z i| < 1 / 8) :
    Real.exp (∑ i ∈ s, (-(z i * Real.sin (x i) * Real.sin (y i)) / (1 + z i * Real.cos (x i)) -
        2 * |z i| * y i ^ 2)) * ∏ i ∈ s, (1 + z i * Real.cos (x i)) ≤
      ∏ i ∈ s, (1 + z i * Real.cos (x i + y i)) := by
  rw [Real.exp_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod₀ (fun i hi => ?_) (fun i hi => claim31 (x i) (y i) (z i) (hz i hi))
  have := claim31_denominator_ge (x i) (z i) (hz i hi)
  exact mul_nonneg (Real.exp_pos _).le (by linarith only [this])

/-- The modular form used for KP (6.6): the quadratic error only sees the reduced phase
`[y]_{2π} ∈ [-π, π)`, while the linear term keeps `sin y`. -/
theorem claim31_mod (x y z : ℝ) (hz : |z| < 1 / 8) :
    Real.exp (-(z * Real.sin x * Real.sin y) / (1 + z * Real.cos x) -
        2 * |z| * (toIcoMod Real.two_pi_pos (-Real.pi) y) ^ 2) * (1 + z * Real.cos x) ≤
      1 + z * Real.cos (x + y) := by
  set yh := toIcoMod Real.two_pi_pos (-Real.pi) y with hyh
  obtain ⟨n, hn⟩ : ∃ n : ℤ, y = yh + n * (2 * Real.pi) := by
    refine ⟨toIcoDiv Real.two_pi_pos (-Real.pi) y, ?_⟩
    have := self_sub_toIcoMod Real.two_pi_pos (-Real.pi) y
    rw [zsmul_eq_mul] at this
    linarith only [this]
  have hs : Real.sin y = Real.sin yh := by rw [hn]; exact Real.sin_add_int_mul_two_pi _ _
  have hc : Real.cos (x + y) = Real.cos (x + yh) := by
    rw [hn, ← add_assoc]; exact Real.cos_add_int_mul_two_pi _ _
  have h := claim31 x yh z hz
  rw [hs, hc]
  exact h

end FroehlichSpencer.BKT

end
