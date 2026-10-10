/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.Infra.Green.Basic

/-!
# Combes–Thomas bound in finite volume

For a Hermitian kernel `a` of range one (with respect to a pseudo-distance `d`) and row bound `K`,
every entry of the finite-volume resolvent decays exponentially in `d`, with constants depending
only on `K` and `|Im z|`, uniformly in the finite set `Λ` and the potential `v`:
`|G_Λ(z; x, y)| ≤ (2/η) exp(-μ d(x, y))`, `μ = log (1 + η / (2 (K + 1)))`, `η = |Im z|`.

Motivation: (1.28) and Appendix B of Fröhlich–Spencer (1983), Fröhlich–Spencer (1983).
-/

@[expose] public section

open Matrix

namespace FroehlichSpencer.Infra

section Helpers

/-- Cauchy–Schwarz with nonnegative weights. -/
private lemma sq_sum_mul_le {ι : Type*} (s : Finset ι) (w t : ι → ℝ) (hw : ∀ i, 0 ≤ w i) :
    (∑ i ∈ s, w i * t i) ^ 2 ≤ (∑ i ∈ s, w i) * ∑ i ∈ s, w i * t i ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq s (fun i => Real.sqrt (w i))
    (fun i => Real.sqrt (w i) * t i)
  have e1 : ∀ i, Real.sqrt (w i) * (Real.sqrt (w i) * t i) = w i * t i := fun i => by
    rw [← mul_assoc, Real.mul_self_sqrt (hw i)]
  have e2 : ∀ i, Real.sqrt (w i) ^ 2 = w i := fun i => Real.sq_sqrt (hw i)
  have e3 : ∀ i, (Real.sqrt (w i) * t i) ^ 2 = w i * t i ^ 2 := fun i => by
    rw [mul_pow, e2]
  simpa only [e1, e2, e3] using h

/-- Schur test in squared form. -/
private lemma sum_norm_sq_mulVec_le {m n : Type*} [Fintype m] [Fintype n] (M : Matrix m n ℂ)
    {R C : ℝ} (hR0 : 0 ≤ R) (hR : ∀ i, ∑ j, ‖M i j‖ ≤ R) (hC : ∀ j, ∑ i, ‖M i j‖ ≤ C)
    (u : n → ℂ) : ∑ i, ‖(M *ᵥ u) i‖ ^ 2 ≤ R * C * ∑ j, ‖u j‖ ^ 2 := by
  have hrow : ∀ i, ‖(M *ᵥ u) i‖ ^ 2 ≤ R * ∑ j, ‖M i j‖ * ‖u j‖ ^ 2 := fun i => by
    have h1 : ‖(M *ᵥ u) i‖ ≤ ∑ j, ‖M i j‖ * ‖u j‖ := by
      rw [Matrix.mulVec, dotProduct]
      refine (norm_sum_le _ _).trans (le_of_eq ?_)
      exact Finset.sum_congr rfl fun j _ => norm_mul _ _
    calc ‖(M *ᵥ u) i‖ ^ 2 ≤ (∑ j, ‖M i j‖ * ‖u j‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ (∑ j, ‖M i j‖) * ∑ j, ‖M i j‖ * ‖u j‖ ^ 2 :=
          sq_sum_mul_le _ _ _ fun j => norm_nonneg _
      _ ≤ R * ∑ j, ‖M i j‖ * ‖u j‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (hR i)
            (Finset.sum_nonneg fun j _ => mul_nonneg (norm_nonneg _) (sq_nonneg _))
  calc ∑ i, ‖(M *ᵥ u) i‖ ^ 2 ≤ ∑ i, R * ∑ j, ‖M i j‖ * ‖u j‖ ^ 2 :=
        Finset.sum_le_sum fun i _ => hrow i
    _ = R * ∑ j, (∑ i, ‖M i j‖) * ‖u j‖ ^ 2 := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        simp only [Finset.sum_mul]
    _ ≤ R * ∑ j, C * ‖u j‖ ^ 2 := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => ?_) hR0
        exact mul_le_mul_of_nonneg_right (hC j) (sq_nonneg _)
    _ = R * C * ∑ j, ‖u j‖ ^ 2 := by rw [← Finset.mul_sum, mul_assoc]

/-- Schur test in norm form, for the `ℓ²` norm on plain vectors. -/
private lemma norm_toLp_mulVec_le {m n : Type*} [Fintype m] [Fintype n] (M : Matrix m n ℂ)
    {R : ℝ} (hR0 : 0 ≤ R) (hR : ∀ i, ∑ j, ‖M i j‖ ≤ R) (hC : ∀ j, ∑ i, ‖M i j‖ ≤ R)
    (u : n → ℂ) : ‖WithLp.toLp 2 (M *ᵥ u)‖ ≤ R * ‖WithLp.toLp 2 u‖ := by
  have h := sum_norm_sq_mulVec_le M hR0 hR hC u
  rw [← sq_le_sq₀ (norm_nonneg _) (mul_nonneg hR0 (norm_nonneg _)), mul_pow,
    norm_toLp_sq, norm_toLp_sq, re_star_dotProduct_self_eq_sum_norm_sq,
    re_star_dotProduct_self_eq_sum_norm_sq]
  calc _ ≤ _ := h
    _ = _ := by ring

/-- Lower bound for a nonreal shift of a Hermitian matrix. -/
private lemma abs_im_mul_norm_toLp_le {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ}
    (hH : H.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) (u : ι → ℂ) :
    |z.im| * ‖WithLp.toLp 2 u‖ ≤ ‖WithLp.toLp 2 ((H - z • (1 : Matrix ι ι ℂ)) *ᵥ u)‖ := by
  have hU := FroehlichSpencer.Matrix.IsHermitian.isUnit_sub_zsmul_one_of_im_ne_zero H hH z hz
  have hinv : (H - z • (1 : Matrix ι ι ℂ))⁻¹ *ᵥ ((H - z • (1 : Matrix ι ι ℂ)) *ᵥ u) = u := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hU),
      Matrix.one_mulVec]
  have h := re_star_dotProduct_inv_mulVec_le hH hz ((H - z • (1 : Matrix ι ι ℂ)) *ᵥ u)
  rw [hinv] at h
  have hpos : 0 < |z.im| := abs_pos.mpr hz
  rw [← norm_toLp_sq, ← norm_toLp_sq, ← sq_abs z.im, le_div_iff₀ (by positivity)] at h
  rw [← sq_le_sq₀ (by positivity) (norm_nonneg _), mul_pow]
  linarith only [h]

/-- Exponential weights change by at most `e^μ - 1` over a unit step. -/
private lemma abs_exp_mul_sub_one_le {μ t : ℝ} (hμ : 0 ≤ μ) (ht : |t| ≤ 1) :
    |Real.exp (μ * t) - 1| ≤ Real.exp μ - 1 := by
  rw [abs_le] at ht
  have h1 : Real.exp (μ * t) ≤ Real.exp μ := Real.exp_le_exp.mpr (by nlinarith only [ht.2, hμ])
  have h2 : Real.exp (-μ) ≤ Real.exp (μ * t) :=
    Real.exp_le_exp.mpr (by nlinarith only [ht.1, hμ])
  have h3 : 1 ≤ Real.exp μ := Real.one_le_exp hμ
  have h4 : Real.exp (-μ) * Real.exp μ = 1 := by rw [← Real.exp_add]; simp
  have h5 : 0 < Real.exp (-μ) := Real.exp_pos _
  rw [abs_sub_le_iff]
  refine ⟨by linarith only [h1], ?_⟩
  nlinarith only [h2, h3, h4, h5]

end Helpers

section Core

variable {X : Type*} [DecidableEq X] {a : X → X → ℂ}

/-- The conjugated-off-diagonal perturbation `B u u' = a u u' (e^{μ (d u y - d u' y)} - 1)`. -/
private noncomputable def weightPerturbation (a : X → X → ℂ) (d : X → X → ℝ) (μ : ℝ) (y : X)
    (Λ : Finset X) : Matrix Λ Λ ℂ :=
  Matrix.of fun u u' => a u u' * ((Real.exp (μ * (d u y - d u' y)) - 1 : ℝ) : ℂ)

private lemma weight_identity (v : X → ℝ) (Λ : Finset X) (z : ℂ) (d : X → X → ℝ) (μ : ℝ)
    (y : X) (g : Λ → ℂ) (u : Λ) :
    ((restrictedOp a v Λ - z • (1 : Matrix Λ Λ ℂ)) *ᵥ
        (fun u' : Λ => ((Real.exp (μ * d u' y) : ℝ) : ℂ) * g u')) u +
      (weightPerturbation a d μ y Λ *ᵥ
        (fun u' : Λ => ((Real.exp (μ * d u' y) : ℝ) : ℂ) * g u')) u =
    ((Real.exp (μ * d u y) : ℝ) : ℂ) * ((restrictedOp a v Λ - z • (1 : Matrix Λ Λ ℂ)) *ᵥ g) u := by
  rw [Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, Matrix.one_mulVec]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Finset.mul_sum,
    mul_sub]
  have hterm : ∀ u' : Λ,
      restrictedOp a v Λ u u' * (((Real.exp (μ * d u' y) : ℝ) : ℂ) * g u') +
        weightPerturbation a d μ y Λ u u' * (((Real.exp (μ * d u' y) : ℝ) : ℂ) * g u') =
      ((Real.exp (μ * d u y) : ℝ) : ℂ) * (restrictedOp a v Λ u u' * g u') := by
    intro u'
    have hE : ((Real.exp (μ * (d u y - d u' y)) : ℝ) : ℂ) * ((Real.exp (μ * d u' y) : ℝ) : ℂ) =
        ((Real.exp (μ * d u y) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, ← Real.exp_add]
      congr 2
      ring
    rw [restrictedOp_apply]
    unfold weightPerturbation
    simp only [Matrix.of_apply, Complex.ofReal_sub, Complex.ofReal_one]
    by_cases h : u = u'
    · subst h
      simp only [ite_true]
      rw [sub_self, mul_zero, Real.exp_zero, Complex.ofReal_one]
      ring
    · simp only [h, ite_false, add_zero]
      linear_combination (a u u' * g u') * hE
  rw [sub_add_eq_add_sub, ← Finset.sum_add_distrib,
    Finset.sum_congr rfl fun u' _ => hterm u']
  ring

omit [DecidableEq X] in
private lemma norm_weightPerturbation_le (ha : ∀ x y, a y x = star (a x y))
    {d : X → X → ℝ} (hd : ∀ x y w, d x y ≤ d x w + d w y)
    (hrange : ∀ x y, a x y ≠ 0 → d x y ≤ 1) {μ : ℝ} (hμ : 0 ≤ μ) (y : X) (Λ : Finset X)
    (u u' : Λ) : ‖weightPerturbation a d μ y Λ u u'‖ ≤ ‖a u u'‖ * (Real.exp μ - 1) := by
  unfold weightPerturbation
  rw [Matrix.of_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  by_cases h : a u u' = 0
  · simp [h]
  · refine mul_le_mul_of_nonneg_left (abs_exp_mul_sub_one_le hμ ?_) (norm_nonneg _)
    have h' : a u' u ≠ 0 := by
      rw [ha u u', star_ne_zero]
      exact h
    have h1 := hd u y u'
    have h2 := hd u' y u
    have h3 := hrange u u' h
    have h4 := hrange u' u h'
    rw [abs_le]
    constructor <;> linarith only [h1, h2, h3, h4]

end Core

section Main

variable {X : Type*} [DecidableEq X] {a : X → X → ℂ} {K : ℝ}

theorem log_one_add_div_pos {K : ℝ} (hK : 0 ≤ K) {z : ℂ} (hz : z.im ≠ 0) :
    0 < Real.log (1 + |z.im| / (2 * (K + 1))) := by
  have hη : 0 < |z.im| := abs_pos.mpr hz
  apply Real.log_pos
  have : 0 < |z.im| / (2 * (K + 1)) := by positivity
  linarith only [this]

/-- Combes–Thomas core: the exponential bound for any shift `z` with `H_Λ - z` invertible and
bounded below by `c > 0`. (`hdet` follows from `hlow`; the version without it is
`norm_resolventColumn_le_exp_of_lower_bound` in `Green/CombesThomasGap.lean`.) -/
theorem combesThomas_core (ha : ∀ x y, a y x = star (a x y))
    (hK : ∀ x (s : Finset X), ∑ y ∈ s, ‖a x y‖ ≤ K)
    {d : X → X → ℝ} (hd : ∀ x y w, d x y ≤ d x w + d w y) (hd0 : ∀ x, d x x = 0)
    (hrange : ∀ x y, a x y ≠ 0 → d x y ≤ 1) (v : X → ℝ) (Λ : Finset X) {z : ℂ} {c : ℝ} (hη : 0 < c)
    (hdet : IsUnit (restrictedOp a v Λ - z • (1 : Matrix Λ Λ ℂ)).det)
    (hlow : ∀ u : Λ → ℂ, c * ‖WithLp.toLp 2 u‖ ≤
      ‖WithLp.toLp 2 ((restrictedOp a v Λ - z • (1 : Matrix Λ Λ ℂ)) *ᵥ u)‖) (x y : X) :
    ‖resolventColumn a v Λ z y x‖ ≤
      2 / c * Real.exp (-Real.log (1 + c / (2 * (K + 1))) * d x y) := by
  have hK0 : 0 ≤ K := by simpa using hK x ∅
  by_cases hx : x ∈ Λ
  swap
  · rw [resolventColumn_of_notMem_left a v z y hx, norm_zero]
    positivity
  by_cases hy : y ∈ Λ
  swap
  · rw [resolventColumn_of_notMem_right a v z x hy, norm_zero]
    positivity
  set η := c with hηdef
  set μ := Real.log (1 + η / (2 * (K + 1))) with hμdef
  have hμe : Real.exp μ = 1 + η / (2 * (K + 1)) :=
    Real.exp_log (by positivity)
  have hμ0 : 0 ≤ μ := (Real.log_pos (by
    have : 0 < η / (2 * (K + 1)) := by positivity
    linarith only [this])).le
  have hKμ : K * (Real.exp μ - 1) ≤ η / 2 := by
    have h1 : K / (K + 1) ≤ 1 := by
      rw [div_le_one (by linarith)]
      linarith
    calc K * (Real.exp μ - 1) = η / 2 * (K / (K + 1)) := by
          rw [hμe]
          field_simp
          ring
      _ ≤ η / 2 * 1 := by gcongr
      _ = η / 2 := mul_one _
  have hR0 : 0 ≤ K * (Real.exp μ - 1) :=
    mul_nonneg hK0 (by linarith only [Real.add_one_le_exp μ, hμ0])
  have hexp1 : 0 ≤ Real.exp μ - 1 := by linarith only [Real.add_one_le_exp μ, hμ0]
  set Bm := weightPerturbation a d μ y Λ with hBm
  have hrow : ∀ u : Λ, ∑ u', ‖Bm u u'‖ ≤ K * (Real.exp μ - 1) := fun u => by
    calc ∑ u', ‖Bm u u'‖ ≤ ∑ u' : Λ, ‖a u u'‖ * (Real.exp μ - 1) :=
          Finset.sum_le_sum fun u' _ => norm_weightPerturbation_le ha hd hrange hμ0 y Λ u u'
      _ = (∑ u' ∈ Λ, ‖a u u'‖) * (Real.exp μ - 1) := by
          rw [← Finset.sum_mul]
          congr 1
          exact Finset.sum_coe_sort Λ (fun w => ‖a u w‖)
      _ ≤ K * (Real.exp μ - 1) := mul_le_mul_of_nonneg_right (hK u Λ) hexp1
  have hcol : ∀ u' : Λ, ∑ u, ‖Bm u u'‖ ≤ K * (Real.exp μ - 1) := fun u' => by
    calc ∑ u, ‖Bm u u'‖ ≤ ∑ u : Λ, ‖a u' u‖ * (Real.exp μ - 1) :=
          Finset.sum_le_sum fun u _ => by
            have h := norm_weightPerturbation_le ha hd hrange hμ0 y Λ u u'
            rwa [ha u' u, norm_star] at h
      _ = (∑ u ∈ Λ, ‖a u' u‖) * (Real.exp μ - 1) := by
          rw [← Finset.sum_mul]
          congr 1
          exact Finset.sum_coe_sort Λ (fun w => ‖a u' w‖)
      _ ≤ K * (Real.exp μ - 1) := mul_le_mul_of_nonneg_right (hK u' Λ) hexp1
  -- the column and its weighted version
  set H := restrictedOp a v Λ with hH
  set e : Λ → ℂ := Pi.single ⟨y, hy⟩ 1 with he
  set g : Λ → ℂ := (H - z • (1 : Matrix Λ Λ ℂ))⁻¹ *ᵥ e with hg
  have hge : (H - z • (1 : Matrix Λ Λ ℂ)) *ᵥ g = e := by
    rw [hg, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  set ψ : Λ → ℂ := fun u' => ((Real.exp (μ * d u' y) : ℝ) : ℂ) * g u' with hψ
  have hid : (H - z • (1 : Matrix Λ Λ ℂ)) *ᵥ ψ + Bm *ᵥ ψ = e := by
    funext u
    rw [Pi.add_apply, weight_identity v Λ z d μ y g u, hge]
    by_cases hu : u = ⟨y, hy⟩
    · subst hu
      simp [he, hd0]
    · simp [he, hu]
  have hn1 : ‖WithLp.toLp 2 e‖ ≤ 1 := by
    rw [← sq_le_one_iff₀ (norm_nonneg _), norm_toLp_sq, re_star_dotProduct_self_eq_sum_norm_sq]
    have h1 : ∑ i, ‖e i‖ ^ 2 = 1 := by
      rw [Finset.sum_eq_single ⟨y, hy⟩]
      · simp [he]
      · intro b _ hb
        simp [he, hb]
      · simp
    exact h1.le
  have hlow := hlow ψ
  have hB := norm_toLp_mulVec_le Bm hR0 hrow hcol ψ
  have hsub : (H - z • (1 : Matrix Λ Λ ℂ)) *ᵥ ψ = e - Bm *ᵥ ψ := eq_sub_of_add_eq hid
  rw [hsub, WithLp.toLp_sub] at hlow
  have hψn : ‖WithLp.toLp 2 ψ‖ ≤ 2 / η := by
    have h1 := norm_sub_le (WithLp.toLp 2 e) (WithLp.toLp 2 (Bm *ᵥ ψ))
    rw [le_div_iff₀ hη]
    nlinarith only [hlow, h1, hB, hn1, hKμ, norm_nonneg (WithLp.toLp 2 ψ), hηdef, hη]
  have hcomp : ‖ψ ⟨x, hx⟩‖ ≤ ‖WithLp.toLp 2 ψ‖ := PiLp.norm_apply_le (WithLp.toLp 2 ψ) ⟨x, hx⟩
  have hgx : resolventColumn a v Λ z y x = g ⟨x, hx⟩ := by
    rw [resolventColumn_of_mem a v z hx hy, hg, he, Matrix.mulVec_single_one]
    rfl
  have hnorm : ‖ψ ⟨x, hx⟩‖ = Real.exp (μ * d x y) * ‖g ⟨x, hx⟩‖ := by
    simp only [hψ, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hexp : Real.exp (μ * d x y) * Real.exp (-(μ * d x y)) = 1 := by
    rw [← Real.exp_add]; simp
  rw [hgx, neg_mul]
  calc ‖g ⟨x, hx⟩‖ = ‖ψ ⟨x, hx⟩‖ * Real.exp (-(μ * d x y)) := by
        rw [hnorm, mul_comm, ← mul_assoc, mul_comm _ (Real.exp _), hexp, one_mul]
    _ ≤ 2 / η * Real.exp (-(μ * d x y)) :=
        mul_le_mul_of_nonneg_right (hcomp.trans hψn) (Real.exp_pos _).le

theorem norm_resolventColumn_le_exp (ha : ∀ x y, a y x = star (a x y))
    (hK : ∀ x (s : Finset X), ∑ y ∈ s, ‖a x y‖ ≤ K)
    {d : X → X → ℝ} (hd : ∀ x y w, d x y ≤ d x w + d w y) (hd0 : ∀ x, d x x = 0)
    (hrange : ∀ x y, a x y ≠ 0 → d x y ≤ 1) (v : X → ℝ) (Λ : Finset X) {z : ℂ} (hz : z.im ≠ 0)
    (x y : X) :
    ‖resolventColumn a v Λ z y x‖ ≤
      2 / |z.im| * Real.exp (-Real.log (1 + |z.im| / (2 * (K + 1))) * d x y) := by
  have hη : 0 < |z.im| := abs_pos.mpr hz
  have hHerm := isHermitian_restrictedOp ha v Λ
  exact combesThomas_core ha hK hd hd0 hrange v Λ hη
    ((Matrix.isUnit_iff_isUnit_det _).mp
      (FroehlichSpencer.Matrix.IsHermitian.isUnit_sub_zsmul_one_of_im_ne_zero _ hHerm z hz))
    (abs_im_mul_norm_toLp_le hHerm hz) x y

/-- Uniformity: the constants depend only on `K` and `z`. -/
theorem exists_norm_resolventColumn_le_exp (K : ℝ) (hK0 : 0 ≤ K) {z : ℂ} (hz : z.im ≠ 0) :
    ∃ C μ : ℝ, 0 < C ∧ 0 < μ ∧ ∀ (a : X → X → ℂ), (∀ x y, a y x = star (a x y)) →
      (∀ x (s : Finset X), ∑ y ∈ s, ‖a x y‖ ≤ K) → ∀ (d : X → X → ℝ),
      (∀ x y w, d x y ≤ d x w + d w y) → (∀ x, d x x = 0) → (∀ x y, a x y ≠ 0 → d x y ≤ 1) →
      ∀ (v : X → ℝ) (Λ : Finset X) (x y : X),
        ‖resolventColumn a v Λ z y x‖ ≤ C * Real.exp (-μ * d x y) := by
  have hη : 0 < |z.im| := abs_pos.mpr hz
  exact ⟨2 / |z.im|, Real.log (1 + |z.im| / (2 * (K + 1))), by positivity,
    log_one_add_div_pos hK0 hz, fun a ha hK d hd hd0 hrange v Λ x y =>
      norm_resolventColumn_le_exp ha hK hd hd0 hrange v Λ hz x y⟩

end Main

end FroehlichSpencer.Infra
