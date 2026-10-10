/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.Infra.Ergodic.Basic
import Mathlib.Probability.Independence.Integration

/-!
# Second-moment bound for cube averages of bounded local functions

For a bounded measurable `f` depending only on the coordinates in a finite set `S`, the cube
averages satisfy `E (A_L f - E f)² ≤ 4 M² |S|² / |Q_L|`, together with the Chebyshev bound.

The
proof expands the square and uses that shifts of `f` by `a` and `b` are independent as soon as the
translated supports `S + a`, `S + b` are disjoint.

This is the quantitative input of the pointwise
ergodic theorem for local functions behind the integrated density of states of
Fröhlich–Spencer (1983), (1.10), Fröhlich–Spencer (1983).
-/

@[expose] public section

open MeasureTheory

namespace FroehlichSpencer.Infra

variable {ν : ℕ}

/-- A measurable function that is invariant under changes away from `T` is measurable for
the σ-algebra `localSigma T`. -/
private theorem measurable_localSigma_of_local {g : ((Fin ν → ℤ) → ℝ) → ℝ} (hg : Measurable g)
    {T : Finset (Fin ν → ℤ)}
    (hT : ∀ v w : (Fin ν → ℤ) → ℝ, (∀ x ∈ T, v x = w x) → g v = g w) :
    Measurable[localSigma (↑T : Set (Fin ν → ℤ))] g := by
  intro B hB
  exact dependsOn_of_measurable_of_invariant (hg hB) fun v w h => by
    simp only [Set.mem_preimage, hT v w fun x hx => h x (Finset.mem_coe.2 hx)]

/-- Orthogonality of mean-zero local functions with disjoint supports. -/
private theorem integral_mul_eq_zero_of_disjoint (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {g₁ g₂ : ((Fin ν → ℤ) → ℝ) → ℝ} (h₁ : Measurable g₁) (h₂ : Measurable g₂)
    {T₁ T₂ : Finset (Fin ν → ℤ)}
    (hT₁ : ∀ v w : (Fin ν → ℤ) → ℝ, (∀ x ∈ T₁, v x = w x) → g₁ v = g₁ w)
    (hT₂ : ∀ v w : (Fin ν → ℤ) → ℝ, (∀ x ∈ T₂, v x = w x) → g₂ v = g₂ w)
    (hd : Disjoint T₁ T₂) (h0 : ∫ v, g₁ v ∂productMeasure μ = 0) :
    ∫ v, g₁ v * g₂ v ∂productMeasure μ = 0 := by
  have hind : ProbabilityTheory.IndepFun g₁ g₂ (productMeasure μ) := by
    have := localSigma_indep (ι := Fin ν → ℤ) μ (Finset.disjoint_coe.2 hd)
    exact (ProbabilityTheory.indep_of_indep_of_le_right
      (ProbabilityTheory.indep_of_indep_of_le_left this
        (measurable_localSigma_of_local h₁ hT₁).comap_le)
      (measurable_localSigma_of_local h₂ hT₂).comap_le)
  have := ProbabilityTheory.IndepFun.integral_mul_eq_mul_integral hind h₁.aestronglyMeasurable
    h₂.aestronglyMeasurable
  simp only [Pi.mul_apply] at this
  rw [this, h0, zero_mul]

/-- **Second-moment bound.** The cube average of a bounded local function concentrates around its
mean with variance at most `4 M² |S|² / |Q_L|`. -/
theorem integral_sq_cubeAverage_sub_le (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {f : ((Fin ν → ℤ) → ℝ) → ℝ} (hf : Measurable f) {M : ℝ} (hM : ∀ v, |f v| ≤ M)
    {S : Finset (Fin ν → ℤ)} (hS : ∀ v w : (Fin ν → ℤ) → ℝ, (∀ x ∈ S, v x = w x) → f v = f w)
    (L : ℕ) :
    ∫ v, (cubeAverage f L v - ∫ w, f w ∂productMeasure μ) ^ 2 ∂productMeasure μ ≤
      4 * M ^ 2 * S.card ^ 2 / (cube ν L).card := by
  classical
  set P : Measure ((Fin ν → ℤ) → ℝ) := productMeasure μ with hP
  set m : ℝ := ∫ w, f w ∂P with hm
  set Q := cube ν L with hQ
  have hn : (0 : ℝ) < Q.card := by exact_mod_cast card_cube_pos ν L
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hfint : Integrable f P :=
    Integrable.of_bound hf.aestronglyMeasurable M (ae_of_all _ fun v => by
      simpa only [Real.norm_eq_abs] using hM v)
  have hmM : |m| ≤ M := by
    have := norm_integral_le_of_norm_le_const (μ := P) (f := f) (C := M)
      (ae_of_all _ fun v => by simpa only [Real.norm_eq_abs] using hM v)
    simpa using this
  set g : (Fin ν → ℤ) → ((Fin ν → ℤ) → ℝ) → ℝ := fun a v => f (latticeShift a v) - m with hg
  have hgm : ∀ a, Measurable (g a) := fun a =>
    (hf.comp (measurable_latticeShift a)).sub measurable_const
  have hgb : ∀ a v, |g a v| ≤ 2 * M := fun a v => by
    have h1 := hM (latticeShift a v)
    have h2 := abs_le.1 h1
    have h3 := abs_le.1 hmM
    exact abs_le.2 ⟨by simp only [hg]; linarith [h2.1, h3.2],
      by simp only [hg]; linarith [h2.2, h3.1]⟩
  have hgl : ∀ a, ∀ v w : (Fin ν → ℤ) → ℝ,
      (∀ x ∈ S.image (· + a), v x = w x) → g a v = g a w :=
    fun a v w h => by
      simp only [hg]
      rw [hS (latticeShift a v) (latticeShift a w)
        fun x hx => h _ (Finset.mem_image_of_mem _ hx)]
  have hg0 : ∀ a, ∫ v, g a v ∂P = 0 := fun a => by
    have hi : Integrable (fun v => f (latticeShift a v)) P :=
      (measurePreserving_latticeShift μ a).integrable_comp_of_integrable hfint
    simp only [hg]
    rw [integral_sub hi (integrable_const _), integral_comp_latticeShift, integral_const]
    simp only [probReal_univ, one_smul]
    exact sub_eq_zero.2 rfl
  have hgi : ∀ a b, Integrable (fun v => g a v * g b v) P := fun a b =>
    Integrable.of_bound ((hgm a).mul (hgm b)).aestronglyMeasurable ((2 * M) * (2 * M))
      (ae_of_all _ fun v => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (hgb a v) (hgb b v) (abs_nonneg _) (by linarith))
  -- pair bound
  set N : (Fin ν → ℤ) → Finset (Fin ν → ℤ) :=
    fun a => (S ×ˢ S).image (fun p => a + p.1 - p.2) with hN
  have hpair : ∀ a b, ∫ v, g a v * g b v ∂P ≤ if b ∈ N a then 4 * M ^ 2 else 0 := by
    intro a b
    split_ifs with hb
    · have h := norm_integral_le_of_norm_le_const (μ := P) (f := fun v => g a v * g b v)
        (C := 4 * M ^ 2) (ae_of_all _ fun v => by
          rw [Real.norm_eq_abs, abs_mul]
          calc |g a v| * |g b v| ≤ (2 * M) * (2 * M) :=
                mul_le_mul (hgb a v) (hgb b v) (abs_nonneg _) (by linarith)
            _ = 4 * M ^ 2 := by ring)
      simp only [probReal_univ, mul_one, Real.norm_eq_abs] at h
      exact (le_abs_self _).trans h
    · have hd : Disjoint (S.image (· + a)) (S.image (· + b)) := by
        rw [Finset.disjoint_left]
        intro z hz hz'
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hz
        obtain ⟨y, hy, hxy⟩ := Finset.mem_image.1 hz'
        apply hb
        refine Finset.mem_image.2 ⟨(x, y), Finset.mem_product.2 ⟨hx, hy⟩, ?_⟩
        have : x + a = y + b := hxy.symm
        simp only
        rw [add_comm a x, this]; abel
      exact (integral_mul_eq_zero_of_disjoint μ (hgm a) (hgm b) (hgl a) (hgl b) hd (hg0 a)).le
  have hsum : ∫ v, (∑ a ∈ Q, g a v) ^ 2 ∂P ≤ Q.card * (S.card ^ 2 * (4 * M ^ 2)) := by
    have e : ∀ v, (∑ a ∈ Q, g a v) ^ 2 = ∑ a ∈ Q, ∑ b ∈ Q, g a v * g b v := fun v => by
      rw [sq, Finset.sum_mul_sum]
    simp only [e]
    rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => hgi a b]
    calc ∑ a ∈ Q, ∫ v, ∑ b ∈ Q, g a v * g b v ∂P
        = ∑ a ∈ Q, ∑ b ∈ Q, ∫ v, g a v * g b v ∂P := by
          refine Finset.sum_congr rfl fun a _ => ?_
          exact integral_finsetSum _ fun b _ => hgi a b
      _ ≤ ∑ a ∈ Q, ∑ b ∈ Q, (if b ∈ N a then 4 * M ^ 2 else 0) :=
          Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => hpair a b
      _ ≤ ∑ _a ∈ Q, (S.card ^ 2 * (4 * M ^ 2)) := by
          refine Finset.sum_le_sum fun a _ => ?_
          rw [Finset.sum_ite_mem, Finset.sum_const, nsmul_eq_mul]
          have h1 : (Q ∩ N a).card ≤ S.card ^ 2 :=
            (Finset.card_le_card Finset.inter_subset_right).trans
              ((Finset.card_image_le).trans (by rw [Finset.card_product, sq]))
          have h2 : ((Q ∩ N a).card : ℝ) ≤ S.card ^ 2 := by exact_mod_cast h1
          exact mul_le_mul_of_nonneg_right h2 (by positivity)
      _ = Q.card * (S.card ^ 2 * (4 * M ^ 2)) := by rw [Finset.sum_const, nsmul_eq_mul]
  have hrew : ∀ v, cubeAverage f L v - m = (Q.card : ℝ)⁻¹ * ∑ a ∈ Q, g a v := fun v => by
    change ((Q.card : ℝ)⁻¹ * ∑ a ∈ Q, f (latticeShift a v)) - m = _
    simp only [hg, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    field_simp
  simp only [hrew, mul_pow]
  rw [integral_const_mul]
  calc ((Q.card : ℝ)⁻¹) ^ 2 * ∫ v, (∑ a ∈ Q, g a v) ^ 2 ∂P
      ≤ ((Q.card : ℝ)⁻¹) ^ 2 * (Q.card * (S.card ^ 2 * (4 * M ^ 2))) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 4 * M ^ 2 * S.card ^ 2 / Q.card := by field_simp

/-- **Chebyshev bound** for the cube averages of a bounded local function. -/
theorem measure_le_abs_cubeAverage_sub_le (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {f : ((Fin ν → ℤ) → ℝ) → ℝ} (hf : Measurable f) {M : ℝ} (hM : ∀ v, |f v| ≤ M)
    {S : Finset (Fin ν → ℤ)} (hS : ∀ v w : (Fin ν → ℤ) → ℝ, (∀ x ∈ S, v x = w x) → f v = f w)
    (L : ℕ) {ε : ℝ} (hε : 0 < ε) :
    productMeasure μ {v | ε ≤ |cubeAverage f L v - ∫ w, f w ∂productMeasure μ|} ≤
      ENNReal.ofReal (4 * M ^ 2 * S.card ^ 2 / ((cube ν L).card * ε ^ 2)) := by
  set P : Measure ((Fin ν → ℤ) → ℝ) := productMeasure μ with hP
  set m : ℝ := ∫ w, f w ∂P with hm
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hfint : Integrable f P :=
    Integrable.of_bound hf.aestronglyMeasurable M (ae_of_all _ fun v => by
      simpa only [Real.norm_eq_abs] using hM v)
  have hmM : |m| ≤ M := by
    have := norm_integral_le_of_norm_le_const (μ := P) (f := f) (C := M)
      (ae_of_all _ fun v => by simpa only [Real.norm_eq_abs] using hM v)
    simpa using this
  have hAm : Measurable fun v => (cubeAverage f L v - m) ^ 2 :=
    ((measurable_cubeAverage hf L).sub measurable_const).pow_const 2
  have hAb : ∀ v, |cubeAverage f L v - m| ≤ 2 * M := fun v => by
    have hn : (0 : ℝ) < (cube ν L).card := by exact_mod_cast card_cube_pos ν L
    have h1 : |cubeAverage f L v| ≤ M := by
      simp only [cubeAverage]
      rw [abs_mul, abs_of_pos (inv_pos.2 hn), inv_mul_le_iff₀ hn]
      calc |∑ a ∈ cube ν L, f (latticeShift a v)|
          ≤ ∑ a ∈ cube ν L, |f (latticeShift a v)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _a ∈ cube ν L, M := Finset.sum_le_sum fun a _ => hM _
        _ = (cube ν L).card * M := by rw [Finset.sum_const, nsmul_eq_mul]
    calc |cubeAverage f L v - m| ≤ |cubeAverage f L v| + |m| := abs_sub _ _
      _ ≤ 2 * M := by linarith
  have hAi : Integrable (fun v => (cubeAverage f L v - m) ^ 2) P :=
    Integrable.of_bound hAm.aestronglyMeasurable ((2 * M) ^ 2) (ae_of_all _ fun v => by
      rw [Real.norm_eq_abs, abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (hAb v) 2)
  have hmk := mul_meas_ge_le_integral_of_nonneg (μ := P)
    (f := fun v => (cubeAverage f L v - m) ^ 2) (ae_of_all _ fun v => sq_nonneg _) hAi (ε ^ 2)
  have hset : {v | ε ≤ |cubeAverage f L v - m|} = {v | ε ^ 2 ≤ (cubeAverage f L v - m) ^ 2} := by
    ext v
    simp only [Set.mem_ofPred_eq]
    rw [← sq_abs (cubeAverage f L v - m)]
    exact (sq_le_sq₀ hε.le (abs_nonneg _)).symm
  have hv := integral_sq_cubeAverage_sub_le μ hf hM hS L
  have hcn : (0 : ℝ) < (cube ν L).card := by exact_mod_cast card_cube_pos ν L
  rw [hset, ← ofReal_measureReal]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [le_div_iff₀ (by positivity)]
  have h2 : ε ^ 2 * P.real {v | ε ^ 2 ≤ (cubeAverage f L v - m) ^ 2} ≤
      4 * M ^ 2 * S.card ^ 2 / (cube ν L).card := hmk.trans hv
  rw [le_div_iff₀ hcn] at h2
  linarith

end FroehlichSpencer.Infra
