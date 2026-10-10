/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.Infra.Ergodic.Variance
import Mathlib.Analysis.PSeries

/-!
# Pointwise ergodic theorem for bounded local and quasi-local functions

For `ν ≥ 1` and an i.i.d. product measure, the cube averages `A_L f` of a bounded measurable
function depending on finitely many coordinates converge almost surely to `∫ f` (along all `L`),
and so do those of any uniform limit of such functions.

The proof combines the Chebyshev bound
of `Ergodic/Variance.lean` with Borel–Cantelli along `L = k²`, an interpolation argument for
nonnegative functions, and an `ε/3` argument for the uniform limits.

This is the input for the
integrated density of states of Fröhlich–Spencer (1983), (1.10), Fröhlich–Spencer (1983).
-/

@[expose] public section

open MeasureTheory Filter Topology

namespace FroehlichSpencer.Infra

variable {ν : ℕ}

private theorem summable_one_div_sq_add_one :
    Summable fun k : ℕ => 1 / ((k : ℝ) ^ 2 + 1) := by
  have h : Summable fun k : ℕ => 1 / ((k : ℝ) ^ 2) := by
    simp
  rw [← summable_nat_add_iff 1] at h ⊢
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) h
  have : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) ^ 2 := by positivity
  exact one_div_le_one_div_of_le this (by linarith)

private theorem ae_tendsto_cubeAverage_sq (hν : 0 < ν) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {f : ((Fin ν → ℤ) → ℝ) → ℝ} (hf : Measurable f) {M : ℝ} (hM : ∀ v, |f v| ≤ M)
    {S : Finset (Fin ν → ℤ)} (hS : ∀ v w : (Fin ν → ℤ) → ℝ, (∀ x ∈ S, v x = w x) → f v = f w) :
    ∀ᵐ v ∂productMeasure μ,
      Tendsto (fun k : ℕ => cubeAverage f (k ^ 2) v) atTop (𝓝 (∫ w, f w ∂productMeasure μ)) := by
  have key : ∀ n : ℕ, ∀ᵐ v ∂productMeasure μ, ∀ᶠ k : ℕ in atTop,
      |cubeAverage f (k ^ 2) v - ∫ w, f w ∂productMeasure μ| < 1 / ((n : ℝ) + 1) := by
    intro n
    have hε : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    set ε : ℝ := 1 / ((n : ℝ) + 1)
    set K : ℝ := 4 * M ^ 2 * S.card ^ 2 / ε ^ 2
    have hK : 0 ≤ K := by positivity
    have hb : ∀ k : ℕ, productMeasure μ
        {v | ε ≤ |cubeAverage f (k ^ 2) v - ∫ w, f w ∂productMeasure μ|} ≤
        ENNReal.ofReal (K * (1 / ((k : ℝ) ^ 2 + 1))) := by
      intro k
      refine (measure_le_abs_cubeAverage_sub_le μ hf hM hS (k ^ 2) hε).trans ?_
      refine ENNReal.ofReal_le_ofReal ?_
      have hc : ((k : ℝ) ^ 2 + 1) ≤ ((cube ν (k ^ 2)).card : ℝ) := by
        rw [card_cube]
        have h1 : 2 * k ^ 2 + 1 ≤ (2 * k ^ 2 + 1) ^ ν := Nat.le_self_pow hν.ne' _
        have h2 : ((2 * k ^ 2 + 1 : ℕ) : ℝ) ≤ (((2 * k ^ 2 + 1) ^ ν : ℕ) : ℝ) := by
          exact_mod_cast h1
        push_cast at h2 ⊢
        nlinarith [sq_nonneg (k : ℝ)]
      have hpos : (0 : ℝ) < (k : ℝ) ^ 2 + 1 := by positivity
      calc 4 * M ^ 2 * (S.card : ℝ) ^ 2 / (((cube ν (k ^ 2)).card : ℝ) * ε ^ 2)
          = K * (1 / ((cube ν (k ^ 2)).card : ℝ)) := by
            simp only [K]; field_simp
        _ ≤ K * (1 / ((k : ℝ) ^ 2 + 1)) :=
            mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le hpos hc) hK
    have hsum : ∑' k : ℕ, productMeasure μ
        {v | ε ≤ |cubeAverage f (k ^ 2) v - ∫ w, f w ∂productMeasure μ|} ≠ ⊤ := by
      refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hb)
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity)
        (summable_one_div_sq_add_one.mul_left K)]
      exact ENNReal.ofReal_ne_top
    filter_upwards [ae_eventually_notMem hsum] with v hv
    filter_upwards [hv] with k hk
    simpa only [Set.mem_ofPred_eq, not_le] using hk
  filter_upwards [ae_all_iff.2 key] with v hv
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hv n)
  exact ⟨N, fun k hk => by rw [Real.dist_eq]; exact (hN k hk).trans hn⟩

private theorem tendsto_card_ratio (ν : ℕ) :
    Tendsto (fun k : ℕ =>
      ((cube ν ((k + 1) ^ 2)).card : ℝ) / ((cube ν (k ^ 2)).card : ℝ)) atTop (𝓝 1) := by
  have hx : Tendsto (fun k : ℕ => ((2 * ((k : ℝ) + 1) ^ 2 + 1) / (2 * (k : ℝ) ^ 2 + 1))) atTop
      (𝓝 1) := by
    have hu : Tendsto (fun k : ℕ => 1 + 4 * (1 / ((k : ℝ) + 1))) atTop (𝓝 1) := by
      have h0 := ((tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (4 : ℝ)).const_add (1 : ℝ)
      rwa [mul_zero, add_zero] at h0
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu
      (fun k => ?_) (fun k => ?_)
    · have : (0 : ℝ) < 2 * (k : ℝ) ^ 2 + 1 := by positivity
      rw [le_div_iff₀ this]; nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    · have hk : (0 : ℝ) ≤ k := k.cast_nonneg
      have : (0 : ℝ) < 2 * (k : ℝ) ^ 2 + 1 := by positivity
      have h1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      show _ ≤ 1 + 4 * (1 / ((k : ℝ) + 1))
      rw [div_le_iff₀ this]
      have : (1 + 4 * (1 / ((k : ℝ) + 1))) * (2 * (k : ℝ) ^ 2 + 1) =
          ((k : ℝ) + 1 + 4) * (2 * (k : ℝ) ^ 2 + 1) / ((k : ℝ) + 1) := by
        field_simp
      rw [this, le_div_iff₀ h1]
      -- integrality: (2k-1)(2k-2) ≥ 0
      have hk' : (k : ℝ) = 0 ∨ 1 ≤ (k : ℝ) := by
        rcases Nat.eq_zero_or_pos k with h | h
        · left; simp [h]
        · right; exact_mod_cast h
      rcases hk' with h | h
      · rw [h]; norm_num
      · nlinarith [mul_nonneg hk (sub_nonneg.2 h), sq_nonneg (k : ℝ)]
  have := hx.pow ν
  rw [one_pow] at this
  refine this.congr (fun k => ?_)
  rw [card_cube, card_cube]
  push_cast
  rw [div_pow]

private theorem tendsto_cubeAverage_of_sq {h : ((Fin ν → ℤ) → ℝ) → ℝ} (hnn : ∀ v, 0 ≤ h v)
    {v : (Fin ν → ℤ) → ℝ} {m : ℝ}
    (ht : Tendsto (fun k : ℕ => cubeAverage h (k ^ 2) v) atTop (𝓝 m)) :
    Tendsto (fun L : ℕ => cubeAverage h L v) atTop (𝓝 m) := by
  have hs : Tendsto Nat.sqrt atTop atTop := by
    refine tendsto_atTop_atTop.2 fun b => ⟨b ^ 2, ?_⟩
    intro a ha
    calc b = Nat.sqrt (b ^ 2) := (Nat.sqrt_eq' b).symm
      _ ≤ Nat.sqrt a := Nat.sqrt_le_sqrt ha
  have hr := (tendsto_card_ratio ν).comp hs
  have hlow : Tendsto (fun L : ℕ => ((((cube ν ((Nat.sqrt L + 1) ^ 2)).card : ℝ) /
      ((cube ν (Nat.sqrt L ^ 2)).card : ℝ))⁻¹ * cubeAverage h (Nat.sqrt L ^ 2) v)) atTop
      (𝓝 (1⁻¹ * m)) := (hr.inv₀ one_ne_zero).mul (ht.comp hs)
  have hup : Tendsto (fun L : ℕ => (((cube ν ((Nat.sqrt L + 1) ^ 2)).card : ℝ) /
      ((cube ν (Nat.sqrt L ^ 2)).card : ℝ)) * cubeAverage h ((Nat.sqrt L + 1) ^ 2) v) atTop
      (𝓝 (1 * m)) := by
    refine hr.mul ?_
    have h2 : Tendsto (fun k : ℕ => cubeAverage h ((k + 1) ^ 2) v) atTop (𝓝 m) :=
      (tendsto_add_atTop_iff_nat (f := fun k : ℕ => cubeAverage h (k ^ 2) v) 1).2 ht
    exact h2.comp hs
  rw [inv_one, one_mul] at hlow
  rw [one_mul] at hup
  have hbd : ∀ L : ℕ, (((cube ν ((Nat.sqrt L + 1) ^ 2)).card : ℝ) /
      ((cube ν (Nat.sqrt L ^ 2)).card : ℝ))⁻¹ * cubeAverage h (Nat.sqrt L ^ 2) v ≤
        cubeAverage h L v ∧ cubeAverage h L v ≤
      (((cube ν ((Nat.sqrt L + 1) ^ 2)).card : ℝ) / ((cube ν (Nat.sqrt L ^ 2)).card : ℝ)) *
        cubeAverage h ((Nat.sqrt L + 1) ^ 2) v := by
    intro L
    set k := Nat.sqrt L with hk
    have hkL : k ^ 2 ≤ L := Nat.sqrt_le' L
    have hLk : L ≤ (k + 1) ^ 2 := (Nat.lt_succ_sqrt' L).le
    have hnk : (0 : ℝ) < (cube ν (k ^ 2)).card := by exact_mod_cast card_cube_pos ν _
    have hnL : (0 : ℝ) < (cube ν L).card := by exact_mod_cast card_cube_pos ν _
    have hnc : (0 : ℝ) < (cube ν ((k + 1) ^ 2)).card := by exact_mod_cast card_cube_pos ν _
    have hknL : ((cube ν (k ^ 2)).card : ℝ) ≤ (cube ν L).card := by
      exact_mod_cast Finset.card_le_card (cube_mono hkL)
    have hLnc : ((cube ν L).card : ℝ) ≤ (cube ν ((k + 1) ^ 2)).card := by
      exact_mod_cast Finset.card_le_card (cube_mono hLk)
    have hs1 : ∑ a ∈ cube ν (k ^ 2), h (latticeShift a v) ≤
        ∑ a ∈ cube ν L, h (latticeShift a v) :=
      Finset.sum_le_sum_of_subset_of_nonneg (cube_mono hkL) (fun _ _ _ => hnn _)
    have hs2 : ∑ a ∈ cube ν L, h (latticeShift a v) ≤
        ∑ a ∈ cube ν ((k + 1) ^ 2), h (latticeShift a v) :=
      Finset.sum_le_sum_of_subset_of_nonneg (cube_mono hLk) (fun _ _ _ => hnn _)
    have hs0 : 0 ≤ ∑ a ∈ cube ν (k ^ 2), h (latticeShift a v) :=
      Finset.sum_nonneg fun _ _ => hnn _
    have hs0' : 0 ≤ ∑ a ∈ cube ν L, h (latticeShift a v) := hs0.trans hs1
    simp only [cubeAverage]
    constructor
    · calc _ = (∑ a ∈ cube ν (k ^ 2), h (latticeShift a v)) /
            ((cube ν ((k + 1) ^ 2)).card : ℝ) := by
            rw [inv_div]; field_simp
        _ ≤ (∑ a ∈ cube ν (k ^ 2), h (latticeShift a v)) / ((cube ν L).card : ℝ) :=
            div_le_div_of_nonneg_left hs0 hnL hLnc
        _ ≤ (∑ a ∈ cube ν L, h (latticeShift a v)) / ((cube ν L).card : ℝ) :=
            div_le_div_of_nonneg_right hs1 hnL.le
        _ = _ := by rw [div_eq_inv_mul]
    · calc ((cube ν L).card : ℝ)⁻¹ * ∑ a ∈ cube ν L, h (latticeShift a v)
          = (∑ a ∈ cube ν L, h (latticeShift a v)) / ((cube ν L).card : ℝ) := by
            rw [div_eq_inv_mul]
        _ ≤ (∑ a ∈ cube ν L, h (latticeShift a v)) / ((cube ν (k ^ 2)).card : ℝ) :=
            div_le_div_of_nonneg_left hs0' hnk hknL
        _ ≤ (∑ a ∈ cube ν ((k + 1) ^ 2), h (latticeShift a v)) /
            ((cube ν (k ^ 2)).card : ℝ) := div_le_div_of_nonneg_right hs2 hnk.le
        _ = _ := by field_simp
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlow hup (fun L => (hbd L).1)
    (fun L => (hbd L).2)

private theorem cubeAverage_add_const (f : ((Fin ν → ℤ) → ℝ) → ℝ) (c : ℝ) (L : ℕ)
    (v : (Fin ν → ℤ) → ℝ) :
    cubeAverage (fun w => f w + c) L v = cubeAverage f L v + c := by
  have h := card_cube_pos ν L
  simp only [cubeAverage, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
  field_simp

private theorem abs_cubeAverage_sub_le {f g : ((Fin ν → ℤ) → ℝ) → ℝ} {ε : ℝ}
    (hfg : ∀ v, |f v - g v| ≤ ε) (L : ℕ) (v : (Fin ν → ℤ) → ℝ) :
    |cubeAverage f L v - cubeAverage g L v| ≤ ε := by
  have h : (0 : ℝ) < (cube ν L).card := by exact_mod_cast card_cube_pos ν L
  have h1 : cubeAverage f L v - cubeAverage g L v =
      ((cube ν L).card : ℝ)⁻¹ *
        ∑ a ∈ cube ν L, (f (latticeShift a v) - g (latticeShift a v)) := by
    simp only [cubeAverage, Finset.sum_sub_distrib]; ring
  rw [h1, abs_mul, abs_of_pos (inv_pos.2 h)]
  have h2 : |∑ a ∈ cube ν L, (f (latticeShift a v) - g (latticeShift a v))| ≤
      (cube ν L).card * ε :=
    (Finset.abs_sum_le_sum_abs _ _).trans <| (Finset.sum_le_sum fun a _ => hfg _).trans
      (by simp)
  calc _ ≤ ((cube ν L).card : ℝ)⁻¹ * ((cube ν L).card * ε) :=
        mul_le_mul_of_nonneg_left h2 (inv_pos.2 h).le
    _ = ε := by field_simp

theorem ae_tendsto_cubeAverage_of_local (hν : 0 < ν) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {f : ((Fin ν → ℤ) → ℝ) → ℝ} (hf : Measurable f) {M : ℝ} (hM : ∀ v, |f v| ≤ M)
    {S : Finset (Fin ν → ℤ)} (hS : ∀ v w : (Fin ν → ℤ) → ℝ, (∀ x ∈ S, v x = w x) → f v = f w) :
    ∀ᵐ v ∂productMeasure μ,
      Tendsto (fun L => cubeAverage f L v) atTop (𝓝 (∫ w, f w ∂productMeasure μ)) := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hnn : ∀ v, 0 ≤ f v + M := fun v => by linarith [(abs_le.1 (hM v)).1]
  have hb : ∀ v, |f v + M| ≤ 2 * M := fun v => by
    rw [abs_le]; constructor <;> linarith [abs_le.1 (hM v)]
  have hS' : ∀ v w : (Fin ν → ℤ) → ℝ, (∀ x ∈ S, v x = w x) → f v + M = f w + M :=
    fun v w h => by rw [hS v w h]
  filter_upwards [ae_tendsto_cubeAverage_sq hν μ (hf.add_const M) hb hS'] with v hv
  have h1 := tendsto_cubeAverage_of_sq (fun w => hnn w) hv
  have hint : ∫ w, (f w + M) ∂productMeasure μ = ∫ w, f w ∂productMeasure μ + M := by
    have hfi : Integrable f (productMeasure μ) :=
      Integrable.of_bound hf.aestronglyMeasurable M (ae_of_all _ fun v => by
        simpa only [Real.norm_eq_abs] using hM v)
    rw [integral_add hfi (integrable_const M)]; simp
  simp only [cubeAverage_add_const, hint] at h1
  simpa using h1.sub_const M

theorem ae_tendsto_cubeAverage_of_forall_approx_local (hν : 0 < ν) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] {f : ((Fin ν → ℤ) → ℝ) → ℝ}
    (happrox : ∀ ε > 0, ∃ (g : ((Fin ν → ℤ) → ℝ) → ℝ) (M : ℝ) (S : Finset (Fin ν → ℤ)),
      Measurable g ∧ (∀ v, |g v| ≤ M) ∧
      (∀ v w : (Fin ν → ℤ) → ℝ, (∀ x ∈ S, v x = w x) → g v = g w) ∧ ∀ v, |f v - g v| ≤ ε) :
    ∀ᵐ v ∂productMeasure μ,
      Tendsto (fun L => cubeAverage f L v) atTop (𝓝 (∫ w, f w ∂productMeasure μ)) := by
  have hpos : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => by positivity
  choose g M S hgm hgM hgS hgf using fun n : ℕ => happrox _ (hpos n)
  have hfm : Measurable f := by
    refine measurable_of_tendsto_metrizable (f := g) (fun n => hgm n) ?_
    rw [tendsto_pi_nhds]
    intro v
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_)
      tendsto_one_div_add_atTop_nhds_zero_nat
    rw [Real.dist_eq, abs_sub_comm]; exact hgf n v
  have hfb : ∀ v, |f v| ≤ M 0 + 1 := fun v => by
    have := hgf 0 v
    have h2 := hgM 0 v
    have : |f v| ≤ |g 0 v| + |f v - g 0 v| := by
      calc |f v| = |g 0 v + (f v - g 0 v)| := by ring_nf
        _ ≤ _ := abs_add_le _ _
    simp at this ⊢
    linarith
  have hfi : Integrable f (productMeasure μ) :=
    Integrable.of_bound hfm.aestronglyMeasurable (M 0 + 1) (ae_of_all _ fun v => by
      simpa only [Real.norm_eq_abs] using hfb v)
  have hgi : ∀ n, Integrable (g n) (productMeasure μ) := fun n =>
    Integrable.of_bound (hgm n).aestronglyMeasurable (M n) (ae_of_all _ fun v => by
      simpa only [Real.norm_eq_abs] using hgM n v)
  have hint : ∀ n, |∫ w, f w ∂productMeasure μ - ∫ w, g n w ∂productMeasure μ| ≤
      1 / ((n : ℝ) + 1) := fun n => by
    rw [← integral_sub hfi (hgi n)]
    have := norm_integral_le_of_norm_le_const (μ := productMeasure μ)
      (f := fun w => f w - g n w) (C := 1 / ((n : ℝ) + 1))
      (ae_of_all _ fun v => by simpa only [Real.norm_eq_abs] using hgf n v)
    simpa using this
  have hall : ∀ᵐ v ∂productMeasure μ, ∀ n : ℕ,
      Tendsto (fun L => cubeAverage (g n) L v) atTop (𝓝 (∫ w, g n w ∂productMeasure μ)) :=
    ae_all_iff.2 fun n => ae_tendsto_cubeAverage_of_local hν μ (hgm n) (hgM n) (hgS n)
  filter_upwards [hall] with v hv
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show 0 < ε / 3 by positivity)
  filter_upwards [Metric.tendsto_nhds.1 (hv n) (ε / 3) (by positivity)] with L hL
  rw [Real.dist_eq] at hL ⊢
  have h1 := abs_cubeAverage_sub_le (hgf n) L v
  have h2 := hint n
  have h3 : |cubeAverage f L v - ∫ w, f w ∂productMeasure μ| ≤
      |cubeAverage f L v - cubeAverage (g n) L v| +
      |cubeAverage (g n) L v - ∫ w, g n w ∂productMeasure μ| +
      |∫ w, f w ∂productMeasure μ - ∫ w, g n w ∂productMeasure μ| := by
    have e : cubeAverage f L v - ∫ w, f w ∂productMeasure μ =
        (cubeAverage f L v - cubeAverage (g n) L v) +
        (cubeAverage (g n) L v - ∫ w, g n w ∂productMeasure μ) -
        (∫ w, f w ∂productMeasure μ - ∫ w, g n w ∂productMeasure μ) := by ring
    rw [e]
    exact (abs_sub _ _).trans (by gcongr; exact abs_add_le _ _)
  linarith

end FroehlichSpencer.Infra
