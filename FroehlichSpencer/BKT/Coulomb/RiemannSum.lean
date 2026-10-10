/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Coulomb.PotentialKernel
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

/-!
# Torus Riemann sums of the potential kernel

The torus Green function at side `L` is the Riemann sum
`R_L(z) = L⁻² ∑_{m ∈ [0,L)²} (1 - cos ⟨2πm/L, z⟩)/ε(2πm/L)` of the potential-kernel integrand
(`Coulomb/TorusKernel.lean`). This module proves `R_L(z) → a(z)` (`tendsto_latticeRiemannSum`).

The proof writes `R_L(z)` as the integral over `[0,2π)²` of the integrand evaluated at the left
grid point (`integral_step_square`, by Fubini and the one-dimensional `integral_step_Ico`), and
applies dominated convergence: the integrand is bounded by `|z|²` everywhere
(`potentialKernelIntegrand_le`) and is continuous off `ε = 0`, which inside `[0,2π)²` is the
single null point `0`. No modulus of continuity or gradient bound is needed.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Coulomb

open MeasureTheory Set Filter Topology

/-- The left Riemann grid point of `t` at mesh `2π/L`: `2π ⌊L t / (2π)⌋ / L`. -/
def riemannGridInternal (L : ℕ) (t : ℝ) : ℝ :=
  2 * Real.pi * ⌊(L : ℝ) * t / (2 * Real.pi)⌋₊ / L

/-- The torus Riemann sum `L⁻² ∑_{m ∈ [0,L)²} (1 - cos ⟨2πm/L, z⟩)/ε(2πm/L)` of the potential
kernel (the `m = 0` term vanishes since the integrand is `0/0 = 0` there). -/
def latticeRiemannSumInternal (L : ℕ) (z : ℤ × ℤ) : ℝ :=
  ((L : ℝ) ^ 2)⁻¹ * ∑ m ∈ Finset.range L ×ˢ Finset.range L,
    potentialKernelIntegrandInternal z (2 * Real.pi * m.1 / L, 2 * Real.pi * m.2 / L)

theorem floor_mem_piece {L : ℕ} (hL : 0 < L) {m : ℕ} {t : ℝ}
    (ht : t ∈ Ico (2 * Real.pi * m / L) (2 * Real.pi * (m + 1) / L)) :
    ⌊(L : ℝ) * t / (2 * Real.pi)⌋₊ = m := by
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  have hpi := Real.pi_pos
  rcases ht with ⟨h1, h2⟩
  rw [Nat.floor_eq_iff]
  · constructor
    · rw [le_div_iff₀ (by positivity)]
      rw [div_le_iff₀ hL'] at h1
      linarith
    · rw [div_lt_iff₀ (by positivity)]
      rw [lt_div_iff₀ hL'] at h2
      linarith
  · have : 0 ≤ t := le_trans (by positivity) h1
    positivity

/-- One-dimensional step-function integral: `∫_{[0,2π)} F(⌊L t/2π⌋) dt = (2π/L) ∑_{m<L} F(m)`. -/
theorem integral_step_Ico (L : ℕ) (hL : 0 < L) (F : ℕ → ℝ) :
    ∫ t in Ico 0 (2 * Real.pi), F ⌊(L : ℝ) * t / (2 * Real.pi)⌋₊ =
      2 * Real.pi / L * ∑ m ∈ Finset.range L, F m := by
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  have hpi := Real.pi_pos
  set s : ℕ → Set ℝ := fun m => Ico (2 * Real.pi * m / L) (2 * Real.pi * (m + 1) / L) with hs
  have hunion : Ico 0 (2 * Real.pi) = ⋃ m ∈ Finset.range L, s m := by
    ext t
    simp only [mem_Ico, mem_iUnion, Finset.mem_range, hs, exists_prop]
    constructor
    · rintro ⟨h0, h1⟩
      refine ⟨⌊(L : ℝ) * t / (2 * Real.pi)⌋₊, ?_, ?_, ?_⟩
      · rw [Nat.floor_lt (by positivity), div_lt_iff₀ (by positivity)]
        nlinarith
      · rw [div_le_iff₀ hL']
        have := Nat.floor_le (show 0 ≤ (L : ℝ) * t / (2 * Real.pi) by positivity)
        rw [le_div_iff₀ (by positivity)] at this
        linarith
      · rw [lt_div_iff₀ hL']
        have := Nat.lt_floor_add_one ((L : ℝ) * t / (2 * Real.pi))
        rw [div_lt_iff₀ (by positivity)] at this
        linarith
    · rintro ⟨m, hm, h1, h2⟩
      have hm' : (m : ℝ) + 1 ≤ L := by exact_mod_cast hm
      constructor
      · exact le_trans (by positivity) h1
      · calc t < 2 * Real.pi * (m + 1) / L := h2
          _ ≤ 2 * Real.pi * L / L := by gcongr
          _ = 2 * Real.pi := by field_simp
  have hconst : ∀ m ∈ Finset.range L,
      ∫ t in s m, F ⌊(L : ℝ) * t / (2 * Real.pi)⌋₊ = 2 * Real.pi / L * F m := by
    intro m _
    rw [setIntegral_congr_fun measurableSet_Ico (fun t ht => by rw [floor_mem_piece hL ht]),
      setIntegral_const, smul_eq_mul, Measure.real, Real.volume_Ico,
      ENNReal.toReal_ofReal (by
        rw [sub_nonneg]; gcongr; linarith)]
    congr 1
    field_simp
    ring
  rw [hunion, integral_biUnion_finset _ (fun m _ => measurableSet_Ico) ?_ ?_]
  · rw [Finset.mul_sum]
    exact Finset.sum_congr rfl hconst
  · intro m _ m' _ hmm'
    simp only [Function.onFun]
    rcases lt_or_gt_of_ne hmm' with h | h
    · refine Set.Ico_disjoint_Ico.2 ?_
      have : (m : ℝ) + 1 ≤ m' := by exact_mod_cast h
      have h2 : 2 * Real.pi * (m + 1) / L ≤ 2 * Real.pi * m' / L := by gcongr
      exact (min_le_left _ _).trans (h2.trans (le_max_right _ _))
    · refine Set.Ico_disjoint_Ico.2 ?_
      have : (m' : ℝ) + 1 ≤ m := by exact_mod_cast h
      have h2 : 2 * Real.pi * (m' + 1) / L ≤ 2 * Real.pi * m / L := by gcongr
      exact (min_le_right _ _).trans (h2.trans (le_max_left _ _))
  · intro m _
    refine (integrableOn_const (C := F m) ?_).congr_fun (fun t ht => by
      rw [floor_mem_piece hL ht]) measurableSet_Ico
    rw [Real.volume_Ico]
    exact ENNReal.ofReal_ne_top

theorem floor_lt_of_mem_Ico {L : ℕ} (hL : 0 < L) {t : ℝ} (ht : t ∈ Ico 0 (2 * Real.pi)) :
    ⌊(L : ℝ) * t / (2 * Real.pi)⌋₊ < L := by
  have hpi := Real.pi_pos
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  rw [Nat.floor_lt (by have := ht.1; positivity), div_lt_iff₀ (by positivity)]
  nlinarith [ht.2]

theorem measurable_step (L : ℕ) (G : ℕ × ℕ → ℝ) :
    Measurable fun k : ℝ × ℝ =>
      G (⌊(L : ℝ) * k.1 / (2 * Real.pi)⌋₊, ⌊(L : ℝ) * k.2 / (2 * Real.pi)⌋₊) := by
  have h1 : Measurable fun k : ℝ × ℝ => ⌊(L : ℝ) * k.1 / (2 * Real.pi)⌋₊ :=
    Nat.measurable_floor.comp (by fun_prop)
  have h2 : Measurable fun k : ℝ × ℝ => ⌊(L : ℝ) * k.2 / (2 * Real.pi)⌋₊ :=
    Nat.measurable_floor.comp (by fun_prop)
  exact (measurable_of_countable G).comp (h1.prodMk h2)

/-- Two-dimensional step-function integral over `[0, 2π)²`. -/
theorem integral_step_square (L : ℕ) (hL : 0 < L) (G : ℕ × ℕ → ℝ) :
    ∫ k in frequencySquareInternal,
        G (⌊(L : ℝ) * k.1 / (2 * Real.pi)⌋₊, ⌊(L : ℝ) * k.2 / (2 * Real.pi)⌋₊) =
      (2 * Real.pi / L) ^ 2 * ∑ m ∈ Finset.range L ×ˢ Finset.range L, G m := by
  set B := ∑ m ∈ Finset.range L ×ˢ Finset.range L, |G m|
  have hB : ∀ a b : ℕ, a < L → b < L → |G (a, b)| ≤ B := fun a b ha hb =>
    Finset.single_le_sum (f := fun m => |G m|) (fun _ _ => abs_nonneg _)
      (Finset.mem_product.2 ⟨Finset.mem_range.2 ha, Finset.mem_range.2 hb⟩)
  have hint : IntegrableOn (fun k : ℝ × ℝ =>
      G (⌊(L : ℝ) * k.1 / (2 * Real.pi)⌋₊, ⌊(L : ℝ) * k.2 / (2 * Real.pi)⌋₊))
      frequencySquareInternal := by
    refine Integrable.of_bound (measurable_step L G).aestronglyMeasurable B ?_
    refine (ae_restrict_iff' measurableSet_frequencySquare).2 (ae_of_all _ fun k hk => ?_)
    rw [Real.norm_eq_abs]
    exact hB _ _ (floor_lt_of_mem_Ico hL hk.1) (floor_lt_of_mem_Ico hL hk.2)
  have h1D : ∀ a : ℕ, IntegrableOn (fun t : ℝ => G (⌊(L : ℝ) * t / (2 * Real.pi)⌋₊, a))
      (Ico 0 (2 * Real.pi)) := by
    intro a
    by_cases ha : a < L
    · refine Integrable.of_bound ((measurable_of_countable G).comp
        ((Nat.measurable_floor.comp (by fun_prop)).prodMk measurable_const)).aestronglyMeasurable
        B ?_
      refine (ae_restrict_iff' measurableSet_Ico).2 (ae_of_all _ fun t ht => ?_)
      rw [Real.norm_eq_abs]
      exact hB _ _ (floor_lt_of_mem_Ico hL ht) ha
    · refine Integrable.of_bound ((measurable_of_countable G).comp
        ((Nat.measurable_floor.comp (by fun_prop)).prodMk measurable_const)).aestronglyMeasurable
        (∑ m ∈ Finset.range L, |G (m, a)|) ?_
      refine (ae_restrict_iff' measurableSet_Ico).2 (ae_of_all _ fun t ht => ?_)
      rw [Real.norm_eq_abs]
      exact Finset.single_le_sum (f := fun m => |G (m, a)|) (fun _ _ => abs_nonneg _)
        (Finset.mem_range.2 (floor_lt_of_mem_Ico hL ht))
  rw [frequencySquareInternal, Measure.volume_eq_prod] at hint ⊢
  rw [setIntegral_prod _ hint]
  have hinner : ∀ x : ℝ, ∫ y in Ico 0 (2 * Real.pi),
      G (⌊(L : ℝ) * (x, y).1 / (2 * Real.pi)⌋₊, ⌊(L : ℝ) * (x, y).2 / (2 * Real.pi)⌋₊) =
      2 * Real.pi / L * ∑ b ∈ Finset.range L, G (⌊(L : ℝ) * x / (2 * Real.pi)⌋₊, b) := by
    intro x
    exact integral_step_Ico L hL (fun b => G (⌊(L : ℝ) * x / (2 * Real.pi)⌋₊, b))
  simp_rw [hinner]
  rw [integral_const_mul, integral_finsetSum _ (fun b _ => h1D b)]
  have houter : ∀ b ∈ Finset.range L, ∫ x in Ico 0 (2 * Real.pi),
      G (⌊(L : ℝ) * x / (2 * Real.pi)⌋₊, b) =
      2 * Real.pi / L * ∑ a ∈ Finset.range L, G (a, b) := fun b _ =>
    integral_step_Ico L hL (fun a => G (a, b))
  rw [Finset.sum_congr rfl houter, ← Finset.mul_sum, ← mul_assoc, ← sq, Finset.sum_product,
    Finset.sum_comm]

theorem measurable_riemannGrid (L : ℕ) : Measurable (riemannGridInternal L) := by
  unfold riemannGridInternal
  have h1 : Measurable fun t : ℝ => ⌊(L : ℝ) * t / (2 * Real.pi)⌋₊ :=
    Nat.measurable_floor.comp (by fun_prop)
  have h2 : Measurable fun t : ℝ => ((⌊(L : ℝ) * t / (2 * Real.pi)⌋₊ : ℕ) : ℝ) :=
    (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp h1
  exact (measurable_const.mul h2).div_const _

/-- `riemannGridInternal L t → t` as `L → ∞`, for `t ≥ 0`. -/
theorem tendsto_riemannGrid {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun L : ℕ => riemannGridInternal L t) atTop (𝓝 t) := by
  have hpi := Real.pi_pos
  have hlow : Tendsto (fun L : ℕ => t - 2 * Real.pi / L) atTop (𝓝 t) := by
    have : Tendsto (fun L : ℕ => 2 * Real.pi / (L : ℝ)) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat _
    simpa using tendsto_const_nhds.sub this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with L hL
    have hL' : (0 : ℝ) < L := by exact_mod_cast hL
    unfold riemannGridInternal
    have := Nat.lt_floor_add_one ((L : ℝ) * t / (2 * Real.pi))
    rw [div_lt_iff₀ (by positivity)] at this
    rw [sub_le_iff_le_add]
    have h2 : t ≤ (2 * Real.pi * ⌊(L : ℝ) * t / (2 * Real.pi)⌋₊ + 2 * Real.pi) / L := by
      rw [le_div_iff₀ hL']
      nlinarith
    calc t ≤ _ := h2
      _ = _ := by ring
  · filter_upwards [eventually_gt_atTop 0] with L hL
    have hL' : (0 : ℝ) < L := by exact_mod_cast hL
    unfold riemannGridInternal
    have := Nat.floor_le (show 0 ≤ (L : ℝ) * t / (2 * Real.pi) by positivity)
    rw [le_div_iff₀ (by positivity)] at this
    rw [div_le_iff₀ hL']
    nlinarith

theorem continuousAt_potentialKernelIntegrand (z : ℤ × ℤ) {k : ℝ × ℝ}
    (hk : latticeSymbolInternal k ≠ 0) : ContinuousAt (potentialKernelIntegrandInternal z) k := by
  unfold potentialKernelIntegrandInternal
  refine ContinuousAt.div (by fun_prop) ?_ hk
  unfold latticeSymbolInternal
  fun_prop

/-- **Riemann-sum convergence** to the potential kernel. -/
theorem tendsto_latticeRiemannSum (z : ℤ × ℤ) :
    Tendsto (fun L : ℕ => latticeRiemannSumInternal L z) atTop
      (𝓝 (potentialKernelInternal z)) := by
  have hpi := Real.pi_pos
  set F : ℕ → ℝ × ℝ → ℝ := fun L k =>
    potentialKernelIntegrandInternal z (riemannGridInternal L k.1, riemannGridInternal L k.2)
  have hstep : ∀ L : ℕ, 0 < L → latticeRiemannSumInternal L z =
      ((2 * Real.pi) ^ 2)⁻¹ * ∫ k in frequencySquareInternal, F L k := by
    intro L hL
    have hL' : (0 : ℝ) < L := by exact_mod_cast hL
    have h := integral_step_square L hL (fun m : ℕ × ℕ =>
      potentialKernelIntegrandInternal z (2 * Real.pi * m.1 / L, 2 * Real.pi * m.2 / L))
    simp only [F, riemannGridInternal]
    rw [h, latticeRiemannSumInternal, ← mul_assoc]
    congr 1
    field_simp
  have hDCT : Tendsto (fun L : ℕ => ∫ k in frequencySquareInternal, F L k) atTop
      (𝓝 (∫ k in frequencySquareInternal, potentialKernelIntegrandInternal z k)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => (z.1 : ℝ) ^ 2 + (z.2 : ℝ) ^ 2)
      (fun L => ?_) (integrable_const _) (fun L => ae_of_all _ fun k => ?_) ?_
    · exact ((measurable_potentialKernelIntegrand z).comp
        (((measurable_riemannGrid L).comp measurable_fst).prodMk
          ((measurable_riemannGrid L).comp measurable_snd))).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (potentialKernelIntegrand_nonneg _ _)]
      exact potentialKernelIntegrand_le _ _
    · filter_upwards [ae_restrict_mem measurableSet_frequencySquare,
        ae_restrict_of_ae ae_ne_zero_prod] with k hk hk0
      have hcont := continuousAt_potentialKernelIntegrand z
        (latticeSymbol_ne_zero_of_mem hk hk0)
      exact hcont.tendsto.comp ((tendsto_riemannGrid hk.1.1).prodMk_nhds
        (tendsto_riemannGrid hk.2.1))
  have hlim := hDCT.const_mul ((2 * Real.pi) ^ 2)⁻¹
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with L hL
  exact (hstep L hL).symm

end FroehlichSpencer.BKT.Coulomb
