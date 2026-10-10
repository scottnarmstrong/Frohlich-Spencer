/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.Infra.Stieltjes.Continuity
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Lipschitz upgrade for the continuity theorem of Stieltjes transforms

If finite measures `μ_n` with uniformly bounded masses have Stieltjes transforms converging on a
dense subset of the upper half-plane, and obey `μ_n ((a, b]) ≤ ρ (b - a)` uniformly, then the limit
`μ` obeys the same bound, has no atoms, and (when the total masses converge) the distribution
functions converge at every `E`.

**Scope.** The uniform bound `μ_n ((a, b]) ≤ ρ (b - a)` for all `a ≤ b` forces every `μ_n` to be
non-atomic; it can never hold for a purely atomic measure such as the normalized eigenvalue
counting measure of a single realization. For the integrated density of states it is meant to be
applied to the **averaged** measures `ν_Λ = E[μ_Λ]` (which obey Wegner's bound deterministically,
`Infra.Wegner`, and whose Stieltjes transforms converge by dominated convergence): this gives a
limit without atoms, and then `tendsto_measure_Iic_of_tendsto_stieltjes` (`Continuity.lean`),
applied realization by realization to the atomic `μ_Λ`, gives convergence at every `E`.
-/

@[expose] public section

open MeasureTheory Complex Filter Topology Set

namespace FroehlichSpencer.Infra

variable {μs : ℕ → Measure ℝ} [∀ n, IsFiniteMeasure (μs n)] {μ : Measure ℝ} [IsFiniteMeasure μ]

private theorem linearRamp_mono_aux {c c' : ℝ} (δ t : ℝ) (hδ : 0 < δ) (h : c ≤ c') :
    linearRamp c δ t ≤ linearRamp c' δ t := by
  unfold linearRamp
  gcongr

private theorem integral_indicator_const_one_aux (ν : Measure ℝ) {s : Set ℝ}
    (hs : MeasurableSet s) :
    ∫ t, s.indicator (fun _ => (1 : ℝ)) t ∂ν = ν.real s :=
  integral_indicator_one hs

/-- A continuous bump `1_{[a+δ, b-δ]} ≤ g ≤ 1_{(a,b]}`. -/
private noncomputable def bump (a b δ t : ℝ) : ℝ := linearRamp b δ t - linearRamp (a + δ) δ t

private theorem continuous_bump (a b δ : ℝ) : Continuous (bump a b δ) :=
  (continuous_linearRamp b δ).sub (continuous_linearRamp (a + δ) δ)

private theorem bump_eq_zero {a b δ : ℝ} (hδ : 0 < δ) (hab : a + 2 * δ ≤ b) {t : ℝ}
    (ht : t ≤ a ∨ b ≤ t) : bump a b δ t = 0 := by
  unfold bump
  rcases ht with ht | ht
  · rw [linearRamp_eq_one hδ (by linarith), linearRamp_eq_one hδ (by linarith)]; ring
  · rw [linearRamp_eq_zero hδ ht, linearRamp_eq_zero hδ (by linarith)]; ring

private theorem bump_nonneg {a b δ : ℝ} (hδ : 0 < δ) (hab : a + 2 * δ ≤ b) (t : ℝ) :
    0 ≤ bump a b δ t := by
  unfold bump
  have := linearRamp_mono_aux (c := a + δ) (c' := b) δ t hδ (by linarith)
  linarith

private theorem bump_le_indicator {a b δ : ℝ} (hδ : 0 < δ) (hab : a + 2 * δ ≤ b) (t : ℝ) :
    bump a b δ t ≤ (Ioc a b).indicator (fun _ => (1 : ℝ)) t := by
  by_cases ht : t ∈ Ioc a b
  · rw [indicator_of_mem ht]
    unfold bump
    linarith [linearRamp_le_one b δ t, linearRamp_nonneg (a + δ) δ t]
  · rw [indicator_of_notMem ht]
    refine (bump_eq_zero hδ hab ?_).le
    simp only [mem_Ioc, not_and_or, not_lt, not_le] at ht
    rcases ht with ht | ht
    · exact Or.inl ht
    · exact Or.inr ht.le

private theorem indicator_le_bump {a b δ : ℝ} (hδ : 0 < δ) (hab : a + 2 * δ ≤ b) (t : ℝ) :
    (Icc (a + δ) (b - δ)).indicator (fun _ => (1 : ℝ)) t ≤ bump a b δ t := by
  by_cases ht : t ∈ Icc (a + δ) (b - δ)
  · rw [indicator_of_mem ht]
    unfold bump
    rw [linearRamp_eq_one hδ ht.2, linearRamp_eq_zero hδ ht.1]; norm_num
  · rw [indicator_of_notMem ht]
    exact bump_nonneg hδ hab t

private theorem integrable_bump (ν : Measure ℝ) [IsFiniteMeasure ν] {a b δ : ℝ} (hδ : 0 < δ)
    (hab : a + 2 * δ ≤ b) : Integrable (bump a b δ) ν := by
  refine (continuous_bump a b δ).integrable_of_hasCompactSupport (HasCompactSupport.intro
    (isCompact_Icc (a := a) (b := b)) fun t ht => ?_)
  refine bump_eq_zero hδ hab ?_
  simp only [mem_Icc, not_and_or, not_le] at ht
  rcases ht with ht | ht
  · exact Or.inl ht.le
  · exact Or.inr ht.le

private theorem tendsto_bump_cocompact {a b δ : ℝ} (hδ : 0 < δ) (hab : a + 2 * δ ≤ b) :
    Tendsto (bump a b δ) (cocompact ℝ) (𝓝 0) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [(isCompact_Icc (a := a) (b := b)).compl_mem_cocompact] with t ht
  symm
  refine bump_eq_zero hδ hab ?_
  simp only [mem_compl_iff, mem_Icc, not_and_or, not_le] at ht
  rcases ht with ht | ht
  · exact Or.inl ht.le
  · exact Or.inr ht.le

private theorem measureReal_Icc_le_aux {M : ℝ} (hM : ∀ n, (μs n).real univ ≤ M)
    {D : Set ℂ} (hdense : {z : ℂ | 0 < z.im} ⊆ closure D)
    (h : ∀ z ∈ D, Tendsto (fun n => stieltjes (μs n) z) atTop (𝓝 (stieltjes μ z)))
    {ρ : ℝ} (hρ : ∀ n a b, a ≤ b → (μs n).real (Ioc a b) ≤ ρ * (b - a))
    {a b δ : ℝ} (hδ : 0 < δ) (hab : a + 2 * δ ≤ b) :
    μ.real (Icc (a + δ) (b - δ)) ≤ ρ * (b - a) := by
  have hlim := tendsto_integral_of_tendsto_stieltjes hM hdense h (continuous_bump a b δ)
    (tendsto_bump_cocompact hδ hab)
  have h1 : ∫ t, bump a b δ t ∂μ ≤ ρ * (b - a) := by
    refine le_of_tendsto' hlim fun n => ?_
    refine le_trans (integral_mono (integrable_bump _ hδ hab)
      ((integrable_const (μ := μs n) (1 : ℝ)).indicator measurableSet_Ioc)
      (bump_le_indicator hδ hab)) ?_
    rw [integral_indicator_const_one_aux _ measurableSet_Ioc]
    exact hρ n a b (by linarith)
  refine le_trans ?_ h1
  rw [← integral_indicator_const_one_aux μ measurableSet_Icc]
  exact integral_mono ((integrable_const (μ := μ) (1 : ℝ)).indicator measurableSet_Icc)
    (integrable_bump _ hδ hab) (indicator_le_bump hδ hab)

private theorem measureReal_Ioo_le_aux {C : ℝ} {a b : ℝ} (hab : a < b)
    (hC : ∀ δ, 0 < δ → a + 2 * δ ≤ b → μ.real (Icc (a + δ) (b - δ)) ≤ C) :
    μ.real (Ioo a b) ≤ C := by
  set s : ℕ → Set ℝ := fun k => Icc (a + (b - a) / (k + 3)) (b - (b - a) / (k + 3)) with hs
  have hpos : ∀ k : ℕ, 0 < (b - a) / ((k : ℝ) + 3) := fun k => by
    have : 0 < b - a := by linarith
    positivity
  have hmono : Monotone s := by
    intro i j hij
    have hle : ((i : ℝ) + 3) ≤ (j : ℝ) + 3 := by
      have : (i : ℝ) ≤ j := by exact_mod_cast hij
      linarith
    have : (b - a) / ((j : ℝ) + 3) ≤ (b - a) / ((i : ℝ) + 3) :=
      div_le_div_of_nonneg_left (by linarith) (by positivity) hle
    exact Icc_subset_Icc (by linarith) (by linarith)
  have hU : (⋃ k, s k) = Ioo a b := by
    ext x
    simp only [mem_iUnion, hs, mem_Icc, mem_Ioo]
    constructor
    · rintro ⟨k, h1, h2⟩
      have := hpos k
      constructor <;> linarith
    · rintro ⟨h1, h2⟩
      set m := min (x - a) (b - x) with hm
      have hm0 : 0 < m := lt_min (by linarith) (by linarith)
      obtain ⟨k, hk⟩ := exists_nat_ge ((b - a) / m)
      have hk' : (b - a) ≤ m * ((k : ℝ) + 3) := by
        rw [div_le_iff₀ hm0] at hk
        have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        nlinarith
      have hd : (b - a) / ((k : ℝ) + 3) ≤ m := by
        rw [div_le_iff₀ (by positivity)]; linarith
      exact ⟨k, by linarith [min_le_left (x - a) (b - x)],
        by linarith [min_le_right (x - a) (b - x)]⟩
  have ht := tendsto_measure_iUnion_atTop (μ := μ) hmono
  rw [hU] at ht
  have ht2 := (ENNReal.tendsto_toReal (measure_ne_top μ _)).comp ht
  refine le_of_tendsto' ht2 fun k => ?_
  have hk := hpos k
  have h2 : a + 2 * ((b - a) / ((k : ℝ) + 3)) ≤ b := by
    have : (2 : ℝ) * ((b - a) / ((k : ℝ) + 3)) ≤ b - a := by
      rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
      have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      nlinarith [sub_pos.2 hab]
    linarith
  exact hC _ hk h2

theorem measure_singleton_eq_zero_of_tendsto_stieltjes {M : ℝ} (hM : ∀ n, (μs n).real univ ≤ M)
    {D : Set ℂ} (hdense : {z : ℂ | 0 < z.im} ⊆ closure D)
    (h : ∀ z ∈ D, Tendsto (fun n => stieltjes (μs n) z) atTop (𝓝 (stieltjes μ z)))
    {ρ : ℝ} (hρ : ∀ n a b, a ≤ b → (μs n).real (Ioc a b) ≤ ρ * (b - a)) (E : ℝ) :
    μ {E} = 0 := by
  have hρ0 : 0 ≤ ρ := by
    have := hρ 0 0 1 zero_le_one
    have h0 : 0 ≤ (μs 0).real (Ioc 0 1) := measureReal_nonneg
    linarith
  have hle : ∀ ε : ℝ, 0 < ε → μ.real {E} ≤ ρ * (2 * ε) := by
    intro ε hε
    have := measureReal_Icc_le_aux hM hdense h hρ (a := E - ε) (b := E + ε) (δ := ε / 2)
      (by linarith) (by linarith)
    refine le_trans (measureReal_mono ?_) (this.trans_eq (by ring))
    intro x hx
    rw [mem_singleton_iff] at hx
    subst hx
    constructor <;> linarith
  have h0 : μ.real {E} ≤ 0 := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    by_cases hρp : ρ = 0
    · have := hle 1 one_pos
      rw [hρp] at this
      linarith
    · have hρp' : 0 < ρ := lt_of_le_of_ne hρ0 (Ne.symm hρp)
      have := hle (ε / (2 * ρ)) (by positivity)
      have e : ρ * (2 * (ε / (2 * ρ))) = ε := by field_simp
      linarith
  have : μ.real {E} = 0 := le_antisymm h0 measureReal_nonneg
  simpa [Measure.real, ENNReal.toReal_eq_zero_iff, measure_ne_top] using this

theorem measure_Ioc_le_of_tendsto_stieltjes {M : ℝ} (hM : ∀ n, (μs n).real univ ≤ M)
    {D : Set ℂ} (hdense : {z : ℂ | 0 < z.im} ⊆ closure D)
    (h : ∀ z ∈ D, Tendsto (fun n => stieltjes (μs n) z) atTop (𝓝 (stieltjes μ z)))
    {ρ : ℝ} (hρ : ∀ n a b, a ≤ b → (μs n).real (Ioc a b) ≤ ρ * (b - a))
    {a b : ℝ} (hab : a ≤ b) : μ.real (Ioc a b) ≤ ρ * (b - a) := by
  rcases hab.eq_or_lt with rfl | hlt
  · simp
  have hρ0 : 0 ≤ ρ := by
    have := hρ 0 0 1 zero_le_one
    have h0 : 0 ≤ (μs 0).real (Ioc 0 1) := measureReal_nonneg
    linarith
  have hIoo := measureReal_Ioo_le_aux (μ := μ) hlt fun δ hδ hδ2 =>
    measureReal_Icc_le_aux hM hdense h hρ hδ hδ2
  have hat := measure_singleton_eq_zero_of_tendsto_stieltjes hM hdense h hρ b
  have hat' : μ.real {b} = 0 := by simp [Measure.real, hat]
  have hsplit : μ.real (Ioc a b) ≤ μ.real (Ioo a b) + μ.real {b} := by
    refine le_trans (measureReal_mono ?_) (measureReal_union_le _ _)
    intro x hx
    rcases hx.2.eq_or_lt with rfl | hxb
    · exact Or.inr rfl
    · exact Or.inl ⟨hx.1, hxb⟩
  linarith

theorem tendsto_measure_Iic_of_tendsto_stieltjes_of_lipschitz
    {D : Set ℂ} (hdense : {z : ℂ | 0 < z.im} ⊆ closure D)
    (h : ∀ z ∈ D, Tendsto (fun n => stieltjes (μs n) z) atTop (𝓝 (stieltjes μ z)))
    (hmass : Tendsto (fun n => (μs n).real univ) atTop (𝓝 (μ.real univ)))
    {ρ : ℝ} (hρ : ∀ n a b, a ≤ b → (μs n).real (Ioc a b) ≤ ρ * (b - a)) (E : ℝ) :
    Tendsto (fun n => (μs n).real (Iic E)) atTop (𝓝 (μ.real (Iic E))) := by
  obtain ⟨M, hM⟩ := (Metric.isBounded_range_of_tendsto _ hmass).bddAbove
  have hM' : ∀ n, (μs n).real univ ≤ M := fun n => hM (mem_range_self n)
  exact tendsto_measure_Iic_of_tendsto_stieltjes hdense h hmass
    (measure_singleton_eq_zero_of_tendsto_stieltjes hM' hdense h hρ E)

end FroehlichSpencer.Infra
