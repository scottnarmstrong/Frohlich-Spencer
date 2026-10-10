/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.Infra.Green.Existence
public import FroehlichSpencer.Infra.Green.FiniteVolumeRegularity
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

/-!
# Infinite-volume solution: continuity in `z`, measurability in the potential

For families of square-summable solutions of `∑' w, a x w * ψ w + (v x - z) * ψ x = δ_y x`
(generic Hermitian kernel of finite row support and bounded row sums) we prove Lipschitz dependence
on `z` in `ℓ²`, continuity of `z ↦ ψ_z(x)` on `{Im z ≠ 0}`, and measurability of `v ↦ ψ_v(x)` for
the product σ-algebra on `X → ℝ` (countable `X`).

No Green function is defined here.

Motivation: Fröhlich–Spencer (1983), (1.4), Fröhlich–Spencer (1983).
-/

@[expose] public section

open Filter Topology

namespace FroehlichSpencer.Infra

variable {X : Type*} [DecidableEq X] {a : X → X → ℂ} {K : ℝ}

omit [DecidableEq X] in
private theorem summable_row (hfin : ∀ x, {y | a x y ≠ 0}.Finite) (x : X) (g : X → ℂ) :
    Summable fun w => a x w * g w :=
  summable_of_ne_finset_zero (s := (hfin x).toFinset) fun w hw => by
    have : a x w = 0 := by simpa using hw
    simp [this]

omit [DecidableEq X] in
private theorem summable_norm_sq' {ψ : X → ℂ} (hψ : Memℓp ψ 2) :
    Summable fun x => ‖ψ x‖ ^ 2 := by
  have := hψ.summable (by simp)
  simpa using this

/-- Lipschitz dependence on `z` in `ℓ²`. -/
theorem tsum_norm_sq_sub_le_of_eq_single (ha : ∀ x y, a y x = star (a x y))
    (hfin : ∀ x, {y | a x y ≠ 0}.Finite) (hK : ∀ x (s : Finset X), ∑ y ∈ s, ‖a x y‖ ≤ K)
    (v : X → ℝ) {z z' : ℂ} (hz : z.im ≠ 0) (hz' : z'.im ≠ 0) {y : X} {ψ ψ' : X → ℂ}
    (hψ : Memℓp ψ 2)
    (hψeq : ∀ x, ∑' w, a x w * ψ w + ((v x : ℂ) - z) * ψ x = (Pi.single y 1 : X → ℂ) x)
    (hψ' : Memℓp ψ' 2)
    (hψ'eq : ∀ x, ∑' w, a x w * ψ' w + ((v x : ℂ) - z') * ψ' x = (Pi.single y 1 : X → ℂ) x) :
    ∑' x, ‖ψ x - ψ' x‖ ^ 2 ≤ ‖z - z'‖ ^ 2 / (z.im ^ 2 * z'.im ^ 2) := by
  have hz2 : 0 < z.im ^ 2 := by positivity
  have hz2' : 0 < z'.im ^ 2 := by positivity
  have hφ : Memℓp (ψ - ψ') 2 := hψ.sub hψ'
  have hf : Memℓp ((z - z') • ψ') 2 := hψ'.const_smul (z - z')
  have heq : ∀ x, ∑' w, a x w * (ψ - ψ') w + ((v x : ℂ) - z) * (ψ - ψ') x =
      ((z - z') • ψ') x := by
    intro x
    have h1 : ∑' w, a x w * (ψ w - ψ' w) =
        ∑' w, a x w * ψ w - ∑' w, a x w * ψ' w := by
      rw [← (summable_row hfin x ψ).tsum_sub (summable_row hfin x ψ')]
      exact tsum_congr fun w => by ring
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [h1]
    linear_combination hψeq x - hψ'eq x
  have h := tsum_norm_sq_le_of_eq ha hfin hK v hz hφ hf heq
  have h2 := tsum_norm_sq_le_of_eq_single ha hfin hK v hz' hψ' hψ'eq
  have h3 : ∑' x, ‖((z - z') • ψ') x‖ ^ 2 = ‖z - z'‖ ^ 2 * ∑' x, ‖ψ' x‖ ^ 2 := by
    rw [← tsum_mul_left]
    exact tsum_congr fun x => by simp [mul_pow]
  rw [h3] at h
  simp only [Pi.sub_apply] at h
  calc ∑' x, ‖ψ x - ψ' x‖ ^ 2 ≤ (‖z - z'‖ ^ 2 * ∑' x, ‖ψ' x‖ ^ 2) / z.im ^ 2 := h
    _ ≤ ‖z - z'‖ ^ 2 * (1 / z'.im ^ 2) / z.im ^ 2 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h2 (sq_nonneg _)) hz2.le
    _ = ‖z - z'‖ ^ 2 / (z.im ^ 2 * z'.im ^ 2) := by field_simp

/-- Continuity in `z` of any family of `ℓ²` solutions. -/
theorem continuousOn_of_forall_eq_single (ha : ∀ x y, a y x = star (a x y))
    (hfin : ∀ x, {y | a x y ≠ 0}.Finite) (hK : ∀ x (s : Finset X), ∑ y ∈ s, ‖a x y‖ ≤ K)
    (v : X → ℝ) (y x : X) {Ψ : ℂ → X → ℂ}
    (hΨ : ∀ z, z.im ≠ 0 → Memℓp (Ψ z) 2 ∧
      ∀ x', ∑' w, a x' w * Ψ z w + ((v x' : ℂ) - z) * Ψ z x' = (Pi.single y 1 : X → ℂ) x') :
    ContinuousOn (fun z => Ψ z x) {z | z.im ≠ 0} := by
  intro z0 hz0
  have hz0' : z0.im ≠ 0 := hz0
  have hp : 0 < |z0.im| := abs_pos.2 hz0'
  set C : ℝ := 2 / z0.im ^ 2 with hC
  have hev : ∀ᶠ z in 𝓝[{z | z.im ≠ 0}] z0, ‖Ψ z x - Ψ z0 x‖ ≤ C * ‖z - z0‖ := by
    have hball : ∀ᶠ z in 𝓝 z0, ‖z - z0‖ < |z0.im| / 2 := by
      have : Tendsto (fun z : ℂ => ‖z - z0‖) (𝓝 z0) (𝓝 ‖z0 - z0‖) :=
        ((continuous_id.sub continuous_const).norm).tendsto z0
      simp only [sub_self, norm_zero] at this
      exact this.eventually (gt_mem_nhds (by positivity))
    filter_upwards [nhdsWithin_le_nhds hball, self_mem_nhdsWithin] with z hzb hzs
    have hzs' : z.im ≠ 0 := hzs
    have himz : |z0.im| / 2 ≤ |z.im| := by
      have : |z0.im - z.im| ≤ ‖z - z0‖ := by
        rw [abs_sub_comm]
        simpa using Complex.abs_im_le_norm (z - z0)
      have h2 := abs_sub_abs_le_abs_sub z0.im z.im
      linarith only [this, h2, hzb]
    have hsq := tsum_norm_sq_sub_le_of_eq_single ha hfin hK v hzs' hz0' (ψ := Ψ z) (ψ' := Ψ z0)
      (hΨ z hzs').1 (hΨ z hzs').2 (hΨ z0 hz0').1 (hΨ z0 hz0').2
    have hxle : ‖Ψ z x - Ψ z0 x‖ ^ 2 ≤ ∑' x, ‖Ψ z x - Ψ z0 x‖ ^ 2 :=
      (summable_norm_sq' ((hΨ z hzs').1.sub (hΨ z0 hz0').1)).le_tsum x fun j _ => by positivity
    have hzz : 0 < z.im ^ 2 := by positivity
    have hzz0 : 0 < z0.im ^ 2 := by positivity
    have hlow : z0.im ^ 2 ≤ 4 * z.im ^ 2 := by
      have := mul_self_le_mul_self (by positivity) himz
      rw [← sq_abs z.im, ← sq_abs z0.im]
      nlinarith only [this]
    have hfin2 : ‖z - z0‖ ^ 2 / (z.im ^ 2 * z0.im ^ 2) ≤ (C * ‖z - z0‖) ^ 2 := by
      rw [div_le_iff₀ (by positivity), hC, mul_pow, div_pow, ← pow_mul]
      have h4 : 0 ≤ ‖z - z0‖ ^ 2 := sq_nonneg _
      have : (2 : ℝ) ^ 2 / z0.im ^ (2 * 2) * ‖z - z0‖ ^ 2 * (z.im ^ 2 * z0.im ^ 2) =
          4 * z.im ^ 2 / z0.im ^ 2 * ‖z - z0‖ ^ 2 := by
        field_simp
        ring
      rw [this]
      have h5 : 1 ≤ 4 * z.im ^ 2 / z0.im ^ 2 := by
        rw [le_div_iff₀ hzz0]; linarith only [hlow]
      nlinarith only [h5, h4]
    exact le_of_sq_le_sq (hxle.trans (hsq.trans hfin2)) (by positivity)
  refine tendsto_iff_norm_sub_tendsto_zero.2
    (squeeze_zero_norm' (a := fun z => C * ‖z - z0‖) ?_ ?_)
  · filter_upwards [hev] with z hz
    simpa [norm_norm] using hz
  · have : Tendsto (fun z : ℂ => C * ‖z - z0‖) (𝓝 z0) (𝓝 (C * ‖z0 - z0‖)) :=
      (((continuous_id.sub continuous_const).norm).const_mul C).tendsto z0
    simp only [sub_self, norm_zero, mul_zero] at this
    exact this.mono_left nhdsWithin_le_nhds

private theorem exists_seq_mem' [Countable X] (y : X) :
    ∃ Λ : ℕ → Finset X, ∀ x, ∀ᶠ n in atTop, x ∈ Λ n := by
  have : Nonempty X := ⟨y⟩
  obtain ⟨f, hf⟩ := exists_surjective_nat X
  refine ⟨fun n => (Finset.range n).image f, fun x => ?_⟩
  obtain ⟨m, rfl⟩ := hf x
  filter_upwards [eventually_gt_atTop m] with n hn
  exact Finset.mem_image.2 ⟨m, Finset.mem_range.2 hn, rfl⟩

/-- Measurability in the potential of any family of `ℓ²` solutions (countable `X`). -/
theorem measurable_of_forall_eq_single [Countable X] (ha : ∀ x y, a y x = star (a x y))
    (hfin : ∀ x, {y | a x y ≠ 0}.Finite) (hK : ∀ x (s : Finset X), ∑ y ∈ s, ‖a x y‖ ≤ K)
    {z : ℂ} (hz : z.im ≠ 0) (y x : X) {Ψ : (X → ℝ) → X → ℂ}
    (hΨ : ∀ v, Memℓp (Ψ v) 2 ∧
      ∀ x', ∑' w, a x' w * Ψ v w + ((v x' : ℂ) - z) * Ψ v x' = (Pi.single y 1 : X → ℂ) x') :
    Measurable fun v => Ψ v x := by
  obtain ⟨Λ, hΛ⟩ := exists_seq_mem' (X := X) y
  refine measurable_of_tendsto_metrizable
    (f := fun n v => resolventColumn a v (Λ n) z y x)
    (fun n => measurable_resolventColumn ha (Λ n) hz y x) ?_
  refine tendsto_pi_nhds.2 fun v => ?_
  exact (tendsto_resolventColumn_of_eventually_mem ha hfin hK v hz hΛ (hΨ v).1 (hΨ v).2).2 x

end FroehlichSpencer.Infra
