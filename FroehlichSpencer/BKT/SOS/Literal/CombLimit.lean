/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.SOS.Literal.Marginal
public import FroehlichSpencer.BKT.Rotator.TheoremC.PinnedAdapter
public import Mathlib.Analysis.Normed.Group.Tannery

/-!
# The mixed comb and its limit (the finite comb construction)

In height coordinates the comb observable of the layer on a region `A` is

`mixedComb A N y = ∏_{x∈A} D_N(2πy_x) ∏_{x∉A} D_N(2πN y_x)` (`combMult A N x ∈ {1, N}`),

the comb `D_N` on `A` and the comb with frequencies in `Nℤ` off `A`. Its pairing with a Schwartz
density `f` is the finite sum of Fourier coefficients `Σ_{q ∈ [−N,N]^ι} f̂(m q)`
(`integral_mixedComb_mul_eq_sum`). As `N → ∞` the frequencies with a nonzero coordinate off `A` run
off to infinity, so by Tannery's theorem the pairings converge to `Σ_{q ∈ ℤ^A} f̂(q ⊕ 0)`
(`tendsto_sum_box_combMult`), which is the lattice sum of the marginal of `f` over the coordinates off
`A` (partial Poisson summation, `tsum_fourier_extZero_eq_tsum_marginal`):

`∫ mixedComb A N · f → Σ_{n ∈ ℤ^A} ∫ f(n ⊕ y) dy` (`tendsto_mixedCombPairing`).

This is the comb (7.16) on `A` inside the continuous field: integer heights on `A`, the field
integrated off `A`.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.SOS.Literal

open MeasureTheory Complex Filter Topology
open scoped SchwartzMap
open FroehlichSpencer.BKT.Rotator
open FroehlichSpencer.BKT.Rotator.TheoremC

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The frequency multiplier: `1` on `A`, `N` off `A`. -/
def combMult (A : Finset ι) (N : ℕ) (x : ι) : ℕ := if x ∈ A then 1 else N

omit [Fintype ι] in
theorem one_le_combMult {A : Finset ι} {N : ℕ} (hN : 1 ≤ N) (x : ι) : 1 ≤ combMult A N x := by
  unfold combMult; split_ifs <;> omega

omit [Fintype ι] in
theorem combMult_le {A : Finset ι} {N : ℕ} (hN : 1 ≤ N) (x : ι) : combMult A N x ≤ N := by
  unfold combMult; split_ifs <;> omega

/-- The mixed comb in height coordinates. -/
def mixedComb (A : Finset ι) (N : ℕ) (y : ι → ℝ) : ℂ :=
  ∏ x, ((dirichletComb N (2 * Real.pi * ((combMult A N x : ℝ) * y x)) : ℝ) : ℂ)

/-- The symmetric frequency box `[−N, N]^ι`. -/
def freqBox (N : ℕ) : Finset (ι → ℤ) := Fintype.piFinset fun _ => Finset.Icc (-(N : ℤ)) N

/-- The scaled frequency `x ↦ m(x) q(x)`. -/
def multFreq (A : Finset ι) (N : ℕ) (q : ι → ℤ) : ι → ℤ := fun x => (combMult A N x : ℤ) * q x

/-- **The Fourier expansion of the mixed comb.** -/
theorem mixedComb_eq_sum (A : Finset ι) (N : ℕ) (y : ι → ℝ) :
    mixedComb A N y = ∑ q ∈ freqBox N,
      cexp (((-2 * Real.pi * ∑ x, y x * (multFreq A N q x : ℝ) : ℝ) : ℂ) * I) := by
  unfold mixedComb freqBox
  simp_rw [← sum_Icc_exp_eq_dirichletComb]
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [← Complex.exp_sum]
  congr 1
  rw [← Finset.sum_mul]
  congr 1
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [multFreq]
  push_cast
  ring

omit [DecidableEq ι] in
theorem integrable_char_mul {f : (ι → ℝ) → ℂ} (hf : Integrable f) (ξ : ι → ℝ) :
    Integrable fun y => cexp (((-2 * Real.pi * ∑ x, y x * ξ x : ℝ) : ℂ) * I) * f y := by
  refine hf.bdd_mul (c := 1) ?_ (Eventually.of_forall fun y => ?_)
  · exact (Continuous.aestronglyMeasurable (by fun_prop))
  · rw [Complex.norm_exp]; simp

/-- **The comb pairing is a finite sum of Fourier coefficients.** -/
theorem integral_mixedComb_mul_eq_sum (A : Finset ι) (N : ℕ) {f : (ι → ℝ) → ℂ}
    (hf : Integrable f) :
    ∫ y, mixedComb A N y * f y =
      ∑ q ∈ freqBox N, multiEuclideanFourierCoefficient f (multFreq A N q) := by
  simp_rw [mixedComb_eq_sum, Finset.sum_mul]
  rw [integral_finsetSum _ fun q _ => integrable_char_mul hf _]
  rfl

omit [Fintype ι] in
/-- The scaled frequency map is injective for `N ≥ 1`. -/
theorem multFreq_injective {A : Finset ι} {N : ℕ} (hN : 1 ≤ N) :
    Function.Injective (multFreq A N) := by
  intro q q' h
  funext x
  have hx := congrFun h x
  simp only [multFreq] at hx
  have hm : (combMult A N x : ℤ) ≠ 0 := by
    have := one_le_combMult (A := A) hN x; omega
  exact mul_left_cancel₀ hm hx

/-- **The limit of the scaled box sums** (Tannery): for a summable family `c` on `ℤ^ι`,
`Σ_{q ∈ [−N,N]^ι} c(m q) → Σ_{q ∈ ℤ^A} c(q ⊕ 0)`. -/
theorem tendsto_sum_box_combMult (A : Finset ι) {c : (ι → ℤ) → ℂ} (hc : Summable c) :
    Tendsto (fun N : ℕ => ∑ q ∈ freqBox N, c (multFreq A N q)) atTop
      (𝓝 (∑' q : {x // x ∈ A} → ℤ, c (extZeroInt (· ∈ A) q))) := by
  classical
  set a : ℕ → (ι → ℤ) → ℂ := fun N r => if r ∈ (freqBox N).image (multFreq A N) then c r else 0
    with ha
  set g : (ι → ℤ) → ℂ := fun r => if ∀ x, x ∉ A → r x = 0 then c r else 0 with hg
  -- the box sums are tsums of `a N`
  have hsum : ∀ N : ℕ, 1 ≤ N → ∑ q ∈ freqBox N, c (multFreq A N q) = ∑' r, a N r := by
    intro N hN
    rw [tsum_eq_sum (s := (freqBox N).image (multFreq A N)) fun r hr => by
      simp only [ha, hr, ↓reduceIte]]
    rw [Finset.sum_image fun q _ q' _ h => multFreq_injective hN h]
    refine Finset.sum_congr rfl fun q hq => ?_
    simp only [ha]
    split_ifs with h
    · rfl
    · exact absurd (Finset.mem_image.mpr ⟨q, hq, rfl⟩) h
  -- the pointwise limit
  have hpt : ∀ r, Tendsto (fun N => a N r) atTop (𝓝 (g r)) := by
    intro r
    refine tendsto_const_nhds.congr' ?_
    by_cases h0 : ∀ x, x ∉ A → r x = 0
    · filter_upwards [eventually_ge_atTop (∑ x, (r x).natAbs + 1)] with N hN
      have hmem : r ∈ (freqBox N).image (multFreq A N) := by
        refine Finset.mem_image.mpr ⟨r, ?_, ?_⟩
        · simp only [freqBox, Fintype.mem_piFinset, Finset.mem_Icc]
          intro x
          have h1 : (r x).natAbs ≤ ∑ y, (r y).natAbs :=
            Finset.single_le_sum (f := fun y => (r y).natAbs) (fun _ _ => Nat.zero_le _)
              (Finset.mem_univ x)
          omega
        · funext x
          simp only [multFreq, combMult]
          by_cases hx : x ∈ A
          · simp [hx]
          · simp [hx, h0 x hx]
      simp only [ha, hg, hmem, ↓reduceIte]
      exact ite_eq_left_iff.mpr fun h => absurd h0 h
    · push Not at h0
      obtain ⟨x, hxA, hx0⟩ := h0
      filter_upwards [eventually_ge_atTop ((r x).natAbs + 1)] with N hN
      have hnot : r ∉ (freqBox N).image (multFreq A N) := by
        intro hmem
        obtain ⟨q, -, hq⟩ := Finset.mem_image.mp hmem
        have hrx := congrFun hq x
        simp only [multFreq, combMult, hxA, ↓reduceIte] at hrx
        have hq0 : q x ≠ 0 := by rintro h; rw [h, mul_zero] at hrx; exact hx0 hrx.symm
        have : (N : ℤ).natAbs ≤ (r x).natAbs := by
          rw [← hrx, Int.natAbs_mul]
          exact Nat.le_mul_of_pos_right _ (Int.natAbs_pos.mpr hq0)
        simp at this
        omega
      have hg0 : g r = 0 := by
        simp only [hg]
        split_ifs with h
        · exact absurd (h x hxA) hx0
        · rfl
      simp only [ha, hnot, ↓reduceIte, hg0]
  have hlim : Tendsto (fun N => ∑' r, a N r) atTop (𝓝 (∑' r, g r)) := by
    refine tendsto_tsum_of_dominated_convergence hc.norm hpt (Eventually.of_forall fun N r => ?_)
    simp only [ha]
    split_ifs
    · exact le_rfl
    · simp
  have hg_eq : ∑' r, g r = ∑' q : {x // x ∈ A} → ℤ, c (extZeroInt (· ∈ A) q) := by
    have hinj : Function.Injective (extZeroInt (ι := ι) (· ∈ A)) := by
      intro q q' h
      funext x
      have := congrFun h x.1
      simp only [extZeroInt, dite_eq_left x.2] at this
      exact this
    rw [← hinj.tsum_eq]
    · refine tsum_congr fun q => ?_
      simp only [hg]
      split_ifs with h
      · rfl
      · exact absurd (fun x hx => by simp [extZeroInt, hx]) h
    · intro r hr
      simp only [Function.mem_support, hg] at hr
      split_ifs at hr with h0
      · refine ⟨fun x => r x.1, ?_⟩
        funext x
        simp only [extZeroInt]
        by_cases hx : x ∈ A
        · simp [hx]
        · simp [hx, h0 x hx]
      · exact absurd rfl hr
  rw [hg_eq] at hlim
  exact hlim.congr' (eventually_atTop.mpr ⟨1, fun N hN => (hsum N hN).symm⟩)

/-- **The comb on `A` inside the continuous field**: the mixed comb pairings of a Schwartz density
converge to the lattice sum of its marginal over the coordinates off `A`. -/
theorem tendsto_mixedCombPairing (A : Finset ι) (f : 𝓢(ι → ℝ, ℂ)) :
    Tendsto (fun N : ℕ => ∫ y, mixedComb A N y * f y) atTop
      (𝓝 (∑' n : {x // x ∈ A} → ℤ, marginalPi (· ∈ A) f (fun i => (n i : ℝ)))) := by
  have h := tendsto_sum_box_combMult A (summable_multiEuclideanFourierCoefficient_of_schwartz f)
  rw [(tsum_fourier_extZero_eq_tsum_marginal (· ∈ A) f).1] at h
  exact h.congr fun N => (integral_mixedComb_mul_eq_sum A N f.integrable).symm

end FroehlichSpencer.BKT.SOS.Literal

end
