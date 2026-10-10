/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Rotator.Ginibre.Evaluation

/-!
# Single-site reference measures: the circle and the clock

The circle measure is Lebesgue measure on `[-π, π)` (Haar measure of the circle, total mass
`2π`); the `N`-state clock measure puts unit mass at the angles `2πj/N`, `0 ≤ j < N` (Haar
measure of `ℤ_N` on the circle, total mass `N`; FS81 (7.1)–(7.2), J pp. 584–585). Their integer
Fourier coefficients are `2π·1[k = 0]` and `N·1[N ∣ k]`. Product measures over a finite site set
restrict along injective site maps to constant multiples of the smaller product measure.
-/

@[expose] public section

open MeasureTheory Set
open FroehlichSpencer.BKT.Rotator FroehlichSpencer.BKT.Rotator.Ginibre
open scoped Real

noncomputable section

namespace FroehlichSpencer.BKT.Ginibre

/-- Haar measure of the circle: Lebesgue measure on `[-π, π)`. -/
def circleMeasure : Measure ℝ :=
  volume.restrict (Ico (-π) π)

/-- Haar measure of `ℤ_N` on the circle: unit masses at the angles `2πj/N`. -/
def clockMeasure (N : ℕ) : Measure ℝ :=
  ∑ j : Fin N, Measure.dirac (2 * π * (j : ℝ) / N)

/-- The product of a single-site measure over a finite site set. -/
def siteProduct (ν : Measure ℝ) (V : Type*) [Fintype V] : Measure (V → ℝ) :=
  Measure.pi fun _ : V => ν

/-- `ν` has the real integer Fourier coefficients `lam`. -/
def HasRealFourier (ν : Measure ℝ) (lam : ℤ → ℝ) : Prop :=
  ∀ k : ℤ, ∫ t, Complex.exp (Complex.I * (k : ℂ) * (t : ℂ)) ∂ν = (lam k : ℂ)

/-- Fourier coefficients of the circle measure. -/
def circleFourier (k : ℤ) : ℝ :=
  if k = 0 then 2 * π else 0

/-- Fourier coefficients of the `N`-state clock measure. -/
def clockFourier (N : ℕ) (k : ℤ) : ℝ :=
  if (N : ℤ) ∣ k then N else 0

instance isFiniteMeasure_circleMeasure : IsFiniteMeasure circleMeasure :=
  ⟨by simp [circleMeasure, Real.volume_Ico]⟩

instance isFiniteMeasure_clockMeasure (N : ℕ) : IsFiniteMeasure (clockMeasure N) :=
  ⟨by simp [clockMeasure, Finset.sum_apply]⟩

theorem circleMeasure_univ : circleMeasure univ = ENNReal.ofReal (2 * π) := by
  rw [circleMeasure, Measure.restrict_apply_univ, Real.volume_Ico]
  congr 1
  ring

theorem clockMeasure_univ (N : ℕ) : clockMeasure N univ = N := by
  simp [clockMeasure, Finset.sum_apply]

theorem hasRealFourier_circle : HasRealFourier circleMeasure circleFourier := by
  intro k
  rw [circleFourier, circleMeasure, integral_character_Ico]
  split_ifs <;> simp

theorem hasRealFourier_clock {N : ℕ} (hN : 0 < N) : HasRealFourier (clockMeasure N) (clockFourier N) := by
  intro k
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  set ζ : ℂ := Complex.exp (2 * π * Complex.I * k / N) with hζ
  have hterm : ∀ j : Fin N, Complex.exp (Complex.I * (k : ℂ) * ((2 * π * (j : ℝ) / N : ℝ) : ℂ))
      = ζ ^ (j : ℕ) := by
    intro j
    rw [hζ, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hint : ∫ t, Complex.exp (Complex.I * (k : ℂ) * (t : ℂ)) ∂clockMeasure N =
      ∑ j : Fin N, ζ ^ (j : ℕ) := by
    rw [clockMeasure, integral_finsetSum_measure]
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [integral_dirac, hterm]
    · intro j _
      exact integrable_dirac enorm_lt_top
  have hζN : ζ ^ N = 1 := by
    rw [hζ, ← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
    exact ⟨k, by field_simp⟩
  have hζ1 : ζ = 1 ↔ (N : ℤ) ∣ k := by
    rw [hζ, Complex.exp_eq_one_iff]
    constructor
    · rintro ⟨n, hn⟩
      refine ⟨n, ?_⟩
      have : (k : ℂ) = (N : ℂ) * n := by
        field_simp at hn
        have h2 : (2 * π * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
        apply mul_left_cancel₀ h2
        linear_combination (2 * π * Complex.I) * hn
      exact_mod_cast this
    · rintro ⟨n, rfl⟩
      refine ⟨n, ?_⟩
      push_cast
      field_simp
  rw [hint, Fin.sum_univ_eq_sum_range (fun j => ζ ^ j) N, clockFourier]
  by_cases hd : (N : ℤ) ∣ k
  · rw [ite_eq_left_iff.mpr (fun h => absurd hd h)] 
    have := (hζ1.mpr hd)
    rw [this]
    simp
  · rw [ite_eq_right_iff.mpr (fun h => absurd h hd)]
    have hne : ζ ≠ 1 := fun h => hd (hζ1.mp h)
    rw [geom_sum_eq hne, hζN]
    simp

theorem siteProduct_circle (V : Type*) [Fintype V] [DecidableEq V] :
    siteProduct circleMeasure V = rotatorRawAngleMeasure V :=
  rfl

instance isFiniteMeasure_siteProduct (ν : Measure ℝ) [IsFiniteMeasure ν] (V : Type*) [Fintype V] :
    IsFiniteMeasure (siteProduct ν V) := by
  unfold siteProduct
  infer_instance

theorem siteProduct_univ_ne_zero {ν : Measure ℝ} [IsFiniteMeasure ν] (hν : ν univ ≠ 0)
    (V : Type*) [Fintype V] : siteProduct ν V univ ≠ 0 := by
  rw [siteProduct, Measure.pi_univ]
  exact Finset.prod_ne_zero_iff.mpr fun _ _ => hν

private lemma siteProduct_zero_of_nonempty (V : Type*) [Fintype V] [Nonempty V] :
    siteProduct (0 : Measure ℝ) V = 0 := by
  apply Measure.measure_univ_eq_zero.mp
  rw [siteProduct, Measure.pi_univ]
  obtain ⟨v⟩ := ‹Nonempty V›
  exact Finset.prod_eq_zero (Finset.mem_univ v) (by simp)

/-- Restricting along an injective site map. -/
theorem map_comp_siteProduct {ν : Measure ℝ} [IsFiniteMeasure ν] {V W : Type*} [Fintype V]
    [Fintype W] {ι : V → W} (hι : Function.Injective ι) :
    (siteProduct ν W).map (fun θ : W → ℝ => θ ∘ ι) =
      ν univ ^ (Fintype.card W - Fintype.card V) • siteProduct ν V := by
  classical
  have hmeas : Measurable (fun θ : W → ℝ => θ ∘ ι) := by fun_prop
  by_cases h0 : ν univ = 0
  · have hν0 : ν = 0 := Measure.measure_univ_eq_zero.mp h0
    subst hν0
    by_cases hW : Nonempty W
    · rw [siteProduct_zero_of_nonempty W, Measure.map_zero]
      by_cases hV : Nonempty V
      · rw [siteProduct_zero_of_nonempty V, smul_zero]
      · rw [not_nonempty_iff] at hV
        have hcard : 0 < Fintype.card W := Fintype.card_pos_iff.mpr hW
        have hk : Fintype.card W - Fintype.card V ≠ 0 := by
          have := hV
          have : Fintype.card V = 0 := Fintype.card_eq_zero
          omega
        rw [h0, zero_pow hk, zero_smul]
    · rw [not_nonempty_iff] at hW
      have := hW
      have hV : IsEmpty V := ⟨fun v => hW.false (ι v)⟩
      rw [siteProduct, siteProduct, Measure.pi_of_empty _ (isEmptyElim : W → ℝ),
        Measure.pi_of_empty _ (isEmptyElim : V → ℝ), Measure.map_dirac' hmeas]
      simp [Subsingleton.elim ((isEmptyElim : W → ℝ) ∘ ι) (isEmptyElim : V → ℝ)]
  set c : ENNReal := ν univ with hc
  have hc0 : c ≠ 0 := h0
  have hct : c ≠ ⊤ := measure_ne_top ν univ
  set k := Fintype.card W - Fintype.card V with hk
  have key : siteProduct ν V =
      (c ^ k)⁻¹ • (siteProduct ν W).map (fun θ : W → ℝ => θ ∘ ι) := by
    unfold siteProduct
    refine Measure.pi_eq fun s hs => ?_
    rw [Measure.smul_apply, Measure.map_apply hmeas (MeasurableSet.univ_pi hs)]
    have hpre : (fun θ : W → ℝ => θ ∘ ι) ⁻¹' (Set.univ.pi s) =
        Set.univ.pi (Function.extend ι s (fun _ => Set.univ)) := by
      ext θ
      simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Function.comp_apply]
      constructor
      · intro h w
        by_cases hw : ∃ i, ι i = w
        · obtain ⟨i, rfl⟩ := hw
          rw [hι.extend_apply]
          exact h i
        · rw [Function.extend_apply' _ _ _ hw]
          exact Set.mem_univ _
      · intro h i
        have := h (ι i)
        rwa [hι.extend_apply] at this
    rw [hpre, Measure.pi_pi]
    have hsplit := Finset.prod_mul_prod_compl (Finset.univ.image ι)
      (fun w => ν (Function.extend ι s (fun _ => Set.univ) w))
    rw [← hsplit, Finset.prod_image (fun a _ b _ h => hι h)]
    have h1 : ∏ i : V, ν (Function.extend ι s (fun _ => Set.univ) (ι i))
        = ∏ i : V, ν (s i) := by
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [hι.extend_apply]
    have h2 : ∏ w ∈ (Finset.univ.image ι)ᶜ,
        ν (Function.extend ι s (fun _ => Set.univ) w) = c ^ k := by
      have : ∀ w ∈ (Finset.univ.image ι)ᶜ,
          ν (Function.extend ι s (fun _ => Set.univ) w) = c := by
        intro w hw
        have hw' : ¬ ∃ i, ι i = w := by
          simpa using hw
        rw [Function.extend_apply' _ _ _ hw']
      rw [Finset.prod_congr rfl this, Finset.prod_const, Finset.card_compl,
        Finset.card_image_of_injective _ hι, Finset.card_univ]
    rw [h1, h2]
    simp only [smul_eq_mul]
    rw [mul_comm _ (c ^ k), ← mul_assoc, ENNReal.inv_mul_cancel (pow_ne_zero _ hc0)
      (ENNReal.pow_ne_top hct), one_mul]
  rw [key, smul_smul, ENNReal.mul_inv_cancel (pow_ne_zero _ hc0) (ENNReal.pow_ne_top hct), one_smul]

theorem integral_comp_siteProduct {ν : Measure ℝ} [IsFiniteMeasure ν] {V W : Type*} [Fintype V]
    [Fintype W] {ι : V → W} (hι : Function.Injective ι) {f : (V → ℝ) → ℝ}
    (hf : AEStronglyMeasurable f (siteProduct ν V)) :
    ∫ θ : W → ℝ, f (θ ∘ ι) ∂siteProduct ν W =
      (ν univ).toReal ^ (Fintype.card W - Fintype.card V) * ∫ θ : V → ℝ, f θ ∂siteProduct ν V := by
  have hmeas : Measurable (fun θ : W → ℝ => θ ∘ ι) := by fun_prop
  rw [← integral_map hmeas.aemeasurable (f := f)]
  · rw [map_comp_siteProduct hι, integral_smul_measure, ENNReal.toReal_pow, smul_eq_mul]
  · rw [map_comp_siteProduct hι]
    exact hf.smul_measure _

/-- Character integrals against a product measure factor over the sites. -/
theorem integral_character_siteProduct {ν : Measure ℝ} [IsFiniteMeasure ν] {lam : ℤ → ℝ}
    (hν : HasRealFourier ν lam) {V : Type*} [Fintype V] (m : Frequency V) :
    ∫ θ, character m θ ∂siteProduct ν V = ((∏ x, lam (m x) : ℝ) : ℂ) := by
  unfold character siteProduct
  rw [integral_fintype_prod_eq_prod (f := fun x (t : ℝ) =>
    Complex.exp (Complex.I * (m x : ℂ) * (t : ℂ)))]
  rw [Complex.ofReal_prod]
  exact Finset.prod_congr rfl fun x _ => hν (m x)

end FroehlichSpencer.BKT.Ginibre

end
