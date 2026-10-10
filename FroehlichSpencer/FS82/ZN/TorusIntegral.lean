/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Group.Integral

/-!
# integrals on a finite product of circles

The §3 model integrates over link angles `θ : E → ℝ/ℤ` with the product of normalized Haar
measures.

This module collects what the proof of (3.38) and (3.49) needs from that measure:

* `pair ρ θ = Σ_e ρ_e θ_e`, the pairing of an integer vector with a configuration, and the circle
  functions `cosC`, `sinC` (`cos 2πx`, `sin 2πx`);
* invariance under translation and under `θ ↦ −θ`;
* `integral_average`: an integral is its own average over a continuous family of translations;
* `integral_cosC_add_zsmul`: a nonzero frequency integrates to zero;
* `integral_shift_link`: the contour shift of one link variable.

If along the variable `θ_x` two
  continuous functions are the restrictions of one entire `1`-periodic function to the real line
  and to the line `ℝ + i a`, they have the same integral.
-/

open MeasureTheory
open scoped BigOperators

@[expose] public section

namespace FroehlichSpencer.FS82.ZN.Torus

noncomputable section

local instance torusIntegral_factOne : Fact (0 < (1 : ℝ)) := ⟨one_pos⟩
local instance torusIntegral_measureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance torusIntegral_isAddHaar : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance torusIntegral_isProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

variable {E : Type*} [Fintype E]

/-! ### The pairing -/

/-- The pairing `Σ_e ρ_e θ_e` of an integer vector with a circle-valued configuration. -/
def pair (ρ : E → ℤ) (θ : E → UnitAddCircle) : UnitAddCircle :=
  ∑ e, ρ e • θ e

theorem pair_add (ρ : E → ℤ) (θ θ' : E → UnitAddCircle) :
    pair ρ (θ + θ') = pair ρ θ + pair ρ θ' := by
  simp [pair, smul_add, Finset.sum_add_distrib]

theorem pair_neg (ρ : E → ℤ) (θ : E → UnitAddCircle) : pair ρ (-θ) = -pair ρ θ := by
  simp [pair]

theorem pair_zsmul_dir (ρ g : E → ℤ) (u : UnitAddCircle) :
    pair ρ (fun e => g e • u) = (∑ e, ρ e * g e) • u := by
  unfold pair
  rw [Finset.sum_smul]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [mul_smul]

theorem pair_single [DecidableEq E] (ρ : E → ℤ) (x : E) (u : UnitAddCircle) :
    pair ρ (Pi.single x u) = ρ x • u := by
  unfold pair
  rw [Finset.sum_eq_single x]
  · simp
  · intro e _ hne
    simp [hne]
  · intro h
    exact absurd (Finset.mem_univ x) h

theorem pair_coe (ρ : E → ℤ) (τ : E → ℝ) :
    pair ρ (fun e => (τ e : UnitAddCircle)) =
      ((∑ e, (ρ e : ℝ) * τ e : ℝ) : UnitAddCircle) := by
  unfold pair
  have h : ∀ e, ρ e • ((τ e : ℝ) : UnitAddCircle) = (((ρ e : ℝ) * τ e : ℝ) : UnitAddCircle) := by
    intro e
    rw [← AddCircle.coe_zsmul, zsmul_eq_mul]
  simp_rw [h]
  exact (map_sum (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ)))
    (fun e => (ρ e : ℝ) * τ e) Finset.univ).symm

theorem continuous_pair (ρ : E → ℤ) : Continuous (pair ρ) := by
  unfold pair
  exact continuous_finsetSum _ fun e _ => (continuous_apply e).zsmul (ρ e)

/-! ### Circle cosine and sine -/

/-- `cos 2πx` as a function on `ℝ/ℤ`. -/
def cosC (z : UnitAddCircle) : ℝ := (fourier (T := (1 : ℝ)) 1 z).re

/-- `sin 2πx` as a function on `ℝ/ℤ`. -/
def sinC (z : UnitAddCircle) : ℝ := (fourier (T := (1 : ℝ)) 1 z).im

theorem fourier_one_coe (x : ℝ) :
    fourier (T := (1 : ℝ)) 1 (x : UnitAddCircle) =
      Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I) := by
  rw [fourier_coe_apply]
  congr 1
  push_cast
  ring

theorem cosC_coe (x : ℝ) : cosC (x : UnitAddCircle) = Real.cos (2 * Real.pi * x) := by
  unfold cosC
  rw [fourier_one_coe, Complex.exp_ofReal_mul_I_re]

theorem sinC_coe (x : ℝ) : sinC (x : UnitAddCircle) = Real.sin (2 * Real.pi * x) := by
  unfold sinC
  rw [fourier_one_coe, Complex.exp_ofReal_mul_I_im]

theorem continuous_cosC : Continuous cosC :=
  Complex.continuous_re.comp (fourier (T := (1 : ℝ)) 1).continuous

theorem continuous_sinC : Continuous sinC :=
  Complex.continuous_im.comp (fourier (T := (1 : ℝ)) 1).continuous

theorem exists_real_lift (z : UnitAddCircle) : ∃ x : ℝ, (x : UnitAddCircle) = z :=
  QuotientAddGroup.mk_surjective z

theorem cosC_neg (z : UnitAddCircle) : cosC (-z) = cosC z := by
  obtain ⟨x, rfl⟩ := exists_real_lift z
  rw [← AddCircle.coe_neg, cosC_coe, cosC_coe, mul_neg, Real.cos_neg]

theorem sinC_neg (z : UnitAddCircle) : sinC (-z) = -sinC z := by
  obtain ⟨x, rfl⟩ := exists_real_lift z
  rw [← AddCircle.coe_neg, sinC_coe, sinC_coe, mul_neg, Real.sin_neg]

theorem cosC_add_half (z : UnitAddCircle) :
    cosC (z + ((1 / 2 : ℝ) : UnitAddCircle)) = -cosC z := by
  obtain ⟨x, rfl⟩ := exists_real_lift z
  rw [← AddCircle.coe_add, cosC_coe, cosC_coe]
  rw [show 2 * Real.pi * (x + 1 / 2) = 2 * Real.pi * x + Real.pi by ring, Real.cos_add_pi]

theorem abs_cosC_le_one (z : UnitAddCircle) : |cosC z| ≤ 1 := by
  obtain ⟨x, rfl⟩ := exists_real_lift z
  rw [cosC_coe]
  exact Real.abs_cos_le_one _

/-! ### Invariance and averaging -/

theorem volume_isNegInvariant : (volume : Measure UnitAddCircle).IsNegInvariant := by
  have : Measure.Regular (volume : Measure UnitAddCircle) := by
    change Measure.Regular (AddCircle.haarAddCircle (T := (1 : ℝ)))
    unfold AddCircle.haarAddCircle
    infer_instance
  infer_instance

theorem integral_translate {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : (E → UnitAddCircle) → F) (τ : E → UnitAddCircle) :
    ∫ θ, f (θ + τ) = ∫ θ, f θ :=
  integral_add_right_eq_self f τ

theorem integral_neg_config {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : (E → UnitAddCircle) → F) : ∫ θ, f (-θ) = ∫ θ, f θ := by
  have := volume_isNegInvariant
  exact integral_neg_eq_self f volume

theorem integrable_of_continuous {F : Type*} [NormedAddCommGroup F]
    (f : (E → UnitAddCircle) → F) (hf : Continuous f) : Integrable f :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

/-- An integral over the configurations is its own average over a continuous family of
translations. -/
theorem integral_average {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (f : (E → UnitAddCircle) → F) (hf : Continuous f)
    (D : UnitAddCircle → (E → UnitAddCircle)) (hD : Continuous D) :
    ∫ θ, f θ = ∫ θ, ∫ u, f (θ + D u) := by
  have hc : Continuous (Function.uncurry
      fun (θ : E → UnitAddCircle) (u : UnitAddCircle) => f (θ + D u)) :=
    hf.comp (continuous_fst.add (hD.comp continuous_snd))
  have hint : Integrable (Function.uncurry
      fun (θ : E → UnitAddCircle) (u : UnitAddCircle) => f (θ + D u))
      (volume.prod volume) :=
    hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [integral_integral_swap hint]
  have h : ∀ u : UnitAddCircle, ∫ θ, f (θ + D u) = ∫ θ, f θ :=
    fun u => integral_translate f (D u)
  simp_rw [h]
  simp

/-- A nonzero frequency integrates to zero. -/
theorem integral_cosC_add_zsmul (z : UnitAddCircle) {n : ℤ} (hn : n ≠ 0) :
    ∫ u : UnitAddCircle, cosC (z + n • u) = 0 := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  apply integral_eq_zero_of_add_right_eq_neg (g := ((1 / 2 / (n : ℝ) : ℝ) : UnitAddCircle))
  intro u
  have hhalf : n • ((1 / 2 / (n : ℝ) : ℝ) : UnitAddCircle) = ((1 / 2 : ℝ) : UnitAddCircle) := by
    rw [← AddCircle.coe_zsmul, zsmul_eq_mul]
    congr 1
    field_simp
  rw [smul_add, hhalf, ← add_assoc, cosC_add_half]

/-! ### The contour shift of one variable -/

/-- Cauchy's theorem for an entire `1`-periodic function: the integral over a period does not
change under a vertical shift of the contour. -/
theorem periodic_integral_vertical_shift_one (G : ℂ → ℂ) (a : ℝ)
    (hG : Differentiable ℂ G) (hper : ∀ w, G (w + 1) = G w) :
    (∫ x : ℝ in (0 : ℝ)..1, G (x : ℂ)) =
      ∫ x : ℝ in (0 : ℝ)..1, G ((x : ℂ) + a * Complex.I) := by
  have hrect := Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn
    G (0 : ℂ) ((1 : ℂ) + a * Complex.I)
    hG.continuous.continuousOn (fun z _ => (hG z).differentiableWithinAt)
  have hside : (∫ y : ℝ in (0 : ℝ)..a, G ((1 : ℂ) + y * Complex.I)) =
      ∫ y : ℝ in (0 : ℝ)..a, G ((0 : ℂ) + y * Complex.I) := by
    apply intervalIntegral.integral_congr
    intro y _
    have h := hper ((0 : ℂ) + y * Complex.I)
    convert h using 1
    ring_nf
  have hrect' :
      (∫ x : ℝ in (0 : ℝ)..1, G (x + (0 : ℝ) * Complex.I)) -
        (∫ x : ℝ in (0 : ℝ)..1, G (x + a * Complex.I)) +
        Complex.I • (∫ y : ℝ in (0 : ℝ)..a, G ((1 : ℂ) + y * Complex.I)) -
        Complex.I • (∫ y : ℝ in (0 : ℝ)..a, G ((0 : ℂ) + y * Complex.I)) = 0 := by
    simpa using hrect
  have heq : (∫ x : ℝ in (0 : ℝ)..1, G (x + (0 : ℝ) * Complex.I)) -
      (∫ x : ℝ in (0 : ℝ)..1, G (x + a * Complex.I)) = 0 := by
    rw [hside] at hrect'
    simpa using hrect'
  simpa using sub_eq_zero.mp heq

theorem integral_circle_eq_intervalIntegral (g : UnitAddCircle → ℂ) :
    ∫ u, g u = ∫ x : ℝ in (0 : ℝ)..1, g (x : UnitAddCircle) := by
  have hvol : (AddCircle.measureSpace (T := (1 : ℝ))).volume =
      (volume : Measure UnitAddCircle) := by
    calc
      _ = AddCircle.haarAddCircle := by
        simpa using (AddCircle.volume_eq_smul_haarAddCircle (T := (1 : ℝ)))
      _ = _ := rfl
  have h := UnitAddCircle.intervalIntegral_preimage (0 : ℝ) g
  rw [zero_add] at h
  rw [h, hvol]

/-- If `g` and `g'` are the restrictions of an entire `1`-periodic function to `ℝ` and to
`ℝ + i a`, they have the same integral over the circle. -/
theorem circle_integral_vertical_shift (g g' : UnitAddCircle → ℂ) (G : ℂ → ℂ) (a : ℝ)
    (hG : Differentiable ℂ G) (hper : ∀ w, G (w + 1) = G w)
    (hg : ∀ x : ℝ, g (x : UnitAddCircle) = G (x : ℂ))
    (hg' : ∀ x : ℝ, g' (x : UnitAddCircle) = G ((x : ℂ) + a * Complex.I)) :
    ∫ u, g u = ∫ u, g' u := by
  rw [integral_circle_eq_intervalIntegral, integral_circle_eq_intervalIntegral]
  simp_rw [hg, hg']
  exact periodic_integral_vertical_shift_one G a hG hper

/-- **The contour shift of one link variable.** -/
theorem integral_shift_link [DecidableEq E] (Ψ Ψ' : (E → UnitAddCircle) → ℂ)
    (hΨ : Continuous Ψ) (hΨ' : Continuous Ψ') (x : E) (a : ℝ)
    (h : ∀ θ : E → UnitAddCircle, ∃ G : ℂ → ℂ, Differentiable ℂ G ∧ (∀ w, G (w + 1) = G w) ∧
      (∀ u : ℝ, Ψ (θ + Pi.single x (u : UnitAddCircle)) = G (u : ℂ)) ∧
      (∀ u : ℝ, Ψ' (θ + Pi.single x (u : UnitAddCircle)) = G ((u : ℂ) + a * Complex.I))) :
    ∫ θ, Ψ θ = ∫ θ, Ψ' θ := by
  have hD : Continuous (fun u : UnitAddCircle => (Pi.single x u : E → UnitAddCircle)) :=
    @continuous_single E (fun _ => UnitAddCircle) _ _ _ x
  rw [integral_average Ψ hΨ _ hD, integral_average Ψ' hΨ' _ hD]
  congr 1
  funext θ
  obtain ⟨G, hG, hper, h1, h2⟩ := h θ
  exact circle_integral_vertical_shift _ _ G a hG hper h1 h2

end

end FroehlichSpencer.FS82.ZN.Torus

end
