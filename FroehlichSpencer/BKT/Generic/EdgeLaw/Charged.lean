/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.EdgeLaw.Normalization
public import FroehlichSpencer.BKT.Generic.EdgeLaw.MultiSiteShift

/-!
# Charged characters vanish under the rooted edge law (generic core)

`integral_character_mul_edgeLaw_eq_zero`: `∫ e^{i⟨φ, τ⟩} g(∇φ) d edgeLaw = 0` for an integer
`τ` with `∑ τ ≠ 0` and every bounded measurable observable `g` of the gradient.

Proof.

The shear `φ ↦ φ + φ(v)(𝟙 − δ_v)` preserves Lebesgue measure and turns the field glued
from `ψ` and the root value `x` into `(ψ, 0) + x 𝟙`.

The density and `g(∇φ)` do not see the
constant `x 𝟙` except through the root window `𝟙_{[-π, π)}(x)`, and the character picks up
`e^{i x ∑ τ}`.

The inner integral is `∫_{-π}^{π} e^{i Q x} dx = 0` for the nonzero integer
`Q = ∑ τ`.

This is the mechanism of KP's `gffLaw` (compare `Coulomb.integral_cos_charge_gffLaw`).
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic

open MeasureTheory Complex
open FroehlichSpencer.BKT.Reduction (gffCharacter)
open FroehlichSpencer.BKT.Rotator.Contour (glue glue_self glue_of_ne
  integral_eq_integral_integral_glue)

/-- `∫ 𝟙_{[-π, π)}(x) e^{iQx} dx = 0` for a nonzero integer `Q`. -/
theorem integral_indicator_mul_exp_eq_zero {Q : ℤ} (hQ : Q ≠ 0) :
    ∫ x : ℝ, (((Set.Ico (-Real.pi) Real.pi).indicator 1 x : ℝ) : ℂ) *
      Complex.exp (I * ((Q : ℂ) * (x : ℂ))) = 0 := by
  have hfun : (fun x : ℝ => (((Set.Ico (-Real.pi) Real.pi).indicator 1 x : ℝ) : ℂ) *
      Complex.exp (I * ((Q : ℂ) * (x : ℂ)))) =
        (Set.Ico (-Real.pi) Real.pi).indicator fun x : ℝ => Complex.exp ((I * Q) * x) := by
    funext x
    by_cases hx : x ∈ Set.Ico (-Real.pi) Real.pi
    · simp only [Set.indicator_of_mem hx, Pi.one_apply, Complex.ofReal_one, one_mul]
      ring_nf
    · simp [Set.indicator_of_notMem hx]
  have hc : I * (Q : ℂ) ≠ 0 := mul_ne_zero I_ne_zero (by exact_mod_cast hQ)
  rw [hfun, integral_indicator measurableSet_Ico, integral_Ico_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos]), integral_exp_mul_complex hc]
  have hper : Complex.exp (I * Q * (Real.pi : ℂ)) = Complex.exp (I * Q * ((-Real.pi : ℝ) : ℂ)) := by
    have h2 : I * Q * (Real.pi : ℂ) = I * Q * ((-Real.pi : ℝ) : ℂ) + (Q : ℂ) * (2 * Real.pi * I) := by
      push_cast; ring
    rw [h2, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  rw [hper, sub_self, zero_div]

variable {V : Type*} [Fintype V] [DecidableEq V] {E : Type*} [Fintype E]

/-- **FS81 (6.3) for integer charges.** Under the rooted edge law a character of nonzero integer
total charge, times any bounded measurable function of the gradient, integrates to zero. -/
theorem integral_character_mul_edgeLaw_eq_zero (G : Multigraph V E)
    (hG : G.toSimpleGraph.Connected) {w : ℂ → ℂ} {W : ℝ} {c : ℝ → ℝ} (hw : IsStripWeight w W c)
    (v : V) (τ : V → ℤ) (hτ : ∑ j, τ j ≠ 0) (g : (E → ℝ) → ℂ) (hg : Measurable g)
    (hbdd : ∃ M : ℝ, ∀ x, ‖g x‖ ≤ M) :
    ∫ φ, gffCharacter (fun j => (τ j : ℝ)) φ * g (G.grad φ) ∂edgeLaw G w v = 0 := by
  obtain ⟨M, hM⟩ := hbdd
  rw [edgeLaw_eq_densityLaw,
    integral_densityLaw (edgeDensity_nonneg G hw v) (measurable_edgeDensity G hw v)]
  suffices h : ∫ φ, ((edgeDensity G w v φ : ℝ) : ℂ) *
      (gffCharacter (fun j => (τ j : ℝ)) φ * g (G.grad φ)) = 0 by
    rw [h, mul_zero]
  set Q : ℤ := ∑ j, τ j with hQ
  set u : V → ℝ := fun j => if j = v then 0 else 1 with hu_def
  have hu : u v = 0 := by simp [hu_def]
  set f : (V → ℝ) → ℂ := fun φ => ((edgeDensity G w v φ : ℝ) : ℂ) *
    (gffCharacter (fun j => (τ j : ℝ)) φ * g (G.grad φ)) with hf
  have hgrad_cont : Continuous fun φ : V → ℝ => G.grad φ := by
    unfold Multigraph.grad; fun_prop
  have hf_int : Integrable f := by
    have hint := (integrable_edgeDensity G hG hw v).ofReal (𝕜 := ℂ)
    refine hint.mul_of_top_left (memLp_top_of_bound ?_ M (Filter.Eventually.of_forall fun φ => ?_))
    · exact ((Reduction.continuous_gffCharacter _).aestronglyMeasurable).mul
        (hg.comp hgrad_cont.measurable).aestronglyMeasurable
    · rw [norm_mul, Reduction.norm_gffCharacter, one_mul]; exact hM _
  -- the shear moves the root value into a global constant
  have hshear : ∀ (ψ : {j // j ≠ v} → ℝ) (x : ℝ),
      shear v u (glue v ψ x) = fun j => glue v ψ 0 j + x := by
    intro ψ x
    funext j
    rw [shear_apply_apply, glue_self]
    by_cases h : j = v
    · subst h; simp [glue_self, hu]
    · simp [glue_of_ne _ _ h, hu_def, h]
  have hpt : ∀ (ψ : {j // j ≠ v} → ℝ) (x : ℝ), f (shear v u (glue v ψ x)) =
      (((∏ e, (w ((G.grad (glue v ψ 0) e : ℝ) : ℂ)).re : ℝ) : ℂ) *
        gffCharacter (fun j => (τ j : ℝ)) (glue v ψ 0) * g (G.grad (glue v ψ 0))) *
      ((((Set.Ico (-Real.pi) Real.pi).indicator 1 x : ℝ) : ℂ) *
        Complex.exp (I * ((Q : ℂ) * (x : ℂ)))) := by
    intro ψ x
    rw [hshear]
    have hgr : G.grad (fun j => glue v ψ 0 j + x) = G.grad (glue v ψ 0) := by
      funext e; simp only [Multigraph.grad]; ring
    have hv : glue v ψ 0 v + x = x := by rw [glue_self, zero_add]
    have hchar : gffCharacter (fun j => (τ j : ℝ)) (fun j => glue v ψ 0 j + x) =
        gffCharacter (fun j => (τ j : ℝ)) (glue v ψ 0) * Complex.exp (I * ((Q : ℂ) * (x : ℂ))) := by
      unfold gffCharacter
      rw [← Complex.exp_add]
      congr 1
      simp only [hQ]
      push_cast
      rw [Finset.sum_mul, ← mul_add, ← Finset.sum_add_distrib]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    simp only [hf, edgeDensity, hgr, hv, hchar]
    push_cast
    ring
  rw [← integral_comp_shear hu f,
    integral_eq_integral_integral_glue v ((integrable_comp_shear_iff hu).mpr hf_int)]
  simp_rw [hpt, integral_const_mul, integral_indicator_mul_exp_eq_zero hτ, mul_zero,
    integral_zero]

end FroehlichSpencer.BKT.Generic

end
