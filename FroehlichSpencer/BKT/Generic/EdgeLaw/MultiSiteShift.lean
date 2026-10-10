/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.EdgeLaw.Shear
public import FroehlichSpencer.BKT.Rotator.Contour.LineShift
public import FroehlichSpencer.BKT.Rotator.Contour.Split

/-!
# The multi-site contour shift on `ℝ^V` (generic core)

Here the whole translation is done along
the single complex direction of `a`:

`integral_add_mul_I_eq`: let `a(j₀) ≠ 0` and `â = a / a(j₀)`.

If `z ↦ F(φ + z â)` is holomorphic on
the strip `|Im z| ≤ |a(j₀)|` for every real `φ`, with an integrable majorant `B_φ(Re z)` vanishing at
infinity, and both the real and the translated integrands are integrable, then
`∫ F(φ) dφ = ∫ F(φ + i a) dφ`.

Proof.

The shear `S φ = φ + φ(j₀)(â − δ_{j₀})` preserves Lebesgue measure (`Generic/EdgeLaw/Shear.lean`)
and maps the glued field `(ψ, x)` (value `x` at `j₀`) to `(ψ, 0) + x â`.

After `S` and Fubini at
`j₀` (`Rotator.Contour.integral_eq_integral_integral_glue`) both sides become iterated integrals of
`g_ψ(x)` and `g_ψ(x + i a(j₀))`, `g_ψ(z) = F((ψ, 0) + z â)`, and the one-variable contour shift
`Rotator.Contour.integral_eq_integral_add_mul_I` identifies them.

Along the deformation every edge
increment of the imaginary part is `Im z · ∇â(e)`, bounded by `|∇a(e)|`.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic

open MeasureTheory Complex Filter Topology
open FroehlichSpencer.BKT.Rotator.Contour (glue glue_self glue_of_ne
  integral_eq_integral_integral_glue integral_eq_integral_add_mul_I)

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
/-- The shear by `â − δ_{j₀}` maps the glued field `(ψ, x)` to `(ψ, 0) + x â` when `â(j₀) = 1`. -/
lemma shear_glue {j₀ : V} {â : V → ℝ} (hâ : â j₀ = 1) (ψ : {j // j ≠ j₀} → ℝ) (x : ℝ) :
    shear j₀ (â - Pi.single j₀ 1) (glue j₀ ψ x) = fun j => glue j₀ ψ 0 j + x * â j := by
  funext j
  rw [shear_apply_apply, glue_self]
  by_cases h : j = j₀
  · subst h
    simp [glue_self, hâ]
  · simp [glue_of_ne _ _ h, h]

/-- **The multi-site contour shift.** For `a(j₀) ≠ 0` and `â = a / a(j₀)`: if
`z ↦ F(φ + z â)` is holomorphic on `|Im z| ≤ |a(j₀)|` with an integrable majorant in `Re z` that
vanishes at infinity, for every real `φ`, and the real and translated integrands are integrable,
then `∫ F(φ) dφ = ∫ F(φ + i a) dφ`. -/
theorem integral_add_mul_I_eq (F : (V → ℂ) → ℂ) (a : V → ℝ) (j₀ : V) (hj₀ : a j₀ ≠ 0)
    (hdiff : ∀ (φ : V → ℝ) (z : ℂ), |z.im| ≤ |a j₀| →
      DifferentiableAt ℂ (fun z : ℂ => F fun j => (φ j : ℂ) + z * ((a j / a j₀ : ℝ) : ℂ)) z)
    (hdom : ∀ φ : V → ℝ, ∃ B : ℝ → ℝ, Integrable B ∧ Tendsto B (cocompact ℝ) (𝓝 0) ∧
      ∀ x y : ℝ, |y| ≤ |a j₀| →
        ‖F fun j => (φ j : ℂ) + ((x : ℂ) + y * I) * ((a j / a j₀ : ℝ) : ℂ)‖ ≤ B x)
    (hint₀ : Integrable fun φ : V → ℝ => F fun j => (φ j : ℂ))
    (hint₁ : Integrable fun φ : V → ℝ => F fun j => (φ j : ℂ) + (a j : ℂ) * I) :
    ∫ φ : V → ℝ, F (fun j => (φ j : ℂ)) =
      ∫ φ : V → ℝ, F (fun j => (φ j : ℂ) + (a j : ℂ) * I) := by
  set â : V → ℝ := fun j => a j / a j₀ with hâ_def
  have hâ : â j₀ = 1 := div_self hj₀
  have hu : (â - Pi.single j₀ (1 : ℝ) : V → ℝ) j₀ = 0 := by
    rw [Pi.sub_apply, Pi.single_eq_same, hâ, sub_self]
  set S := shear j₀ (â - Pi.single j₀ 1)
  set g : ({j // j ≠ j₀} → ℝ) → ℂ → ℂ := fun ψ z =>
    F fun j => (glue j₀ ψ 0 j : ℂ) + z * (â j : ℂ) with hg
  have h0 : ∀ ψ (x : ℝ), (fun φ : V → ℝ => F fun j => (φ j : ℂ)) (S (glue j₀ ψ x)) = g ψ x := by
    intro ψ x
    simp only [S, shear_glue hâ ψ x, hg]
    congr 1
    funext j
    push_cast
    ring
  have h1 : ∀ ψ (x : ℝ),
      (fun φ : V → ℝ => F fun j => (φ j : ℂ) + (a j : ℂ) * I) (S (glue j₀ ψ x)) =
        g ψ ((x : ℂ) + (a j₀ : ℂ) * I) := by
    intro ψ x
    simp only [S, shear_glue hâ ψ x, hg]
    congr 1
    funext j
    have hj₀' : (a j₀ : ℂ) ≠ 0 := by exact_mod_cast hj₀
    have haj : (a j : ℂ) = (a j₀ : ℂ) * (â j : ℂ) := by
      simp only [hâ_def]
      push_cast
      rw [mul_div_assoc', mul_comm, mul_div_assoc, div_self hj₀', mul_one]
    rw [haj]
    push_cast
    ring
  have hS₀ := integral_comp_shear hu (fun φ : V → ℝ => F fun j => (φ j : ℂ))
  have hS₁ := integral_comp_shear hu (fun φ : V → ℝ => F fun j => (φ j : ℂ) + (a j : ℂ) * I)
  have hi₀ : Integrable fun φ => (fun φ : V → ℝ => F fun j => (φ j : ℂ)) (S φ) :=
    (integrable_comp_shear_iff hu).mpr hint₀
  have hi₁ : Integrable fun φ =>
      (fun φ : V → ℝ => F fun j => (φ j : ℂ) + (a j : ℂ) * I) (S φ) :=
    (integrable_comp_shear_iff hu).mpr hint₁
  rw [← hS₀, ← hS₁, integral_eq_integral_integral_glue j₀ hi₀,
    integral_eq_integral_integral_glue j₀ hi₁]
  congr 1
  funext ψ
  simp only [h0, h1]
  obtain ⟨B, hB, hBlim, hBdom⟩ := hdom (glue j₀ ψ 0)
  exact integral_eq_integral_add_mul_I (fun z hz => hdiff _ z hz) hB hBlim
    (fun x y hy => hBdom x y hy)

end FroehlichSpencer.BKT.Generic

end
