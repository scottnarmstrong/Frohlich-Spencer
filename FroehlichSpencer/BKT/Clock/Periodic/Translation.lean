/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Clock.Periodic.Contour
public import FroehlichSpencer.BKT.Clock.Periodic.Law
public import FroehlichSpencer.BKT.Generic.EdgeRatio
public import FroehlichSpencer.BKT.Reduction.SpinWaveTranslation
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Complex translation for the compact-angle clock law

This module gives a product-contour shift on a finite compact angle box. Its charge hypothesis is
the exact character-period condition: each site frequency times the period is an integer multiple
of `2π`. For the clock parameterization `φ = n θ`, this is `n * τ(j) ∈ ℤ` site by site. Neutrality
alone does not make a character periodic on the compact box.

Source: FS81 §7.1, (7.9); contour shifts use cancellation of periodic side integrals.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Clock.Periodic

open MeasureTheory Complex
open FroehlichSpencer.BKT.Reduction (gffCharacter)

/-- A real angle vector with a specified imaginary displacement. -/
def complexAngleField {d : ℕ} (φ c : Fin d → ℝ) : Fin d → ℂ :=
  fun j => (φ j : ℂ) + (c j : ℂ) * Complex.I

/-- The compact-box integral of a holomorphic function at the field displaced by `i c`. -/
def compactAngleIntegral {d : ℕ} (P : ℝ) (F : (Fin d → ℂ) → ℂ) (c : Fin d → ℝ) : ℂ :=
  ∫ φ, F (complexAngleField φ c) ∂compactAngleBaseMeasure P

/-- Integrating a holomorphic function over a compact periodic box is invariant under a vertical
shift of one site coordinate. The proof uses Fubini and the one-dimensional contour identity, with
periodicity cancelling the rectangle's vertical sides. -/
theorem compactAngleIntegral_shiftCoordinate {d : ℕ} {P t : ℝ} (hP : 0 < P)
    (F : (Fin d → ℂ) → ℂ) (hF : Differentiable ℂ F)
    (hperiodic : ∀ j z, F (Function.update z j (z j + (P : ℂ))) = F z)
    (c : Fin d → ℝ) (j : Fin d)
    (hint : ∀ c : Fin d → ℝ,
      Integrable (fun φ => F (complexAngleField φ c)) (compactAngleBaseMeasure P)) :
    compactAngleIntegral P F c =
      compactAngleIntegral P F (Function.update c j (c j + t)) := by
  cases d with
  | zero => exact Fin.elim0 j
  | succ m =>
    let μ : Fin (m + 1) → Measure ℝ := fun _ =>
      volume.restrict (Set.Ioc (-P / 2) (P / 2))
    let e : ℝ × (Fin m → ℝ) ≃ᵐ (Fin (m + 1) → ℝ) :=
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) j).symm
    have hmp : MeasurePreserving e
        ((μ j).prod (Measure.pi fun k => μ (j.succAbove k))) (Measure.pi μ) := by
      exact (measurePreserving_piFinSuccAbove μ j).symm
    have hleftInt : Integrable (fun φ : Fin (m + 1) → ℝ =>
        F (complexAngleField φ c)) (Measure.pi μ) := by
      simpa [compactAngleBaseMeasure, μ] using hint c
    have hrightInt : Integrable (fun φ : Fin (m + 1) → ℝ =>
        F (complexAngleField φ (Function.update c j (c j + t)))) (Measure.pi μ) := by
      simpa [compactAngleBaseMeasure, μ] using hint (Function.update c j (c j + t))
    have hprodLeft : Integrable
        (fun p : ℝ × (Fin m → ℝ) => F (complexAngleField (e p) c))
        ((μ j).prod (Measure.pi fun k => μ (j.succAbove k))) :=
      (hmp.integrable_comp (hleftInt.aestronglyMeasurable)).mpr hleftInt
    have hprodRight : Integrable
        (fun p : ℝ × (Fin m → ℝ) =>
          F (complexAngleField (e p) (Function.update c j (c j + t))))
        ((μ j).prod (Measure.pi fun k => μ (j.succAbove k))) :=
      (hmp.integrable_comp (hrightInt.aestronglyMeasurable)).mpr hrightInt
    have hL := hmp.integral_comp' (fun φ => F (complexAngleField φ c))
    have hR := hmp.integral_comp'
      (fun φ => F (complexAngleField φ (Function.update c j (c j + t))))
    have hL' : compactAngleIntegral P F c =
        ∫ p, F (complexAngleField (e p) c)
          ∂((μ j).prod (Measure.pi fun k => μ (j.succAbove k))) := by
      unfold compactAngleIntegral
      simpa [compactAngleBaseMeasure, μ] using hL.symm
    have hR' : compactAngleIntegral P F (Function.update c j (c j + t)) =
        ∫ p, F (complexAngleField (e p) (Function.update c j (c j + t)))
          ∂((μ j).prod (Measure.pi fun k => μ (j.succAbove k))) := by
      unfold compactAngleIntegral
      simpa [compactAngleBaseMeasure, μ] using hR.symm
    rw [hL', hR', integral_prod_symm _ hprodLeft, integral_prod_symm _ hprodRight]
    apply integral_congr_ae
    filter_upwards with ψ
    let base : Fin (m + 1) → ℂ := complexAngleField (e (0, ψ)) c
    let g : ℂ → ℂ := fun z => F (Function.update base j (z + (c j : ℂ) * Complex.I))
    have hgfield : Differentiable ℂ
        (fun z : ℂ => Function.update base j (z + (c j : ℂ) * Complex.I)) := by
      refine (differentiable_pi (𝕜 := ℂ)
        (Φ := fun z : ℂ => (Function.update base j (z + (c j : ℂ) * Complex.I) :
          Fin (m + 1) → ℂ))).2 fun k => ?_
      by_cases hk : k = j
      · subst k
        simp only [Function.update_self]
        fun_prop
      · simp only [Function.update_of_ne hk]
        fun_prop
    have hg : Differentiable ℂ g := hF.comp hgfield
    have hgperiodic : ∀ z : ℂ, g (z + (P : ℂ)) = g z := by
      intro z
      let z₀ : Fin (m + 1) → ℂ := Function.update base j (z + (c j : ℂ) * Complex.I)
      have hv : Function.update base j (z + (P : ℂ) + (c j : ℂ) * Complex.I) =
          Function.update z₀ j (z₀ j + (P : ℂ)) := by
        funext k
        by_cases hk : k = j
        · subst k
          simp only [z₀, Function.update_self]
          ring
        · simp [z₀, Function.update_of_ne hk]
      calc
        g (z + (P : ℂ)) = F (Function.update base j (z + (P : ℂ) + (c j : ℂ) * Complex.I)) := rfl
        _ = F (Function.update z₀ j (z₀ j + (P : ℂ))) := by rw [hv]
        _ = F z₀ := hperiodic j z₀
        _ = g z := rfl
    have hcoordinates (x : ℝ) : e (x, ψ) = Function.update (e (0, ψ)) j x := by
      funext k
      by_cases hk : k = j
      · subst k
        simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
          Equiv.coe_fn_mk, Fin.insertNth_apply_same]
      · obtain ⟨l, rfl⟩ := Fin.exists_succAbove_eq hk
        simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
          Equiv.coe_fn_mk, Fin.insertNth_apply_succAbove]
    have hleftPoint (x : ℝ) :
        F (complexAngleField (e (x, ψ)) c) = g (x : ℂ) := by
      unfold g
      congr 1
      rw [hcoordinates]
      funext k
      by_cases hk : k = j
      · subst k
        simp [complexAngleField, base]
      · simp [complexAngleField, base, Function.update_of_ne hk]
    have hrightPoint (x : ℝ) :
        F (complexAngleField (e (x, ψ)) (Function.update c j (c j + t))) =
          g ((x : ℂ) + (t : ℂ) * Complex.I) := by
      unfold g
      congr 1
      rw [hcoordinates]
      funext k
      by_cases hk : k = j
      · subst k
        simp only [complexAngleField, Function.update_self]
        push_cast
        ring
      · simp [complexAngleField, Function.update_of_ne hk, base]
    have hinterval := periodic_intervalIntegral_shift (P := P) (t := t) g hg hgperiodic
    have horder : -P / 2 ≤ P / 2 := by linarith
    have hμleft : (∫ x, F (complexAngleField (e (x, ψ)) c) ∂(μ j)) =
        ∫ x in (-P / 2)..(P / 2), g (x : ℂ) := by
      rw [intervalIntegral.integral_of_le horder]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => hleftPoint x
    have hμright :
        (∫ x, F (complexAngleField (e (x, ψ)) (Function.update c j (c j + t))) ∂(μ j)) =
          ∫ x in (-P / 2)..(P / 2), g ((x : ℂ) + (t : ℂ) * Complex.I) := by
      rw [intervalIntegral.integral_of_le horder]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => hrightPoint x
    rw [hμleft, hμright]
    exact hinterval

/-- Simultaneous complex translation on the compact angle box. The coordinate shifts are composed
one at a time, so the only source-specific condition is that the integrand is periodic in each real
coordinate. -/
theorem compactAngleIntegral_complexShift {d : ℕ} {P : ℝ} (hP : 0 < P)
    (F : (Fin d → ℂ) → ℂ) (hF : Differentiable ℂ F)
    (hperiodic : ∀ j z, F (Function.update z j (z j + (P : ℂ))) = F z)
    (a : Fin d → ℝ)
    (hint : ∀ c : Fin d → ℝ,
      Integrable (fun φ => F (complexAngleField φ c)) (compactAngleBaseMeasure P)) :
    compactAngleIntegral P F 0 = compactAngleIntegral P F a := by
  classical
  have hset : ∀ s : Finset (Fin d),
      compactAngleIntegral P F 0 =
        compactAngleIntegral P F (fun j => if j ∈ s then a j else 0) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      have hz : (fun j : Fin d => if j ∈ (∅ : Finset (Fin d)) then a j else 0) = 0 := by
        funext j
        simp
      rw [hz]
    | @insert j s hj ih =>
      let c : Fin d → ℝ := fun k => if k ∈ s then a k else 0
      have hstep := compactAngleIntegral_shiftCoordinate (t := a j) hP F hF hperiodic c j hint
      calc
        compactAngleIntegral P F 0 = compactAngleIntegral P F c := by
          simpa [c] using ih
        _ = compactAngleIntegral P F (Function.update c j (c j + a j)) := hstep
        _ = compactAngleIntegral P F (fun k => if k ∈ insert j s then a k else 0) := by
          congr 1
          funext k
          by_cases hk : k = j
          · subst k
            simp [c, hj]
          · simp [c, hk, hj, Finset.mem_insert]
  simpa using hset Finset.univ

end FroehlichSpencer.BKT.Clock.Periodic

end
