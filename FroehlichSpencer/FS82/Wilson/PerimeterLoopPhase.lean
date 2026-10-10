/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Wilson.PerimeterRelativePhase

/-!
# the sheet-minus-residual identity on every plaquette

For a shift `tau` with `d₁ tau = sigma − eps` on the finite dual complex (FS82 (2.51)), the
curvature of the zero-extended one-form of `tau` is the integer sheet minus the oriented extension
of `eps` on **every** plaquette of the bumped box: on the image of the dual plaquettes this is the
hypothesis, and off the image all three terms vanish, since a plaquette that contains a link of
`Λ*` is a plaquette of `Λ*` (`chainCoboundary_sourcePrimalOneForm_eq_zero`).

This is the hypothesis
`hdecomp` of the relative phase representatives, without any condition on where a filling lies.

* `orientedSheetOnPlaquettes`: the integer sheet in coordinate orientation, extended by zero.
* `loopField_plaquette_decomposition`: the identity.
* `sum_controlledOrientedDualField_sq`: the oriented extension has the `ℓ²` norm of `eps`.
-/

open scoped BigOperators
open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Currents
open FroehlichSpencer.FS82.Currents.ShortPhase
open FroehlichSpencer.FS82.Currents.PlaquetteCarrierPacking
open FroehlichSpencer.FS82.Currents.ShortPhaseAggregate
open FroehlichSpencer.FS82.Currents.ShortComponentPhase
open FroehlichSpencer.FS82.Gaussian
open FroehlichSpencer.FS82.Moment.SourceConstructor

@[expose] public section

namespace FroehlichSpencer.FS82.Wilson

noncomputable section

variable {B : Box 4}

/-- The integer sheet on the plaquettes of the bumped box, in coordinate orientation and extended
by zero off the image of the dual plaquettes. -/
def orientedSheetOnPlaquettes (sheet : SourceDualTwoCells B → ℤ) (p : SourcePlaquette B) : ℤ := by
  classical
  exact if hp : sourcePlaquetteInDualImage p then
    sourceDualSigma (sourcePlaquetteDualPreimage p hp) * sheet (sourcePlaquetteDualPreimage p hp)
  else 0

theorem orientedSheetOnPlaquettes_apply (sheet : SourceDualTwoCells B → ℤ)
    (q : SourceDualTwoCells B) :
    orientedSheetOnPlaquettes sheet (sourceDualTwoPlaquette q) = sourceDualSigma q * sheet q := by
  have hp := sourceDualTwoPlaquette_interior q
  have hpre : sourcePlaquetteDualPreimage (sourceDualTwoPlaquette q) hp = q := by
    apply sourceDualTwoPlaquette_injective
    exact Classical.choose_spec
      (sourcePlaquetteInDualImage_iff_exists (sourceDualTwoPlaquette q) |>.mp hp)
  simp [orientedSheetOnPlaquettes, hp, hpre]

/-- **Sheet minus residual on every plaquette** (FS82 (2.51) in coordinate orientation). -/
theorem loopField_plaquette_decomposition
    (tau : EuclideanSpace ℝ (SourceDualOneCells B))
    (sigma eps : EuclideanSpace ℝ (SourceDualTwoCells B))
    (sheet : SourceDualTwoCells B → ℤ)
    (hsigma : ∀ q, (sheet q : ℝ) = sigma q)
    (hshift : (sourceLatticeComplex (B := B)).d₁ tau = sigma - eps) :
    ∀ p : SourcePlaquette B,
      controlledOrientedDualFieldOnPlaquettes eps p +
        chainCoboundary (sourcePrimalOneForm tau) p.1 =
          (orientedSheetOnPlaquettes sheet p : ℝ) := by
  classical
  intro p
  by_cases hp : sourcePlaquetteInDualImage p
  · obtain ⟨q, rfl⟩ := (sourcePlaquetteInDualImage_iff_exists p).mp hp
    have hcurl : chainCoboundary (sourcePrimalOneForm tau) (sourceDualTwoPlaquette q).1 =
        dualCellOrientationSign q.1 * ((sourceLatticeComplex (B := B)).d₁ tau q) :=
      chainCoboundary_sourcePrimalOneForm_signed tau q
    have hpoint : (sourceLatticeComplex (B := B)).d₁ tau q = sigma q - eps q := by
      have h := congrArg (fun y : EuclideanSpace ℝ (SourceDualTwoCells B) => y.ofLp q) hshift
      simpa using h
    rw [controlledOrientedDualFieldOnPlaquettes_apply, hcurl, orientedSheetOnPlaquettes_apply,
      Int.cast_mul, sourceDualSigma_cast_eq_orientationSign, hsigma, hpoint]
    ring
  · rw [chainCoboundary_sourcePrimalOneForm_eq_zero tau p hp]
    simp [controlledOrientedDualFieldOnPlaquettes, orientedSheetOnPlaquettes, hp]

/-- The oriented extension of a dual two-form to the plaquettes has the same `ℓ²` norm. -/
theorem sum_controlledOrientedDualField_sq (f : SourceDualTwoCells B → ℝ) :
    (∑ p : SourcePlaquette B, (controlledOrientedDualFieldOnPlaquettes f p) ^ 2) =
      ∑ q : SourceDualTwoCells B, (f q) ^ 2 := by
  classical
  have hfield : ∀ p : SourcePlaquette B, controlledOrientedDualFieldOnPlaquettes f p =
      sourceDualFieldOnPlaquettes (fun q => dualCellOrientationSign q.1 * f q) p := by
    intro p
    unfold controlledOrientedDualFieldOnPlaquettes sourceDualFieldOnPlaquettes
    rfl
  simp_rw [hfield]
  rw [sourceDualFieldOnPlaquettes_energy]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [mul_pow, dualCellOrientationSign_two_sq, one_mul]

end

end FroehlichSpencer.FS82.Wilson

end
