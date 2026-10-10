/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Clock.Disorder.AuxiliarySeamProfile
public import FroehlichSpencer.BKT.Clock.Disorder.Insertion
public import FroehlichSpencer.BKT.Clock.Disorder.CompactShift
public import FroehlichSpencer.BKT.Clock.VillainClock.DisorderCarrier
import Mathlib.Tactic

/-!
# Seam insertion as a shifted compact clock density

The compact field is `φ = N θ`, so the angle twist `2πξ` from (1.32) is the bond shift
`2πNξ` in the numerator of `cos(∇φ/N)`. The source seam is oriented opposite to the positive
vertical graph edge, hence the sign `-2πNξ` below. This theorem identifies the disorder insertion
times the free clock density with the compact bond product having that seam twist. It is the exact
finite-volume bridge used with `exists_auxiliarySeamProfile` and the free-square charge layer.
-/

@[expose] public section

noncomputable section

open FroehlichSpencer.BKT.Rotator
open FroehlichSpencer.BKT.Clock.Compact
open FroehlichSpencer.BKT.Clock.Periodic
open FroehlichSpencer.BKT.Clock.VillainClock

namespace FroehlichSpencer.BKT.Clock.Disorder

/-- The seam twist on the rescaled compact field `φ = N θ`. -/
def clockDisorderSeamTwist {r L : ℕ} (hL : 0 < L) (hr : r ≤ L) (N : ℕ) (ξ : ℝ) :
    RotatorInternalBond (2 * L) → ℝ := fun e =>
  if e ∈ freeSquareDisorderEdgeSet hL hr then -2 * Real.pi * (N : ℝ) * ξ else 0

/-- Multiplying the compact free clock density by the seam insertion is exactly a twisted bond
product. The factor `N` in the twist converts the original angle shift to the `φ = N θ` carrier;
the negative sign comes from the positive vertical graph orientation versus the source's
upper-minus-lower seam orientation. -/
theorem clockDensity_mul_clockDisorderField_eq_twistedBondProduct {r L : ℕ} (N : ℕ)
    (β ξ : ℝ) (hN : 0 < N) (hL : 0 < L) (hr : r ≤ L)
    (φ : RotatorSpinSite (2 * L) → ℝ) :
    clockDensity β N (rotatorFreeGraph (2 * L)) φ *
      clockDisorderField N β ξ φ hL hr =
      compactClockBondProduct (rotatorFreeGraph (2 * L)) β N φ
        (clockDisorderSeamTwist hL hr N ξ) := by
  classical
  let S := freeSquareDisorderEdgeSet hL hr
  let B : RotatorInternalBond (2 * L) → ℝ := fun e =>
    Real.exp (β * Real.cos ((rotatorFreeGraph (2 * L)).grad φ e / N))
  let Q : RotatorInternalBond (2 * L) → ℝ := fun e =>
    Real.exp (β * Real.cos (((rotatorFreeGraph (2 * L)).grad φ e -
      2 * Real.pi * (N : ℝ) * ξ) / N)) / B e
  have hInsertion : clockDisorderField N β ξ φ hL hr = ∏ e ∈ S, Q e := by
    unfold clockDisorderField
    change (∏ i : Fin r, _) =
      ∏ e ∈ Finset.univ.image (disorderSeamEdge hL hr), Q e
    rw [Finset.prod_image (disorderSeamEdge_injective hL hr).injOn]
    refine Finset.prod_congr rfl fun i hi => ?_
    let d := φ (disorderSeamUpper hL hr i) - φ (disorderSeamLower hL hr i)
    have hgrad : (rotatorFreeGraph (2 * L)).grad φ (disorderSeamEdge hL hr i) = -d := by
      simp [Multigraph.grad, d]
    have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    change Real.exp (β * (Real.cos (d / N + 2 * Real.pi * ξ) - Real.cos (d / N))) =
      Real.exp (β * Real.cos (((rotatorFreeGraph (2 * L)).grad φ
        (disorderSeamEdge hL hr i) - 2 * Real.pi * (N : ℝ) * ξ) / N)) /
        Real.exp (β * Real.cos ((rotatorFreeGraph (2 * L)).grad φ
          (disorderSeamEdge hL hr i) / N))
    rw [hgrad, ← Real.exp_sub]
    congr 1
    have hnum : (-d - 2 * Real.pi * (N : ℝ) * ξ) / N =
        -(d / N + 2 * Real.pi * ξ) := by
      field_simp [hN0]
      ring
    rw [hnum, Real.cos_neg]
    have hden : -d / N = -(d / N) := by ring
    rw [hden, Real.cos_neg]
    ring
  have hInsertionAll : clockDisorderField N β ξ φ hL hr =
      ∏ e, if e ∈ S then Q e else 1 := by
    rw [Finset.prod_ite_mem_eq]
    exact hInsertion
  let T : RotatorInternalBond (2 * L) → ℝ := fun e =>
    Real.exp (β * Real.cos (((rotatorFreeGraph (2 * L)).grad φ e -
      2 * Real.pi * (N : ℝ) * ξ) / N))
  have hFactor : ∀ e, B e * (if e ∈ S then Q e else 1) =
      if e ∈ S then T e else B e := by
    intro e
    by_cases hs : e ∈ S
    · simp only [ite_eq_left hs]
      dsimp [Q, T, B]
      field_simp [Real.exp_ne_zero]
    · simp only [ite_eq_right hs, mul_one]
  unfold clockDensity
  rw [hInsertionAll, ← Finset.prod_mul_distrib]
  calc
    (∏ e, B e * (if e ∈ S then Q e else 1)) =
        ∏ e, if e ∈ S then T e else B e := by
      apply Finset.prod_congr rfl
      intro e he
      exact hFactor e
    _ = compactClockBondProduct (rotatorFreeGraph (2 * L)) β N φ
        (clockDisorderSeamTwist hL hr N ξ) := by
      unfold compactClockBondProduct clockDisorderSeamTwist
      change (∏ e, if e ∈ S then T e else B e) =
        ∏ e, Real.exp (β * Real.cos (((rotatorFreeGraph (2 * L)).grad φ e +
          (if e ∈ S then -2 * Real.pi * (N : ℝ) * ξ else 0)) / N))
      apply Finset.prod_congr rfl
      intro e he
      by_cases hs : e ∈ S
      · simp only [ite_eq_left hs]
        dsimp [T]
        have harg : ((rotatorFreeGraph (2 * L)).grad φ e -
            2 * Real.pi * (N : ℝ) * ξ) / N =
          ((rotatorFreeGraph (2 * L)).grad φ e + -2 * Real.pi * (N : ℝ) * ξ) / N := by ring
        rw [harg]
      · simp only [ite_eq_right hs]
        dsimp [B]
        have harg : ((rotatorFreeGraph (2 * L)).grad φ e / N) =
            ((rotatorFreeGraph (2 * L)).grad φ e + 0) / N := by ring
        rw [harg]

/-- The seam indicator used by the auxiliary dual-current profile is exactly the marked-edge
indicator of the finite clock insertion. -/
theorem clockDisorderSeamTwist_eq_indicator {r L : ℕ} (hL : 0 < L) (hr : r ≤ L)
    (N : ℕ) (ξ : ℝ) (e : RotatorInternalBond (2 * L)) :
    clockDisorderSeamTwist hL hr N ξ e =
      2 * Real.pi * (-(N : ℝ) * ξ) *
        (if ∃ i : Fin r, e = .inr
          (FroehlichSpencer.BKT.Duality.verticalDualEdgeData
            ⟨L + i.val + 1, by omega⟩ ⟨L, by omega⟩) then (1 : ℤ) else 0 : ℝ) := by
  classical
  have hedge (i : Fin r) : disorderSeamEdge hL hr i = .inr
      (FroehlichSpencer.BKT.Duality.verticalDualEdgeData
        ⟨L + i.val + 1, by omega⟩ ⟨L, by omega⟩) := by
    rfl
  have hmem : e ∈ freeSquareDisorderEdgeSet hL hr ↔
      ∃ i : Fin r, e = .inr
        (FroehlichSpencer.BKT.Duality.verticalDualEdgeData
          ⟨L + i.val + 1, by omega⟩ ⟨L, by omega⟩) := by
    rw [freeSquareDisorderEdgeSet, Finset.mem_image]
    simp only [Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, he⟩
      exact ⟨i, he.symm.trans (hedge i)⟩
    · rintro ⟨i, he⟩
      exact ⟨i, (hedge i).trans he.symm⟩
  unfold clockDisorderSeamTwist
  by_cases h : e ∈ freeSquareDisorderEdgeSet hL hr
  · have hex := hmem.mp h
    simp only [h, ite_true, hex]
    ring
  · have hex : ¬ ∃ i : Fin r, e = .inr
        (FroehlichSpencer.BKT.Duality.verticalDualEdgeData
          ⟨L + i.val + 1, by omega⟩ ⟨L, by omega⟩) := fun he => h (hmem.mpr he)
    simp only [h, ite_false, hex]
    ring

/-- The straight seam twist has a logarithmic-energy decomposition on every buffered centered
free square. The constant is the explicit finite coarse constant from the dual harmonic
field construction; substituting `Nξ` converts that profile to the rescaled compact clock field. -/
theorem exists_clockDisorderSeamProfile {L r : ℕ} (hbuf : 2 * r + 1 ≤ L) (hL : 0 < L)
    (N : ℕ) (ξ : ℝ) :
    ∃ C₀ : ℝ, 0 < C₀ ∧
      ∃ σ : RotatorSpinSite (2 * L) → ℝ,
        ∃ θ : RotatorInternalBond (2 * L) → ℝ,
          (∀ e, clockDisorderSeamTwist (r := r) hL (show r ≤ L by omega) N ξ e =
            (rotatorFreeGraph (2 * L)).grad σ e + θ e) ∧
          (∑ e, θ e ^ 2) ≤ (N : ℝ) ^ 2 * ξ ^ 2 * C₀ *
            (1 + Real.log (1 + (r : ℝ))) := by
  have hr : r ≤ L := by omega
  obtain ⟨C₀, hC₀, hprofile⟩ := exists_auxiliarySeamProfile hbuf hL
  obtain ⟨σ, θ, hdecomp, henergy⟩ := hprofile (-(N : ℝ) * ξ)
  refine ⟨C₀, hC₀, σ, θ, ?_, ?_⟩
  · intro e
    rw [clockDisorderSeamTwist_eq_indicator hL hr N ξ e]
    exact hdecomp e
  · calc
      (∑ e, θ e ^ 2) ≤ (-(N : ℝ) * ξ) ^ 2 * C₀ *
          (1 + Real.log (1 + (r : ℝ))) := henergy
      _ = (N : ℝ) ^ 2 * ξ ^ 2 * C₀ *
          (1 + Real.log (1 + (r : ℝ))) := by ring

/-- The shifted seam partition integrand on the free square. After the profile decomposition, the
twisted clock density times the original Fejér multiplier equals the residual-offset density at
`φ + σ` times that same multiplier. The compact charge-layer identity can then be applied at the
site shift `-σ` after the torus change of variables. -/
theorem exists_clockDisorderSeamFejerShift {L r : ℕ} (hbuf : 2 * r + 1 ≤ L) (hL : 0 < L)
    (N M : ℕ) (hN : 0 < N) (β ξ : ℝ) :
    ∃ C₀ : ℝ, 0 < C₀ ∧
      ∃ σ : RotatorSpinSite (2 * L) → ℝ,
        ∃ θ : RotatorInternalBond (2 * L) → ℝ,
          (∀ e, clockDisorderSeamTwist (r := r) hL (by omega) N ξ e =
            (rotatorFreeGraph (2 * L)).grad σ e + θ e) ∧
          (∑ e, θ e ^ 2) ≤ (N : ℝ) ^ 2 * ξ ^ 2 * C₀ *
            (1 + Real.log (1 + (r : ℝ))) ∧
          ∀ φ : RotatorSpinSite (2 * L) → ℝ,
            clockDensity β N (rotatorFreeGraph (2 * L)) φ *
                clockDisorderField (r := r) N β ξ φ hL (show r ≤ L by omega) *
                ∏ v, fejerPolynomial M (φ v - clockOffset N) =
              (∏ e, Real.exp (β * Real.cos
                (((rotatorFreeGraph (2 * L)).grad (φ + σ) e + θ e) / N))) *
                ∏ v, fejerPolynomial M (φ v - clockOffset N) := by
  have hr : r ≤ L := by omega
  obtain ⟨C₀, hC₀, σ, θ, hdecomp, henergy⟩ :=
    exists_clockDisorderSeamProfile hbuf hL N ξ
  refine ⟨C₀, hC₀, σ, θ, hdecomp, henergy, ?_⟩
  intro φ
  have hshift := compactClockBondProduct_twist_eq_shiftedOffset
    (rotatorFreeGraph (2 * L)) β N φ σ (clockDisorderSeamTwist (r := r) hL hr N ξ) θ
    hdecomp
  rw [clockDensity_mul_clockDisorderField_eq_twistedBondProduct N β ξ hN hL hr φ]
  rw [hshift]
  unfold compactClockBondProduct
  rfl

end FroehlichSpencer.BKT.Clock.Disorder

end
