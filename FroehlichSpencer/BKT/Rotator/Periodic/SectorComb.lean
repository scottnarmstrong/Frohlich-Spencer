/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Rotator.Periodic.Comb
public import FroehlichSpencer.BKT.Rotator.Periodic.DualCarrier
public import FroehlichSpencer.BKT.Rotator.BesselInterp.Properties

/-!
# Periodic comb samples and twisted-height sectors

The rootless real coordinates used by Poisson summation are identified with pinned integer heights
on the dual torus. This file records the carrier-level interface needed to read the comb limit as a
winding-sector partition sum.
-/

@[expose] public section

open Complex
open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Lattice2D
open FroehlichSpencer.BKT.Rotator
open FroehlichSpencer.BKT.Rotator.BesselInterp

noncomputable section

namespace FroehlichSpencer.BKT.Rotator.Periodic

variable {L : ℕ} [NeZero L]

/-- Integer rootless coordinates on the square carrier, extended by zero at the chosen root. -/
def rootIntegerField {hS : 1 < L}
    (z : RootedVertex L hS → ℤ) : Site L → ℤ := fun v =>
  if h : v = periodicRootSite hS then 0 else z ⟨v, h⟩

/-- The torus dual carrier sends its chosen root to the square root. -/
theorem torusDualSquareIso_root (hL : 2 < L) (hS : 1 < L) :
    (torusDualSquareIso hL).vertices (0, 0) = periodicRootSite hS := by
  simp [torusDualSquareIso, torusQuarterTurnEquiv, torusQuarterTurn,
    squareTorusVertexEquiv, periodicRootSite]

/-- Reindexing and reversing edges leaves a product of even current weights unchanged. -/
theorem prod_currentPullback_even {V E W F : Type*}
    [Fintype E] [DecidableEq V] [DecidableEq W] [Fintype F]
    {G : Multigraph V E} {H : Multigraph W F}
    (I : Multigraph.Isomorphism G H) (w : ℤ → ℝ) (hw : ∀ n, w (-n) = w n)
    (q : F → ℤ) :
    (∏ e : E, w (currentPullback I q e)) = ∏ f : F, w (q f) := by
  classical
  calc
    (∏ e : E, w (currentPullback I q e)) = ∏ e : E, w (q (I.edges e)) := by
      apply Finset.prod_congr rfl
      intro e he
      by_cases hs : currentSameOrientation I e
      · simp [currentPullback, hs]
      · simp [currentPullback, hs, hw]
    _ = ∏ f : F, w (q f) := Equiv.prod_comp I.edges (fun f => w (q f))

/-- The real sector offset transported to the square-periodic carrier. -/
def periodicSectorOffset (hL : 2 < L) (w : ℤ × ℤ) : Bond L → ℝ :=
  torusDualFieldToSquare hL (fun e => (torusHarmonicCurrent w e : ℝ))

/-- The real field corresponding to an integer torus current on the dual square carrier. -/
def periodicTorusCurrentOffset (hL : 2 < L) (q : TorusEdge L → ℤ) : Bond L → ℝ :=
  torusDualFieldToSquare hL (fun e => (q e : ℝ))

/-- Rootless integer coordinates are equivalent to the pinned integer fields on the torus dual
carrier. -/
def periodicPinnedHeightsEquivRooted (hL : 2 < L) (hS : 1 < L) :
    periodicPinnedHeights L ≃ (RootedVertex L hS → ℤ) where
  toFun h := fun v => h.1 ((torusDualSquareIso hL).vertices.symm v.1)
  invFun z := by
    let H : TorusVertex L → ℤ := fun p => rootIntegerField z ((torusDualSquareIso hL).vertices p)
    have hroot : H (0, 0) = 0 := by
      simp [H, rootIntegerField, torusDualSquareIso_root hL hS]
    exact ⟨H, hroot⟩
  left_inv h := by
    apply Subtype.ext
    funext p
    change rootIntegerField (fun v => h.1 ((torusDualSquareIso hL).vertices.symm v.1))
      ((torusDualSquareIso hL).vertices p) = h.1 p
    by_cases hp : (torusDualSquareIso hL).vertices p = periodicRootSite hS
    · have hp0 : p = (0, 0) := by
        apply (torusDualSquareIso hL).vertices.injective
        rw [hp, torusDualSquareIso_root hL hS]
      rw [hp0, torusDualSquareIso_root hL hS]
      simp only [rootIntegerField]
      exact h.2.symm
    · simp [rootIntegerField, hp]
  right_inv z := by
    funext v
    simp only [Equiv.apply_symm_apply]
    have hv : v.1 ≠ periodicRootSite hS := v.2
    simp [rootIntegerField, hv]

/-- The inverse height field has the prescribed root-zero square coordinates. -/
theorem periodicPinnedHeightsEquivRooted_symm_apply (hL : 2 < L) (hS : 1 < L)
    (z : RootedVertex L hS → ℤ) (p : TorusVertex L) :
    ((periodicPinnedHeightsEquivRooted hL hS).symm z).1 p =
      rootIntegerField z ((torusDualSquareIso hL).vertices p) := rfl

/-- Pushing the real form of a pinned torus height to the square carrier gives the root-zero
coordinate field used by the periodic density. -/
theorem periodicPinnedHeight_pushField_eq_rootField (hL : 2 < L) (hS : 1 < L)
    (z : RootedVertex L hS → ℤ) :
    (torusDualSquareIso hL).pushField
        (fun p => (((periodicPinnedHeightsEquivRooted hL hS).symm z).1 p : ℝ)) =
      rootField hS (fun v => (z v : ℝ)) := by
  funext v
  simp only [Multigraph.Isomorphism.pushField_apply]
  rw [periodicPinnedHeightsEquivRooted_symm_apply]
  by_cases hv : v = periodicRootSite hS <;>
    simp [rootIntegerField, rootField, hv]

private theorem torusDualFieldToSquare_add_apply (hL : 2 < L)
    (u v : TorusEdge L → ℝ) (e : TorusEdge L) :
    torusDualFieldToSquare hL (u + v) ((torusDualSquareIso hL).edges e) =
      torusDualFieldToSquare hL u ((torusDualSquareIso hL).edges e) +
        torusDualFieldToSquare hL v ((torusDualSquareIso hL).edges e) := by
  classical
  unfold torusDualFieldToSquare
  simp only [Equiv.symm_apply_apply, Pi.add_apply]
  split_ifs <;> ring

/-- On integer samples, the periodic interpolated density is the current weight after dual
transport. -/
theorem periodicDensityCoords_integer_sample_eq_currentWeight
    (hL : 2 < L) (hS : 1 < L) {β : ℝ} (hβ : 0 < β)
    (q₀ : TorusEdge L → ℤ) (z : RootedVertex L hS → ℤ) :
    periodicDensityCoords β
        (fun e => 2 * Real.pi * periodicTorusCurrentOffset hL q₀ e)
        (fun v => (z v : ℝ)) =
      (rotatorCurrentWeight (rotatorIReal β)
        (squareCurrentOfTorus hL
          (q₀ + torusDualGradient ((periodicPinnedHeightsEquivRooted hL hS).symm z).1)) : ℂ) := by
  let I := torusDualSquareIso hL
  let h := (periodicPinnedHeightsEquivRooted hL hS).symm z
  let q := q₀ + torusDualGradient h.1
  have hpush : I.pushField (fun p => (h.1 p : ℝ)) =
      rootField hS (fun v => (z v : ℝ)) := by
    simpa [I, h] using periodicPinnedHeight_pushField_eq_rootField hL hS z
  have hdual (e : TorusEdge L) :
      (torusDualGraph hL).grad (fun p => (h.1 p : ℝ)) e =
        (torusDualGradient h.1 e : ℝ) := by
    rw [torusDualGraph_grad_eq_torusDualGradientReal]
    cases e with
    | mk p d => cases d <;> simp [torusDualGradientReal, torusDualGradient, Int.cast_sub]
  have htransport (e : TorusEdge L) :
      (squarePeriodic L).grad (rootField hS (fun v => (z v : ℝ))) (I.edges e) +
          periodicTorusCurrentOffset hL q₀ (I.edges e) =
        torusDualFieldToSquare hL (fun t => (q t : ℝ)) (I.edges e) := by
    rw [← hpush]
    have hgrad :
        torusDualFieldToSquare hL ((torusDualGraph hL).grad
          (fun p => (h.1 p : ℝ))) (I.edges e) =
          (squarePeriodic L).grad (I.pushField (fun p => (h.1 p : ℝ))) (I.edges e) := by
      simpa [I] using torusDualFieldToSquare_grad hL (fun p => (h.1 p : ℝ)) e
    rw [← hgrad]
    unfold periodicTorusCurrentOffset
    have hqreal : (fun t => (q t : ℝ)) =
        (fun t => (q₀ t : ℝ)) + (torusDualGraph hL).grad
          (fun p => (h.1 p : ℝ)) := by
      funext t
      change ((q₀ t + torusDualGradient h.1 t : ℤ) : ℝ) =
        (q₀ t : ℝ) + (torusDualGraph hL).grad (fun p => (h.1 p : ℝ)) t
      rw [Int.cast_add, hdual]
    rw [hqreal, torusDualFieldToSquare_add_apply hL]
    ring
  have hbess (n : ℤ) :
      besselInterp β ((n : ℤ) : ℂ) = (rotatorIReal β n : ℂ) := by
    calc
      besselInterp β ((n : ℤ) : ℂ) = rotatorI β n :=
        besselInterp_intCast_eq_rotatorI hβ n
      _ = (rotatorIReal β n : ℂ) := rotatorI_eq_realCast β n
  have hmode (e : TorusEdge L) :
      besselInterp β
          ((((squarePeriodic L).grad (rootField hS (fun v => (z v : ℝ))) (I.edges e) +
              periodicTorusCurrentOffset hL q₀ (I.edges e) : ℝ) : ℂ)) =
        (rotatorIReal β (q e) : ℂ) := by
    rw [htransport e]
    by_cases hs : currentSameOrientation (torusDualSquareIso hL) e
    · have hv : torusDualFieldToSquare hL (fun t => (q t : ℝ)) (I.edges e) =
          (q e : ℝ) := by
        simp [torusDualFieldToSquare, I, hs]
      rw [hv]
      exact hbess (q e)
    · have hv : torusDualFieldToSquare hL (fun t => (q t : ℝ)) (I.edges e) =
          -(q e : ℝ) := by
        simp [torusDualFieldToSquare, I, hs]
      rw [hv, besselInterp_neg_ofReal hβ]
      simpa [rotatorIReal, besselCoeffRe_neg] using hbess (q e)
  have hprod :
      periodicDensityCoords β
          (fun e => 2 * Real.pi * periodicTorusCurrentOffset hL q₀ e)
          (fun v => (z v : ℝ)) =
        ((∏ e : TorusEdge L, rotatorIReal β (q e) : ℝ) : ℂ) := by
    unfold periodicDensityCoords
    have hdiv : ∀ e : Bond L,
        (2 * Real.pi * periodicTorusCurrentOffset hL q₀ e) / (2 * Real.pi) =
          periodicTorusCurrentOffset hL q₀ e := by
      intro e
      field_simp [ne_of_gt (by positivity : (0 : ℝ) < 2 * Real.pi)]
    simp_rw [hdiv]
    let F : Bond L → ℂ := fun e => besselInterp β
      ((((squarePeriodic L).grad (rootField hS (fun v => (z v : ℝ))) e +
        periodicTorusCurrentOffset hL q₀ e : ℝ) : ℂ))
    calc
      (∏ e : Bond L, F e) = ∏ e : TorusEdge L, F (I.edges e) :=
        (Equiv.prod_comp I.edges F).symm
      _ = ∏ e : TorusEdge L, (rotatorIReal β (q e) : ℂ) := by
        apply Finset.prod_congr rfl
        intro e he
        exact hmode e
      _ = ((∏ e : TorusEdge L, rotatorIReal β (q e) : ℝ) : ℂ) := by
        rw [← Complex.ofReal_prod]
  rw [hprod]
  change ((∏ e : TorusEdge L, rotatorIReal β (q e) : ℝ) : ℂ) = _
  unfold rotatorCurrentWeight squareCurrentOfTorus
  rw [prod_currentPullback_even (squarePeriodicTorusIsomorphism hL) (rotatorIReal β)
    (fun n => by simp [rotatorIReal, besselCoeffRe_neg]) q]

end FroehlichSpencer.BKT.Rotator.Periodic

end
