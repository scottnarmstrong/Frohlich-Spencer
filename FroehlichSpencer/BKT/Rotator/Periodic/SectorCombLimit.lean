/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Rotator.Periodic.SectorComb

/-!
# Periodic Poisson limits in winding sectors

The rootless Fourier cutoff converges to the pinned lattice sum. This file identifies both the
neutral and marked lattice sums with their cohomological winding-sector partition functions.
-/

@[expose] public section

open Complex Filter Topology
open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Lattice2D
open FroehlichSpencer.BKT.Rotator

namespace FroehlichSpencer.BKT.Rotator.Periodic

noncomputable section

private theorem periodicCurrentWeight_summable_for_comb {L : ℕ} (β : ℝ)
    (hI : Summable (rotatorI β)) :
    Summable (fun q : Bond L → ℤ =>
      |rotatorCurrentWeight (rotatorIReal β) q|) := by
  have h := Villain.summable_norm_prod_currents (E := Bond L)
    (fun _ m => rotatorI β m) (fun _ => hI.norm)
  apply h.congr
  intro q
  rw [rotatorCurrentWeight]
  rw [show (∏ e : Bond L, rotatorI β (q e)) =
      ((∏ e : Bond L, rotatorIReal β (q e) : ℝ) : ℂ) by
        simp [rotatorI_eq_realCast]]
  rw [Complex.norm_real, Real.norm_eq_abs]

/--
The real edge offset for a marked winding sector: the fixed source path plus its winding
representative, transported to the periodic square carrier.
-/
def periodicMarkedSectorOffset {L : ℕ} [NeZero L] (hL : 2 < L)
    (a x : Site L) (ξ : ℤ) (w : ℤ × ℤ) : Bond L → ℝ :=
  torusDualFieldToSquare hL (fun e =>
    ((torusSourcePathCurrent (squareTorusVertexEquiv L a)
      (squareTorusVertexEquiv L x) ξ e + torusHarmonicCurrent w e : ℤ) : ℝ))

/-- The complete root-pinned lattice sum of the neutral offset density is the neutral winding
sector weight. -/
theorem periodicNeutralSector_pinnedLatticeSum_eq {L : ℕ} [NeZero L]
    (hL : 2 < L) {β : ℝ} (hβ : 0 < β) (w : ℤ × ℤ)
    (hI : Summable (rotatorI β)) :
    (∑' z : RootedVertex L (by omega) → ℤ,
      periodicDensityCoords β
        (fun e => 2 * Real.pi * periodicSectorOffset hL w e)
        (fun v => (z v : ℝ))) =
      (periodicNeutralSectorWeight hL β w : ℂ) := by
  let hS : 1 < L := by omega
  let E := periodicPinnedHeightsEquivRooted hL hS
  have hcurrent (h : periodicPinnedHeights L) :
      ((periodicNeutralSectorEquiv hL w) h).1.1 =
        periodicTwistedHeightCurrent hL w h := rfl
  have hinj : Function.Injective (periodicTwistedHeightCurrent hL w) := by
    intro h₁ h₂ hh
    apply (periodicNeutralSectorEquiv hL w).injective
    apply Subtype.ext
    apply Subtype.ext
    rw [hcurrent, hcurrent]
    exact hh
  have hsum : Summable (fun h : periodicPinnedHeights L =>
      |rotatorCurrentWeight (rotatorIReal β)
        (periodicTwistedHeightCurrent hL w h)|) := by
    have hall := periodicCurrentWeight_summable_for_comb (L := L) β hI
    apply hall.comp_injective
    exact hinj
  have hsumReal : Summable (fun h : periodicPinnedHeights L =>
      rotatorCurrentWeight (rotatorIReal β)
        (periodicTwistedHeightCurrent hL w h)) := hsum.of_norm
  have hsumComplex :
      (∑' h : periodicPinnedHeights L,
        (rotatorCurrentWeight (rotatorIReal β)
          (periodicTwistedHeightCurrent hL w h) : ℂ)) =
        (periodicNeutralHeightSectorWeight hL β w : ℂ) := by
    rw [← Complex.ofReal_tsum (fun h : periodicPinnedHeights L =>
      rotatorCurrentWeight (rotatorIReal β)
        (periodicTwistedHeightCurrent hL w h))]
    rfl
  calc
    _ = ∑' h : periodicPinnedHeights L,
        periodicDensityCoords β
          (fun e => 2 * Real.pi * periodicSectorOffset hL w e)
          (fun v => ((E h) v : ℝ)) := by
      exact (Equiv.tsum_eq E (fun z : RootedVertex L hS → ℤ =>
        periodicDensityCoords β
          (fun e => 2 * Real.pi * periodicSectorOffset hL w e)
          (fun v => (z v : ℝ)))).symm
    _ = ∑' h : periodicPinnedHeights L,
        (rotatorCurrentWeight (rotatorIReal β)
          (periodicTwistedHeightCurrent hL w h) : ℂ) := by
      apply tsum_congr
      intro h
      have hs := periodicDensityCoords_integer_sample_eq_currentWeight
        hL hS hβ (torusHarmonicCurrent w) (E h)
      have hinv : (E.symm (E h)).1 = h.1 := by simp [E]
      rw [hinv] at hs
      have horder : torusHarmonicCurrent w + torusDualGradient h.1 =
          torusDualGradient h.1 + torusHarmonicCurrent w := by
        funext e
        exact add_comm _ _
      rw [horder] at hs
      simpa [E, periodicSectorOffset, periodicTorusCurrentOffset,
        periodicTwistedHeightCurrent] using hs
    _ = (periodicNeutralHeightSectorWeight hL β w : ℂ) := by
      exact hsumComplex
    _ = (periodicNeutralSectorWeight hL β w : ℂ) := by
      rw [periodicNeutralSectorWeight_eq_twistedHeight]

/-- The periodic neutral comb pairings converge to the neutral sector partition function. -/
theorem periodicNeutralCombPairing_tendsto_sector {L : ℕ} [NeZero L]
    (hL : 2 < L) {β : ℝ} (hβ : 0 < β) (hβ₁ : 1 ≤ β) (w : ℤ × ℤ)
    (hI : Summable (rotatorI β)) :
    Tendsto (fun N : ℕ =>
      ∫ z : RootedVertex L (by omega) → ℝ,
        periodicNeutralCombCutoff N z *
          periodicDensityCoords β
            (fun e => 2 * Real.pi * periodicSectorOffset hL w e) z) atTop
      (𝓝 (periodicNeutralSectorWeight hL β w : ℂ)) := by
  let hS : 1 < L := by omega
  rw [← periodicNeutralSector_pinnedLatticeSum_eq hL hβ w hI]
  exact periodicNeutralCombCutoffPairing_tendsto_pinnedLatticeSum hβ₁
    (fun e => 2 * Real.pi * periodicSectorOffset hL w e)

/-- The complete root-pinned lattice sum of the marked offset density is the marked winding
sector weight. -/
theorem periodicMarkedSector_pinnedLatticeSum_eq {L : ℕ} [NeZero L]
    (hL : 2 < L) {β : ℝ} (hβ : 0 < β) (a x : Site L) (ξ : ℤ) (w : ℤ × ℤ)
    (hI : Summable (rotatorI β)) :
    (∑' z : RootedVertex L (by omega) → ℤ,
      periodicDensityCoords β
        (fun e => 2 * Real.pi * periodicMarkedSectorOffset hL a x ξ w e)
        (fun v => (z v : ℝ))) =
      (periodicMarkedSectorWeight hL β a x ξ w : ℂ) := by
  let hS : 1 < L := by omega
  let E := periodicPinnedHeightsEquivRooted hL hS
  have hcurrent (h : periodicPinnedHeights L) :
      ((periodicMarkedSectorEquiv hL a x ξ w) h).1 =
        periodicMarkedTwistedHeightCurrent hL a x ξ w h := rfl
  have hinj : Function.Injective (periodicMarkedTwistedHeightCurrent hL a x ξ w) := by
    intro h₁ h₂ hh
    apply (periodicMarkedSectorEquiv hL a x ξ w).injective
    apply Subtype.ext
    rw [hcurrent, hcurrent]
    exact hh
  have hsum : Summable (fun h : periodicPinnedHeights L =>
      |rotatorCurrentWeight (rotatorIReal β)
        (periodicMarkedTwistedHeightCurrent hL a x ξ w h)|) := by
    have hall := periodicCurrentWeight_summable_for_comb (L := L) β hI
    apply hall.comp_injective
    exact hinj
  have hsumComplex :
      (∑' h : periodicPinnedHeights L,
        (rotatorCurrentWeight (rotatorIReal β)
          (periodicMarkedTwistedHeightCurrent hL a x ξ w h) : ℂ)) =
        (periodicMarkedHeightSectorWeight hL β a x ξ w : ℂ) := by
    rw [← Complex.ofReal_tsum (fun h : periodicPinnedHeights L =>
      rotatorCurrentWeight (rotatorIReal β)
        (periodicMarkedTwistedHeightCurrent hL a x ξ w h))]
    rfl
  calc
    _ = ∑' h : periodicPinnedHeights L,
        periodicDensityCoords β
          (fun e => 2 * Real.pi * periodicMarkedSectorOffset hL a x ξ w e)
          (fun v => ((E h) v : ℝ)) := by
      exact (Equiv.tsum_eq E (fun z : RootedVertex L hS → ℤ =>
        periodicDensityCoords β
          (fun e => 2 * Real.pi * periodicMarkedSectorOffset hL a x ξ w e)
          (fun v => (z v : ℝ)))).symm
    _ = ∑' h : periodicPinnedHeights L,
        (rotatorCurrentWeight (rotatorIReal β)
          (periodicMarkedTwistedHeightCurrent hL a x ξ w h) : ℂ) := by
      apply tsum_congr
      intro h
      let γ := torusSourcePathCurrent (squareTorusVertexEquiv L a)
        (squareTorusVertexEquiv L x) ξ
      let q₀ := γ + torusHarmonicCurrent w
      have hs := periodicDensityCoords_integer_sample_eq_currentWeight
        hL hS hβ q₀ (E h)
      have hinv : (E.symm (E h)).1 = h.1 := by simp [E]
      rw [hinv] at hs
      have hq₀ : q₀ + torusDualGradient h.1 =
          γ + (torusDualGradient h.1 + torusHarmonicCurrent w) := by
        funext e
        simp [q₀, γ]
        ring
      rw [hq₀] at hs
      simpa [E, γ, q₀, periodicMarkedSectorOffset, periodicTorusCurrentOffset,
        periodicMarkedTwistedHeightCurrent] using hs
    _ = (periodicMarkedHeightSectorWeight hL β a x ξ w : ℂ) := hsumComplex
    _ = (periodicMarkedSectorWeight hL β a x ξ w : ℂ) := by
      rw [periodicMarkedSectorWeight_eq_twistedHeight]

/-- The periodic marked comb pairings converge to the marked winding sector partition function. -/
theorem periodicMarkedCombPairing_tendsto_sector {L : ℕ} [NeZero L]
    (hL : 2 < L) {β : ℝ} (hβ : 0 < β) (hβ₁ : 1 ≤ β)
    (a x : Site L) (ξ : ℤ) (w : ℤ × ℤ) (hI : Summable (rotatorI β)) :
    Tendsto (fun N : ℕ =>
      ∫ z : RootedVertex L (by omega) → ℝ,
        periodicNeutralCombCutoff N z *
          periodicDensityCoords β
            (fun e => 2 * Real.pi * periodicMarkedSectorOffset hL a x ξ w e) z) atTop
      (𝓝 (periodicMarkedSectorWeight hL β a x ξ w : ℂ)) := by
  let hS : 1 < L := by omega
  rw [← periodicMarkedSector_pinnedLatticeSum_eq hL hβ a x ξ w hI]
  exact periodicNeutralCombCutoffPairing_tendsto_pinnedLatticeSum hβ₁
    (fun e => 2 * Real.pi * periodicMarkedSectorOffset hL a x ξ w e)

end

end FroehlichSpencer.BKT.Rotator.Periodic

end
