module
public import Mathlib
public import FroehlichSpencer.BKT.Ginibre.Models
public import FroehlichSpencer.BKT.Surface.VillainClock.VillainContinuousCorrelation
public import FroehlichSpencer.BKT.Surface.VillainClock.VillainContinuousLimit
public import FroehlichSpencer.BKT.Surface.VillainClock.FreeBox
public import FroehlichSpencer.BKT.Surface.VillainClock.RotatorSpinSite
public import FroehlichSpencer.BKT.Surface.VillainClock.BoxRadius
public import FroehlichSpencer.BKT.Surface.VillainClock.L1Dist
public import FroehlichSpencer.BKT.Surface.VillainClock.FreeRadius
public import FroehlichSpencer.BKT.Surface.VillainClock.DipoleGap
public import FroehlichSpencer.BKT.Surface.VillainClock.SiteToZ
public import FroehlichSpencer.BKT.Surface.VillainClock.SquareBoxZ
public import FroehlichSpencer.BKT.Clock.Compact.Theorem71
public import FroehlichSpencer.BKT.Generic.Marked.Gap
public import FroehlichSpencer.BKT.Lattice2D.LogLowerBound

@[expose] public section

open MeasureTheory
open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Ginibre
open FroehlichSpencer.BKT.Rotator.Ginibre

namespace FroehlichSpencer.BKT.Surface.VillainClock.Bridge

theorem villainContinuousCorrelation_eq_internal (β : ℝ) (hβ : 0 < β) (ξ : ℤ)
    (Λ : Finset (ℤ × ℤ)) (u v : ℤ × ℤ) :
    VillainClock.villainContinuousCorrelation β hβ ξ Λ u v =
      (Ginibre.villainModel β hβ).twoPoint ξ Λ u v := by
  let M := Ginibre.villainModel β hβ
  have hν : M.ν = volume.restrict (Set.Ico (-Real.pi) Real.pi) := rfl
  have hw (b : Λ × Λ) : IsBondWeight (M.bondWeight Λ b) := M.isBondWeight_bondWeight Λ b
  have hweight (θ : Λ → ℝ) :
      (∏ b : Λ × Λ,
        (if (b.2 : ℤ × ℤ) = (b.1 : ℤ × ℤ) + (1, 0) ∨
            (b.2 : ℤ × ℤ) = (b.1 : ℤ × ℤ) + (0, 1) then
          (fun x : ℝ => ∑' m : ℤ, Real.exp (-(β / 2) * (x + 2 * Real.pi * m) ^ 2))
        else fun _ => 1) (θ b.1 - θ b.2)) =
      Ginibre.pairWeight (Rotator.Ginibre.bondFrequency Λ) (M.bondWeight Λ) θ := by
    simp only [Ginibre.pairWeight, Rotator.Ginibre.phase_bondFrequency]
    refine Finset.prod_congr rfl ?_
    intro b hb
    simp only [Ginibre.FreeModel.bondWeight, M, Ginibre.villainModel,
      Rotator.Ginibre.LatticeStep]
    rfl

  rw [VillainClock.villainContinuousCorrelation, Ginibre.FreeModel.twoPoint,
    Ginibre.FreeModel.gibbs, Ginibre.integral_pairGibbs M.mass_ne_zero hw]
  rw [hν]
  congr 1
  · refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
    calc
      Real.cos (ξ * (VillainClock.latticeAngleLiteral θ u - VillainClock.latticeAngleLiteral θ v)) * _ =
          Real.cos (ξ * (Rotator.Ginibre.latticeAngle θ u -
            Rotator.Ginibre.latticeAngle θ v)) * _ := by
              congr 2
      _ = _ := by
        exact congrArg (fun z : ℝ =>
          Real.cos (ξ * (Rotator.Ginibre.latticeAngle θ u -
            Rotator.Ginibre.latticeAngle θ v)) * z) (hweight θ)
  · refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
    exact hweight θ


theorem latticeAngleLiteral_eq_internal {Λ : Finset (ℤ × ℤ)}
    (θ : Λ → ℝ) (z : ℤ × ℤ) :
    VillainClock.latticeAngleLiteral θ z = Rotator.Ginibre.latticeAngle θ z := rfl

theorem freeBox_eq_explicit (L : ℕ) :
    VillainClock.freeBox L =
      Finset.Icc (-(L : ℤ)) L ×ˢ Finset.Icc (-(L : ℤ)) L := rfl


theorem rotatorSpinSite_eq_internal (L : ℕ) :
    VillainClock.rotatorSpinSite L = FroehlichSpencer.BKT.Rotator.RotatorSpinSite L := rfl

theorem boxRadius_eq_internal (z : ℤ × ℤ) :
    VillainClock.boxRadius z = FroehlichSpencer.BKT.Rotator.Ginibre.boxRadius z := rfl

theorem freeBox_eq_internal (L : ℕ) :
    VillainClock.freeBox L = FroehlichSpencer.BKT.Rotator.Ginibre.freeBox L := rfl

theorem l1Dist_eq_internal (u v : ℤ × ℤ) :
    VillainClock.l1Dist u v = FroehlichSpencer.BKT.Clock.Compact.l1Dist u v := rfl

theorem freeRadius_eq_internal {L : ℕ} (p x : Fin L × Fin L) :
    VillainClock.freeRadius p x = FroehlichSpencer.BKT.Lattice2D.freeRadius p x := rfl

theorem dipoleGap_eq_internal (ξ : ℝ) :
    VillainClock.dipoleGap ξ = FroehlichSpencer.BKT.Generic.Marked.dipoleGap ξ := rfl

theorem siteToZ_eq_internal {L : ℕ} (p : VillainClock.rotatorSpinSite L) :
    VillainClock.siteToZ p = FroehlichSpencer.BKT.Rotator.Ginibre.siteToZ p := rfl

theorem squareBoxZ_eq_internal (L : ℕ) :
    VillainClock.squareBoxZ L = FroehlichSpencer.BKT.Rotator.Ginibre.squareBoxZ L := rfl

theorem villainContinuousLimit_eq_internal (β : ℝ) (hβ : 0 < β) (ξ : ℤ)
    (u v : ℤ × ℤ) :
    VillainClock.villainContinuousLimit β hβ ξ u v =
      (Ginibre.villainModel β hβ).twoPointLimit ξ u v := by
  rw [VillainClock.villainContinuousLimit]
  apply Filter.Tendsto.limsup_eq
  convert (Ginibre.villainModel β hβ).tendsto_twoPointLimit ξ u v using 1
  funext L
  exact villainContinuousCorrelation_eq_internal β hβ ξ
    (VillainClock.freeBox L) u v

end FroehlichSpencer.BKT.Surface.VillainClock.Bridge
