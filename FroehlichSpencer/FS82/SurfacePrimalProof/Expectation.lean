/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.SurfacePrimalProof.Observable
public import FroehlichSpencer.FS82.PrimalInterface.PrimalBridge
public import FroehlichSpencer.FS82.Wilson.PrimalFieldStrength
import Mathlib.Tactic

open MeasureTheory
open FroehlichSpencer.FS82.Surface
open FroehlichSpencer.FS82.Wilson

@[expose] public section
namespace FroehlichSpencer.FS82.SurfaceInfinite

open PrimalInterface

 theorem sourcePrimalPairExpectation_eq_internal (R : Surface.RectBox4)
    (β : ℝ) (hβ : 0 < β) (p q : Surface.PrimalPlaquettes R) :
    (∫ θ : Surface.PrimalLinks R → ℝ,
      sourcePrimalFieldStrength R β hβ θ p * sourcePrimalFieldStrength R β hβ θ q ∂
        Surface.primalVillainLaw R β hβ) =
      Wilson.primalFieldStrengthCorrelation β
        (PrimalInterface.plaquetteEquiv R p) (PrimalInterface.plaquetteEquiv R q) := by
  have hobs : (fun θ : Surface.PrimalLinks R → ℝ =>
      sourcePrimalFieldStrength R β hβ θ p * sourcePrimalFieldStrength R β hβ θ q) =
      fun θ => (fun z : Wilson.PrimalAngleConfig R.side =>
        Wilson.primalFieldStrength β z (PrimalInterface.plaquetteEquiv R p) *
        Wilson.primalFieldStrength β z (PrimalInterface.plaquetteEquiv R q))
          (PrimalInterface.circleConfig (PrimalInterface.linkEquiv R) θ) := by
    funext θ
    rw [sourcePrimalFieldStrength_eq_circle R β hβ θ p,
      sourcePrimalFieldStrength_eq_circle R β hβ θ q]
  have hZ : 0 < ∫ z, Wilson.primalVillainDensity (B := R.side) β z
      ∂PrimalInterface.torusHaar (Wilson.PrimalLinks R.side) := by
    exact Wilson.primalVillainPartition_pos β hβ
  let F : Wilson.PrimalAngleConfig R.side → ℂ := fun z =>
    Wilson.primalFieldStrength β z (PrimalInterface.plaquetteEquiv R p) *
      Wilson.primalFieldStrength β z (PrimalInterface.plaquetteEquiv R q)
  have hF : Continuous F :=
    (Wilson.continuous_primalFieldStrength β hβ (PrimalInterface.plaquetteEquiv R p)).mul
      (Wilson.continuous_primalFieldStrength β hβ (PrimalInterface.plaquetteEquiv R q))
  rw [hobs, PrimalInterface.primalVillainLaw_eq R β hβ]
  have hn := PrimalInterface.integral_normalized (PrimalInterface.linkEquiv R) _
    (Wilson.primalVillainDensity_continuous (B := R.side) β)
    (fun z => (Wilson.primalVillainDensity_pos β z hβ).le) hZ F hF
  change (∫ θ, F (PrimalInterface.circleConfig (PrimalInterface.linkEquiv R) θ) ∂_) = _
  rw [hn]
  unfold Wilson.primalFieldStrengthCorrelation
  congr 1
  apply integral_congr_ae
  filter_upwards [] with z
  dsimp [F]
  ring

end FroehlichSpencer.FS82.SurfaceInfinite
end
