/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Order.LiminfLimsup
public import FroehlichSpencer.BKT.Surface.VillainClockModel
public import FroehlichSpencer.BKT.Rotator.FreeBox
public import FroehlichSpencer.BKT.Clock.Compact.Theorem71
public import FroehlichSpencer.BKT.Generic.Marked.Gap
public import FroehlichSpencer.BKT.Lattice2D.LogLowerBound
public import FroehlichSpencer.BKT.Clock.VillainClock.Model
public import FroehlichSpencer.BKT.Clock.VillainClock.SourceTheorem71
public import FroehlichSpencer.BKT.Bridge.VillainClockCorrelation


@[expose] public section

open MeasureTheory Filter
open Filter Topology
open FroehlichSpencer.BKT.Rotator.Ginibre
open FroehlichSpencer.BKT.Clock.VillainClock
open FroehlichSpencer.BKT.Clock.Compact (l1Dist)
open FroehlichSpencer.BKT.Bridge.VillainClockCorrelation

namespace FroehlichSpencer.BKT.Provider

theorem villain_clock_theorem71_2 :
    ∃ n₀ : ℝ → ℝ → ℕ, ∃ β'' : ℝ → ℕ → ℝ → ℝ,
      (∀ q : ℝ, 0 < q →
        Tendsto (fun β : ℝ => n₀ β q) atTop atTop) ∧
      (∀ β : ℝ, Tendsto (fun q : ℝ => n₀ β q) (𝓝[>] 0) atTop) ∧
      (∀ (β : ℝ) (N : ℕ) (q : ℝ), n₀ β q ≤ N →
        0 < β'' β N q) ∧
      ∀ q : ℝ, 0 < q →
        ∀ (β : ℝ) (hβ : 0 < β) (N : ℕ), n₀ β q ≤ N →
          ∀ (hN : 0 < N) (ξ : ℕ), 0 < ξ → ξ < N →
            q ≤ Generic.Marked.dipoleGap ((ξ : ℝ) / N) →
              ((∀ (L : ℕ) (a b : Rotator.RotatorSpinSite L),
                  ∫ θ, Real.cos ((ξ : ℤ) *
                    (Rotator.Ginibre.latticeAngle θ (Rotator.Ginibre.siteToZ a) -
                      Rotator.Ginibre.latticeAngle θ (Rotator.Ginibre.siteToZ b)))
                    ∂villainClockModel N hN β hβ (Rotator.Ginibre.squareBoxZ L) ≤
                    2 * ((↑(Lattice2D.freeRadius a b) : ℝ) + 1) ^
                      (-((↑ξ : ℝ) ^ 2 / (2 * Real.pi * β'' β N q)))) ∧
                (∀ (L : ℕ) (u v : ℤ × ℤ),
                  Rotator.Ginibre.boxRadius u ≤ L → Rotator.Ginibre.boxRadius v ≤ L →
                    ∫ θ, Real.cos ((ξ : ℤ) *
                      (Rotator.Ginibre.latticeAngle θ u - Rotator.Ginibre.latticeAngle θ v))
                      ∂villainClockModel N hN β hβ (Rotator.Ginibre.freeBox L) ≤
                      2 * ((↑(l1Dist u v) : ℝ) + 1) ^
                      (-((↑ξ : ℝ) ^ 2 / (2 * Real.pi * β'' β N q)))) ∧
              ∀ (u v : ℤ × ℤ),
                Filter.limsup
                    (fun L : ℕ => ∫ θ, Real.cos ((ξ : ℤ) *
                      (Rotator.Ginibre.latticeAngle θ u - Rotator.Ginibre.latticeAngle θ v))
                      ∂villainClockModel N hN β hβ (Rotator.Ginibre.freeBox L))
                    atTop ≤
                  2 * ((↑(l1Dist u v) : ℝ) + 1) ^
                    (-((↑ξ : ℝ) ^ 2 / (2 * Real.pi * β'' β N q)))) := by
  obtain ⟨c, hc, n₀, β'', hβgrow, hqgrow, hpos, hbounds⟩ :=
    Clock.VillainClock.villain_clock_theorem71_2_source
  refine ⟨n₀, β'', hβgrow, hqgrow, ?_, ?_⟩
  · intro β N q hN
    exact hpos β N q hN
  · intro q hq β hβ N hNle hNpos ξ hξ0 hξN hgap
    rcases hbounds q hq β hβ N hNle hNpos ξ hξ0 hξN hgap with
      ⟨⟨hsquare, hfree⟩, hlimit⟩
    refine ⟨?_, ?_⟩
    · intro L a b
      have h := hsquare L a b
      rw [← villainClockLaw_twoPoint_eq N hNpos β hβ (ξ : ℤ) (squareBoxZ L)
        (siteToZ a) (siteToZ b)] at h
      exact h
    · refine ⟨?_, ?_⟩
      · intro L u v hu hv
        have h := hfree L u v hu hv
        rw [← villainClockLaw_twoPoint_eq N hNpos β hβ (ξ : ℤ) (freeBox L) u v] at h
        exact h
      · intro u v
        have h := hlimit u v
        rw [← villainClockLaw_limsup_eq_twoPointLimit N hNpos β hβ (ξ : ℤ) u v] at h
        exact h

end FroehlichSpencer.BKT.Provider

end
