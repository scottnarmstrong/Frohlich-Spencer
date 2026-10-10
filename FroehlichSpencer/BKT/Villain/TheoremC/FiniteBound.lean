/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Villain.TheoremC.Numbers
public import FroehlichSpencer.BKT.Rotator.TheoremC.MainD
public import FroehlichSpencer.BKT.Rotator.FreeBox
public import FroehlichSpencer.BKT.Generic.PinnedCharges.WiredAdapter

/-! # Gaussian Villain finite-volume rooted T1.5 bound

This is the direct Gaussian specialization of the rooted T1.5-NG theorem on `squareZero`. The
same pinned layer hypothesis as the rotator route suffices for this analytic estimate.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Villain.TheoremC

open MeasureTheory Filter Topology
open FroehlichSpencer.BKT.Generic
open FroehlichSpencer.BKT.Rotator
open FroehlichSpencer.BKT.Rotator.TheoremC
open FroehlichSpencer.BKT.Lattice2D
open FroehlichSpencer.BKT.Generic.PinnedCharges (SquareZeroBond)

/-- The rooted T1.5 estimate for the Gaussian Villain edge weight, uniformly in the cutoff and
box, under the same `PinnedLayerHypothesisD` as the rotator theorem. `B` is four π squared times
the physical Villain inverse temperature. -/
theorem integral_shift_ge_gaussianVillain_of_pinnedLayerD
    (hyp : PinnedLayerHypothesisD) :
    ∃ (L₀ : ℕ) (B₀ : ℝ) (ε : ℝ → ℝ),
      1 ≤ B₀ ∧ Tendsto ε atTop (𝓝 0) ∧
      ∀ B : ℝ, B₀ ≤ B →
        ∀ L : ℕ, L₀ ≤ L → 1 < L → ∀ N : ℕ, 1 ≤ N →
          ∀ σ : RotatorDualFace L → ℝ, ∀ θ : SquareZeroBond L → ℝ,
            Real.exp (-(B⁻¹ * ∑ e, θ e ^ 2) -
                ε B * ∑ e, (toIcoMod Real.two_pi_pos (-Real.pi) ((squareZero L).grad σ e) ^ 2 +
                  θ e ^ 2)) *
                ∫ φ, edgeDensity (squareZero L) (gaussianVillainWeight B) none φ *
                  ∏ j, pinnedCombLam L N j (φ j - φ none) ≤
              ∫ φ, offsetEdgeDensity (squareZero L) (gaussianVillainWeight B) θ none φ *
                ∏ j, pinnedCombLam L N j
                  (φ j + σ j - (φ none + σ none)) := by
  obtain ⟨D₁, D₂, α, K₀, K₁, Kv, a₁, a₂, Kov, L₀, hα, hK₀, hK₁, hD₁, hKv, hwit⟩ := hyp
  obtain ⟨B₀, amp, b, ε, k₀, hB₀, hεlim, hN⟩ :=
    exists_gaussianVillainNumbers Kov hα hK₀ hK₁ hD₁ hKv
  refine ⟨L₀, B₀, ε, hB₀, hεlim, fun B hB L hL₀ hL N hN' σ θ => ?_⟩
  have hBpos : 0 < B := by linarith [hB₀, hB]
  have hW0 : 0 ≤ Real.pi * B := by positivity
  have hW1 : 1 ≤ Real.pi * B := by nlinarith [Real.two_le_pi]
  obtain ⟨hamp, hampW, hk₀, hexp, hquad₁, hquad₂, hM, hb8, hb₁, hb₂, hε0, hthr⟩ := hN B hB
  obtain ⟨Wt⟩ := hwit L hL₀ N hN'
  obtain ⟨hw, hnzero, hlog, hcurv, hcost⟩ :=
    gaussianVillainWeight_data hBpos (Real.pi * B) hW0
  exact integral_shift_ge_of_rootedLayerD (squareZero_connected L hL) none Wt.layer
    Wt.isLocal hKv hw hnzero hlog hcurv hcost (inv_pos.mpr hBpos) hK₀ hK₁ hD₁ hamp hampW hW1
    hk₀ hexp hquad₁ hquad₂ zero_le_one le_rfl hM Wt.entropy_exp hb8 hb₁ hb₂ hthr σ θ

end FroehlichSpencer.BKT.Villain.TheoremC

end
