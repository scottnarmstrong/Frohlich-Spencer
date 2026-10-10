/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.SOS.Peierls.Summability
public import FroehlichSpencer.BKT.SOS.Roughening.Theorem73

/-! # The two regimes of the pinned SOS model (FS81 §7.2, Remark 2)

The high-temperature (small β) side follows from Theorem 7.3 at pairs whose distance equals their
boundary depth. The large β Peierls estimate is the remaining predecessor for the full transition.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.SOS.Peierls

open Filter Topology
open FroehlichSpencer.BKT.Generic.PinnedCharges (Site siteBoundaryDepth)
open FroehlichSpencer.BKT.SOS.Roughening

/-- At arbitrarily large scale, a square contains a deep pair at exactly that distance. -/
def deepPairLeft (L₀ r : ℕ) : Site (max L₀ (2 * r + 1)) :=
  (⟨0, by omega⟩, ⟨r, by omega⟩)

def deepPairCenter (L₀ r : ℕ) : Site (max L₀ (2 * r + 1)) :=
  (⟨r, by omega⟩, ⟨r, by omega⟩)

theorem deepPair_geometry (L₀ r : ℕ) :
    L₀ ≤ max L₀ (2 * r + 1) ∧
      linfDist (deepPairCenter L₀ r) (deepPairLeft L₀ r) ≤
        siteBoundaryDepth (deepPairCenter L₀ r) := by
  constructor
  · exact Nat.le_max_left _ _
  · simp [deepPairCenter, deepPairLeft, linfDist, siteBoundaryDepth]
    omega

/-- The pinned-box variance is unbounded over boxes and deep pairs for every sufficiently small
β, with the quantitative lower bound furnished by FS81 (7.18). -/
theorem sos_smallTemperature_variance_unbounded :
    ∃ (β₀ : ℝ) (β' : ℝ → ℝ) (L₀ : ℕ), 0 < β₀ ∧
      Tendsto β' (𝓝[>] 0) (𝓝 0) ∧
      ∀ β : ℝ, 0 < β → β ≤ β₀ → 0 < β' β ∧
        ∀ K : ℝ, ∃ L : ℕ, ∃ u v : Site L,
          L₀ ≤ L ∧ linfDist u v ≤ siteBoundaryDepth u ∧
            K < sosVariance L β u v := by
  obtain ⟨β₀, β', L₀, hβ₀, hlim, hdeep⟩ := sos_theorem73_deep
  refine ⟨β₀, β', L₀, hβ₀, hlim, ?_⟩
  intro β hβ hββ₀
  obtain ⟨hβ', hbound⟩ := hdeep β hβ hββ₀
  refine ⟨hβ', ?_⟩
  intro K
  have hlog : Tendsto (fun r : ℕ => Real.log (1 + (r : ℝ))) atTop atTop := by
    exact Real.tendsto_log_atTop.comp (by
      simpa [add_comm] using
        (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop))
  obtain ⟨r, hr⟩ := (hlog.eventually_gt_atTop (K * β' β)).exists
  let L := max L₀ (2 * r + 1)
  let u : Site L := deepPairCenter L₀ r
  let v : Site L := deepPairLeft L₀ r
  have hgeom := deepPair_geometry L₀ r
  have hdist : linfDist u v = r := by
    simp [u, v, deepPairCenter, deepPairLeft, linfDist]
  have hvbound := (hbound L (Nat.le_max_left _ _) u v hgeom.2).2
  rw [hdist] at hvbound
  have hK : K < Real.log (1 + (r : ℝ)) / β' β :=
    (lt_div_iff₀ hβ').2 (by simpa [mul_comm] using hr)
  refine ⟨L, u, v, hgeom.1, hgeom.2, ?_⟩
  exact lt_of_lt_of_le hK hvbound

end FroehlichSpencer.BKT.SOS.Peierls

end
