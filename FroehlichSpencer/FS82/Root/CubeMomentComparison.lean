/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Root.FiniteMomentComparison
public import FroehlichSpencer.FS82.Infinite.MomentLimit

/-!
# the cube corollary of the first root

Every centred cube of side `2N`, `N ≥ 1`, is log-thick, so the first root gives (2.93) on the whole
cube tail with one `β''`.
-/

open Filter
open FroehlichSpencer.FS82.Gaussian
open FroehlichSpencer.FS82.Moment.SourceConstructor
open FroehlichSpencer.FS82.Moment.Comparison
open FroehlichSpencer.FS82.Infinite

@[expose] public section

namespace FroehlichSpencer.FS82.Root

/-- Every centred cube of side `2N`, `N ≥ 1`, is log-thick. -/
theorem cube_isLogThickBox (N : ℕ) (hN : 1 ≤ N) : IsLogThickBox (cube N) := by
  have hlog : Real.log ((2 * N : ℕ) + 1 : ℝ) ≤ ((2 * N : ℕ) : ℝ) := by
    have hpos : (0 : ℝ) < ((2 * N : ℕ) : ℝ) + 1 := by positivity
    have h := Real.log_le_sub_one_of_pos hpos
    linarith
  refine ⟨2 * N, ⌈Real.log ((2 * N : ℕ) + 1 : ℝ)⌉₊, by omega, Nat.le_ceil _, ?_, ?_⟩
  · intro i
    exact Nat.ceil_le.mpr hlog
  · intro i
    exact le_rfl

/-- **The cube root.** For `β` above the threshold, (2.93) holds on every cube `N ≥ 1` with the
single lower rate `β'' = β(1 − 2β c_pack(β))`. -/
theorem fs82_cube_moment_comparison {β : ℝ} (hβ : rootBetaThreshold ≤ β) :
    ∀ N, 1 ≤ N → ∀ μN : cubeSourceW N, ∀ t : ℝ,
      Real.exp ((t ^ 2 * betaDoublePrime rootPackingCoefficient β / 2) *
          quotientCovarianceQuadratic (sourceLatticeComplex (B := cube N)) μN) ≤
        sourceDualMoment β μN t ∧
      sourceDualMoment β μN t ≤
        Real.exp ((t ^ 2 * β / 2) *
          quotientCovarianceQuadratic (sourceLatticeComplex (B := cube N)) μN) := by
  intro N hN μN t
  obtain ⟨N', m, hN', hm, hmin, hBmax⟩ := cube_isLogThickBox N hN
  exact fs82_moment_comparison_logThick_box N' m hN' hm hmin hBmax hβ μN t


theorem fs82_cubeMoment_infinite_volume {β : ℝ} (hβ : rootBetaThreshold ≤ β)
    (μ : GlobalLinkField) (hμ : globallyCoClosed μ) (t : ℝ) :
    ∃ N₀, 1 ≤ N₀ ∧
      ∃ hW : ∀ N ≥ N₀,
        cubeLinkRestriction N (μ : Cubical.RealLatticeChain 4) ∈ cubeSourceW N,
        (∀ x, IsCubeMomentClusterPoint (cubeMomentTail N₀ β t μ hW) x →
          Real.exp ((t ^ 2 * betaDoublePrime rootPackingCoefficient β / 2) *
            globalVariationalCovariance μ) ≤ x ∧
          x ≤ Real.exp ((t ^ 2 * β / 2) * globalVariationalCovariance μ)) ∧
        (∃ x, IsCubeMomentClusterPoint (cubeMomentTail N₀ β t μ hW) x) ∧
        Real.exp ((t ^ 2 * betaDoublePrime rootPackingCoefficient β / 2) *
            globalVariationalCovariance μ) ≤
          Filter.liminf (cubeMomentTail N₀ β t μ hW) atTop ∧
        Filter.limsup (cubeMomentTail N₀ β t μ hW) atTop ≤
          Real.exp ((t ^ 2 * β / 2) * globalVariationalCovariance μ) :=
  exists_cubeMoment_finite_to_infinite μ hμ (fs82_cube_moment_comparison hβ) t

end FroehlichSpencer.FS82.Root

end
