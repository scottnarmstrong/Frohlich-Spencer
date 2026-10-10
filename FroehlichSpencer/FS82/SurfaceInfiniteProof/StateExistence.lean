module


public import FroehlichSpencer.FS82.SurfaceInfiniteProof.StateIdentities
public import FroehlichSpencer.FS82.Infinite.LimitStateLimit
public import FroehlichSpencer.FS82.Infinite.CubeExhaustion
public import FroehlichSpencer.FS82.SurfaceInfiniteProof.BoundaryBridge

@[expose] public section

open FroehlichSpencer.FS82.Surface
open FroehlichSpencer.FS82.SurfaceInfinite
open FroehlichSpencer.FS82.Infinite

namespace FroehlichSpencer.FS82.SurfaceInfinite

theorem source_cube_limit_state_nonempty (β : ℝ) (hβ : 0 < β) :
    Nonempty (CubeCurvatureLimitState β hβ) := by
  obtain ⟨L⟩ := exists_cubeCurvatureLimitState β hβ
  exact ⟨cubeStateOfInternal L⟩

theorem source_compact_filling_nonempty (μ : GlobalLinkField)
    (hμ : realLatticeBoundary (μ : Surface.RealLatticeChain) = 0) :
    ∃ σ : GlobalPlaquetteField,
      realLatticeBoundary (σ : Surface.RealLatticeChain) =
        (μ : Surface.RealLatticeChain) := by
  have hμ' : globallyCoClosed μ := by
    change globalBoundary (μ : FroehlichSpencer.FS82.Cubical.RealLatticeChain 4) = 0
    rw [← FroehlichSpencer.FS82.SurfaceInfiniteProof.surface_boundary_eq_global]
    exact hμ
  obtain ⟨σ, hfill⟩ := compactFilling_exists μ hμ'
  refine ⟨σ, ?_⟩
  rw [FroehlichSpencer.FS82.SurfaceInfiniteProof.surface_boundary_eq_global]
  exact hfill

end FroehlichSpencer.FS82.SurfaceInfinite
