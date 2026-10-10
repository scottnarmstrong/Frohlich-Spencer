/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib
public import FroehlichSpencer.FS82.SurfaceInfinite.All
public import FroehlichSpencer.FS82.SurfaceInfiniteProof.StateExistence

@[expose] public section

namespace FroehlichSpencer.FS82.Provider.InfiniteGates

theorem cube_limit_state_nonempty (β : ℝ) (hβ : 0 < β) :
    Nonempty (FroehlichSpencer.FS82.SurfaceInfinite.CubeCurvatureLimitState β hβ) :=
  FroehlichSpencer.FS82.SurfaceInfinite.source_cube_limit_state_nonempty β hβ

theorem compact_filling_nonempty (μ : FroehlichSpencer.FS82.SurfaceInfinite.GlobalLinkField)
    (hμ : FroehlichSpencer.FS82.Surface.realLatticeBoundary
      (μ : FroehlichSpencer.FS82.Surface.RealLatticeChain) = 0) :
    ∃ σ : FroehlichSpencer.FS82.SurfaceInfinite.GlobalPlaquetteField,
      FroehlichSpencer.FS82.Surface.realLatticeBoundary
        (σ : FroehlichSpencer.FS82.Surface.RealLatticeChain) =
          (μ : FroehlichSpencer.FS82.Surface.RealLatticeChain) :=
  FroehlichSpencer.FS82.SurfaceInfinite.source_compact_filling_nonempty μ hμ

end FroehlichSpencer.FS82.Provider.InfiniteGates

end
