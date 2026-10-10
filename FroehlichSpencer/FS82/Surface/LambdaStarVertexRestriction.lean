/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib
public import FroehlichSpencer.FS82.Surface.RectBox4
public import FroehlichSpencer.FS82.Surface.DualCoord
public import FroehlichSpencer.FS82.Surface.DualCell
public import FroehlichSpencer.FS82.Surface.DualCellAxes
public import FroehlichSpencer.FS82.Surface.DualCellDegree
public import FroehlichSpencer.FS82.Surface.DualVertices
public import FroehlichSpencer.FS82.Surface.LatticeCoord
public import FroehlichSpencer.FS82.Surface.LatticeCell
public import FroehlichSpencer.FS82.Surface.RealLatticeChain
public import FroehlichSpencer.FS82.Surface.DualEmbedCoordC1
public import FroehlichSpencer.FS82.Surface.DualCellEmbeddingC1

/-! FS82 source definition statement -/

@[expose] public section

open scoped BigOperators
open Filter

namespace FroehlichSpencer.FS82.Surface

noncomputable def lambdaStarVertexRestriction (R : RectBox4) :
    RealLatticeChain →ₗ[ℝ] EuclideanSpace ℝ (DualVertices R) where
  toFun q := WithLp.toLp 2 fun v => q (dualCellEmbeddingC1 R v.1)
  map_add' q q' := by ext v; rfl
  map_smul' a q := by ext v; simp [smul_eq_mul]

end FroehlichSpencer.FS82.Surface

end
