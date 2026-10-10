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
public import FroehlichSpencer.FS82.Surface.LatticeCoord
public import FroehlichSpencer.FS82.Surface.LatticeCell
public import FroehlichSpencer.FS82.Surface.DualEmbedCoordC1

/-! FS82 source definition statement -/

@[expose] public section

open scoped BigOperators
open Filter

namespace FroehlichSpencer.FS82.Surface

noncomputable def dualCellEmbeddingC1 (R : RectBox4) : DualCell R ↪ LatticeCell where
  toFun c i := dualEmbedCoordC1 R i (c i)
  inj' := by
    intro c₁ c₂ h
    funext i
    exact (dualEmbedCoordC1 R i).injective (congrFun h i)

end FroehlichSpencer.FS82.Surface

end
