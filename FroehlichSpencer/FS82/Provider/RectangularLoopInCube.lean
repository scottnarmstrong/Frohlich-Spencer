/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.PrimalInterface.LoopBridge

/-! Provider of the gate `rectangularLoop_subset_centredCube` of the perimeter surface. -/

public section

namespace FroehlichSpencer.FS82.Provider

theorem rectangularLoop_subset_centredCube (L T N : ℕ) (hN : 0 < N) (hL : L ≤ N) (hT : T ≤ N)
    (c : Surface.LatticeCell) (hc : c ∈ (Surface.rectangularLoop L T).support) :
    ∃ ℓ : Surface.PrimalLinks (Surface.centredCube N hN),
      Surface.primalCellEmbedding (Surface.centredCube N hN) ℓ.1 = c :=
  PrimalInterface.rectangularLoop_subset_centredCube L T N hN hL hT c hc

end FroehlichSpencer.FS82.Provider

end
