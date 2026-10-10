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
public import FroehlichSpencer.FS82.Surface.DualLinks
public import FroehlichSpencer.FS82.Surface.LatticeCoord
public import FroehlichSpencer.FS82.Surface.LatticeCell
public import FroehlichSpencer.FS82.Surface.DualEmbedCoordC1
public import FroehlichSpencer.FS82.Surface.DualCellEmbeddingC1
public import FroehlichSpencer.FS82.Surface.LambdaStarEmbeddingC1
public import FroehlichSpencer.FS82.Surface.LatticeVertices4
public import FroehlichSpencer.FS82.Surface.LatticePotentialGradient
public import FroehlichSpencer.FS82.Surface.LatticePotentialVertexCell
public import FroehlichSpencer.FS82.Surface.IsExteriorVertex
public import FroehlichSpencer.FS82.SourceInterface.SourceTheorems
public import FroehlichSpencer.FS82.Provider.GaugePotentialNormalization

/-! FS82 characterization theorem -/

-- FROZEN_ANCHOR_PREFIX_BEGIN
@[expose] public section

open scoped BigOperators
open Filter

namespace FroehlichSpencer.FS82.Surface

theorem normalizeIntegerGaugePotential_connectedExterior
    (R : RectBox4) (γ : Surface.LatticeVertices4 → ℤ)
    (hsupp : ∀ c : Surface.LatticeCell,
      Surface.latticePotentialGradient γ c ≠ 0 →
        c ∈ Set.range (Surface.lambdaStarEmbeddingC1 R)) :
    ∃ γ₀ : Surface.LatticeVertices4 → ℤ,
      (∀ c : Surface.LatticeCell,
        Surface.latticePotentialGradient γ₀ c =
          Surface.latticePotentialGradient γ c) ∧
      Set.Finite {x : Surface.LatticeVertices4 | γ₀ x ≠ 0} ∧
      (∀ x, γ₀ x ≠ 0 →
        ∃ v : DualVertices R,
          Surface.dualCellEmbeddingC1 R v.1 =
            Surface.latticePotentialVertexCell x) ∧
      (∀ x, Surface.isExteriorVertex R x → γ₀ x = 0) ∧
      ∀ η : Surface.LatticeVertices4 → ℤ,
        (∀ c : Surface.LatticeCell,
          Surface.latticePotentialGradient η c =
            Surface.latticePotentialGradient γ c) →
        (∀ x, Surface.isExteriorVertex R x → η x = 0) → η = γ₀ :=
  -- FROZEN_ANCHOR_PROOF_BEGIN

  by exact FroehlichSpencer.FS82.Provider.normalizeIntegerGaugePotential_connectedExterior R γ hsupp
  -- FROZEN_ANCHOR_PROOF_END


-- FROZEN_ANCHOR_SUFFIX_BEGIN
end FroehlichSpencer.FS82.Surface

end
-- FROZEN_ANCHOR_SUFFIX_END
