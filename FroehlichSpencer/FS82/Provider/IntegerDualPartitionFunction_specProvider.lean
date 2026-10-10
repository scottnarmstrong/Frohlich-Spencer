/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib
public import FroehlichSpencer.FS82.Surface.ExistsUnique_integerDualPartitionFunction
public import FroehlichSpencer.FS82.Surface.IntegerDualPartitionFunction
public import FroehlichSpencer.FS82.Surface.RectBox4
public import FroehlichSpencer.FS82.Surface.DualCoord
public import FroehlichSpencer.FS82.Surface.DualCell
public import FroehlichSpencer.FS82.Surface.DualCellAxes
public import FroehlichSpencer.FS82.Surface.DualCellDegree
public import FroehlichSpencer.FS82.Surface.DualLinks
public import FroehlichSpencer.FS82.Surface.LatticeCoord
public import FroehlichSpencer.FS82.Surface.LatticeCell
public import FroehlichSpencer.FS82.Surface.LatticeChain
public import FroehlichSpencer.FS82.Surface.DualEmbedCoordC1
public import FroehlichSpencer.FS82.Surface.DualCellEmbeddingC1
public import FroehlichSpencer.FS82.Surface.LambdaStarEmbeddingC1
public import FroehlichSpencer.FS82.Surface.LatticeIsEdge
public import FroehlichSpencer.FS82.Surface.LatticeRankBefore
public import FroehlichSpencer.FS82.Surface.LatticeBasis
public import FroehlichSpencer.FS82.Surface.LatticeEdgeCell
public import FroehlichSpencer.FS82.Surface.LatticeCoboundaryBasis
public import FroehlichSpencer.FS82.Surface.LatticeCoboundary
public import FroehlichSpencer.FS82.Surface.IntegerDualField
public import FroehlichSpencer.FS82.Surface.LatticeVertices4
public import FroehlichSpencer.FS82.Surface.LatticePotentialGradient
public import FroehlichSpencer.FS82.Surface.SourceIntegerGaugeRelation
public import FroehlichSpencer.FS82.Surface.LambdaStarIntegerZeroExtension
public import FroehlichSpencer.FS82.Surface.IntegerLatticeCurl
public import FroehlichSpencer.FS82.Surface.IntegerDualFieldWeight
public import FroehlichSpencer.FS82.Surface.SourceIntegerGaugeRelationSetoid
public import FroehlichSpencer.FS82.Surface.IntegerDualGaugeQuotient
public import FroehlichSpencer.FS82.Surface.IntegerDualGaugeWeight

@[expose] public section

open scoped BigOperators
open FroehlichSpencer.FS82.Surface
namespace FroehlichSpencer.FS82.Provider

theorem integerDualPartitionFunction_spec (R : RectBox4) (β : ℝ) (hβ : 0 < β) :
    HasSum (integerDualGaugeWeight R β hβ) (integerDualPartitionFunction R β hβ) ∧
      0 < integerDualPartitionFunction R β hβ ∧
      ∀ Z', HasSum (integerDualGaugeWeight R β hβ) Z' →
        Z' = integerDualPartitionFunction R β hβ := by
  have hchosen := Classical.choose_spec (existsUnique_integerDualPartitionFunction R β hβ).exists
  constructor
  · simpa only [integerDualPartitionFunction] using hchosen.1
  constructor
  · simpa only [integerDualPartitionFunction] using hchosen.2
  · intro Z' hZ'
    have hsum : Z' = Classical.choose (existsUnique_integerDualPartitionFunction R β hβ).exists :=
      HasSum.unique hZ' hchosen.1
    simpa only [integerDualPartitionFunction] using hsum

end FroehlichSpencer.FS82.Provider

end
