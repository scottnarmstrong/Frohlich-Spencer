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
public import FroehlichSpencer.FS82.Surface.DualLinks
public import FroehlichSpencer.FS82.Surface.LatticeCoord
public import FroehlichSpencer.FS82.Surface.LatticeCell
public import FroehlichSpencer.FS82.Surface.DualEmbedCoordC1
public import FroehlichSpencer.FS82.Surface.DualCellEmbeddingC1
public import FroehlichSpencer.FS82.Surface.LambdaStarEmbeddingC1
public import FroehlichSpencer.FS82.Surface.IntegerDualField
public import FroehlichSpencer.FS82.Surface.LatticeVertices4
public import FroehlichSpencer.FS82.Surface.LatticePotentialGradient
public import FroehlichSpencer.FS82.Surface.SourceIntegerGaugeRelation
public import FroehlichSpencer.FS82.Surface.SourceIntegerGaugeRelationSetoid
public import FroehlichSpencer.FS82.Surface.IntegerDualGaugeQuotient

/-! FS82 source definition statement -/

@[expose] public section

open scoped BigOperators
open Filter

namespace FroehlichSpencer.FS82.Surface

instance integerDualGaugeQuotientMeasurableSpace (R : RectBox4) :
    MeasurableSpace (IntegerDualGaugeQuotient R) := ⊤

end FroehlichSpencer.FS82.Surface

end
