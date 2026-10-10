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
public import FroehlichSpencer.FS82.Surface.LambdaStarRealChain
public import FroehlichSpencer.FS82.Surface.RealDualField

/-! FS82 source definition statement -/

@[expose] public section

open scoped BigOperators
open Filter

namespace FroehlichSpencer.FS82.Surface

noncomputable def finsuppToEuclidean (R : RectBox4) :
    LambdaStarRealChain R →ₗ[ℝ] RealDualField R where
  toFun q := WithLp.toLp 2 (Finsupp.linearEquivFunOnFinite ℝ ℝ (DualLinks R) q)
  map_add' q r := by
    ext a
    simp only [WithLp.ofLp_add, Pi.add_apply]
    simp [Finsupp.linearEquivFunOnFinite]
  map_smul' c q := by
    ext a
    simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    simp [Finsupp.linearEquivFunOnFinite]

end FroehlichSpencer.FS82.Surface

end
