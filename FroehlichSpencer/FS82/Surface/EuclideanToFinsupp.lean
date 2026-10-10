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

noncomputable def euclideanToFinsupp (R : RectBox4) :
    RealDualField R →ₗ[ℝ] LambdaStarRealChain R where
  toFun x := (Finsupp.linearEquivFunOnFinite ℝ ℝ (DualLinks R)).symm x.ofLp
  map_add' x y := by
    apply (Finsupp.linearEquivFunOnFinite ℝ ℝ (DualLinks R)).injective
    simp only [map_add, LinearEquiv.apply_symm_apply, WithLp.ofLp_add]
  map_smul' a x := by
    apply (Finsupp.linearEquivFunOnFinite ℝ ℝ (DualLinks R)).injective
    simp only [map_smul, LinearEquiv.apply_symm_apply, WithLp.ofLp_smul, RingHom.id_apply]

end FroehlichSpencer.FS82.Surface

end
