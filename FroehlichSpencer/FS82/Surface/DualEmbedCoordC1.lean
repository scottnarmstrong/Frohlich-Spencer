/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib
public import FroehlichSpencer.FS82.Surface.RectBox4
public import FroehlichSpencer.FS82.Surface.DualCoord
public import FroehlichSpencer.FS82.Surface.LatticeCoord

/-! FS82 source definition statement -/

@[expose] public section

open scoped BigOperators
open Filter

namespace FroehlichSpencer.FS82.Surface

noncomputable def dualEmbedCoordC1 (R : RectBox4) (i : Fin 4) :
    DualCoord R i ↪ LatticeCoord where
  toFun := fun x => match x with
    | Sum.inl v => Sum.inl (R.origin i + v.val + 1)
    | Sum.inr e => Sum.inr (R.origin i + e.val)
  inj' := by
    intro x y h
    cases x with
    | inl x =>
      cases y with
      | inl y =>
        simp only [Sum.inl.injEq] at h
        have hv : (x.val : ℤ) = y.val := by omega
        exact congrArg Sum.inl (Fin.ext (by exact_mod_cast hv))
      | inr y => cases h
    | inr x =>
      cases y with
      | inl y => cases h
      | inr y =>
        simp only [Sum.inr.injEq] at h
        have hv : (x.val : ℤ) = y.val := Int.add_left_cancel h
        exact congrArg Sum.inr (Fin.ext (by exact_mod_cast hv))

end FroehlichSpencer.FS82.Surface

end
