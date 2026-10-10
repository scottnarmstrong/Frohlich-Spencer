/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Probability.ProbabilityMassFunction.Basic
public import FroehlichSpencer.FS82.SurfaceInfinite.SourceLatticeShift
public import FroehlichSpencer.FS82.SurfaceInfinite.SourceShiftBoxSet
public import FroehlichSpencer.FS82.SurfaceInfinite.SourceShiftBoxSetFinite
public import FroehlichSpencer.FS82.SurfaceInfinite.SourceShiftBox

@[expose] public section

open MeasureTheory
open Filter Topology
open scoped ComplexConjugate

namespace FroehlichSpencer.FS82.SurfaceInfinite

noncomputable section

noncomputable def sourceShiftUniform (n : ℕ) : PMF SourceLatticeShift := by
  classical
  letI := (sourceShiftBoxSet_finite n).to_subtype
  let S := {a : SourceLatticeShift // a ∈ sourceShiftBox n}
  let m := Fintype.card S
  have hm : 0 < m := Fintype.card_pos_iff.mpr ⟨⟨0, by
    rw [sourceShiftBox, Set.Finite.mem_toFinset (sourceShiftBoxSet_finite n)]
    intro i
    simp⟩⟩
  let p : PMF S := PMF.ofFintype (fun _ => ((m : ℕ) : ENNReal)⁻¹) (by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact ENNReal.mul_inv_cancel (by exact_mod_cast (Nat.ne_of_gt hm))
      (ENNReal.natCast_ne_top _))
  exact p.map Subtype.val

end
end FroehlichSpencer.FS82.SurfaceInfinite

end
