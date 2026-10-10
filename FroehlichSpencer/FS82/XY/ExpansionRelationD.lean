/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.XY.ActivityD
public import FroehlichSpencer.FS82.XY.SeparationD
public import FroehlichSpencer.FS82.XY.CurrentExpansionD
import all FroehlichSpencer.FS82.XY.CurrentExpansionD

/-!
# the expansion with the base-near collision relation

Its specialization there uses "common coface of degree `d − 1`".

That relation does not
separate the divergences of two currents (see `XY/SeparationD.lean`), so the expansion is taken
here with the relation `cellBaseNear` on the dual cells of degree `d − 2`, which contains both
"common coface" and "common face".

For every lineage `h` of a terminal state, with current
`J = lineageCurrent q h` and `L` cells:

* `lineage_extent`: the base points of the cells of `J` differ by at most `L − 1`;
* `lineage_disjoint`: distinct lineages of one state have disjoint supports, and no two of their
  cells are base-near (`lineage_separated`);
* `lineageCoefficient_le`: the coefficient is at most `3 ^ (6 ^ d · L) · ∏ z(|J_e|)`.

These are the geometric hypotheses of `DualD.AdmissibleFamily`, and the input of
`DualD.activity_envelope`.
-/

open scoped BigOperators

@[expose] public section

namespace FroehlichSpencer.FS82.XY.DualD

open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Currents
open FroehlichSpencer.FS82.XY.ExpansionD.Generic

variable {d : ℕ} {B : Box d}

/-- The collision relation of the expansion: base points at `ℓ^∞` distance at most one. -/
def baseNearRelation (B : Box d) (n : ℕ) : SymmetricCurrentRelation (DualDForm B n) where
  near a b := cellBaseNear a.1 b.1
  symmetric _ _ := ⟨cellBaseNear_symm, cellBaseNear_symm⟩

/-- **The expansion with the base-near relation.** -/
theorem exists_baseNearCurrentExpansion (n : ℕ) (q : DualDForm B n → ℤ) (z : ℤ → ℝ)
    (hz0 : z 0 = 0) (hz : ∀ k, 0 ≤ z k) (hzpos : ∀ k, 0 < k → 0 < z k) :
    ∃ T : List (CurrentExpansionTerm (DualDForm B n)),
      IsFixedFrequencyCurrentExpansion (baseNearRelation B n) q z T ∧
        T.length ≤ 6 ^ (currentSupport q).card :=
  exists_fixedFrequencySeparatedCurrentExpansion_withLineageActivity
    (baseNearRelation B n) q z hz0 hz hzpos

section Lineages

variable {n : ℕ} {q : DualDForm B n → ℤ} {z : ℤ → ℝ}
  {T : List (CurrentExpansionTerm (DualDForm B n))}
  (hT : IsFixedFrequencyCurrentExpansion (baseNearRelation B n) q z T)

include hT in
theorem lineage_support {t : CurrentExpansionTerm (DualDForm B n)} (ht : t ∈ T)
    {h : ActivityLineage (DualDForm B n)} (hh : h ∈ t.state) :
    currentSupport (lineageCurrent q h) = h.active := by
  obtain ⟨hgood, hq⟩ := (hT.2.2.1 t ht).1 h hh
  exact ActivityLineage.currentSupport_value_eq_active hgood q hq

include hT in
/-- The extent of a lineage current is at most its number of cells minus one. -/
theorem lineage_extent {t : CurrentExpansionTerm (DualDForm B n)} (ht : t ∈ T)
    {h : ActivityLineage (DualDForm B n)} (hh : h ∈ t.state) (e f : DualDForm B n)
    (he : lineageCurrent q h e ≠ 0) (hf : lineageCurrent q h f ≠ 0) (k : Fin d) :
    cellBase e.1 k + 1 ≤ cellBase f.1 k + currentLength (lineageCurrent q h) := by
  obtain ⟨hgood, _⟩ := (hT.2.2.1 t ht).1 h hh
  have hsupp := lineage_support hT ht hh
  have hea : e ∈ h.active := by
    rw [← hsupp]
    exact mem_currentSupport_iff.mpr he
  have hfa : f ∈ h.active := by
    rw [← hsupp]
    exact mem_currentSupport_iff.mpr hf
  unfold currentLength
  rw [hsupp]
  exact good_active_extent (near := (baseNearRelation B n).near) (fun _ _ h => h) hgood
    e hea f hfa k


include hT in
/-- **The coefficient of a lineage.** -/
theorem lineageCoefficient_le (hz : ∀ k, 0 ≤ z k)
    {t : CurrentExpansionTerm (DualDForm B n)} (ht : t ∈ T)
    {h : ActivityLineage (DualDForm B n)} (hh : h ∈ t.state) :
    lineageCoefficient q z h ≤
      (3 : ℝ) ^ (6 ^ d * currentLength (lineageCurrent q h)) *
        ∏ e ∈ currentSupport (lineageCurrent q h), z |lineageCurrent q h e| := by
  have hbound := hT.2.2.2.2.2.2.2 t ht h hh
  have hcard := card_activityNeighborhood_le (baseNearRelation B n).near (fun _ _ h => h)
    (currentSupport (lineageCurrent q h))
  have hprod : 0 ≤ ∏ e ∈ currentSupport (lineageCurrent q h), z |lineageCurrent q h e| :=
    Finset.prod_nonneg fun e _ => hz _
  refine hbound.trans (mul_le_mul_of_nonneg_right ?_ hprod)
  exact pow_le_pow_right₀ (by norm_num) hcard

end Lineages

end FroehlichSpencer.FS82.XY.DualD

end
