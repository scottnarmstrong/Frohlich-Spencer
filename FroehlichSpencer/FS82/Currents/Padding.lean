/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Currents.Expansion

/-!
# FS82: assignment-independent finite padding for the Lemma 2 branches

The recursive proof lowers every branch weight by at most a factor `1/6` per
collision. This gives a finite bound on the number of terminal branches that
depends only on the size of the cubical link carrier, not on the mode values.
-/

public section

open scoped BigOperators

namespace FroehlichSpencer.FS82.Currents


/-- The padding width depends only on the finite cubical link carrier. -/
@[expose] noncomputable def currentExpansionPaddingSize (B : Cubical.Box 4) : ℕ :=
  6 ^ Fintype.card (Link B)

/--
Choose the fixed-frequency family.

Its branch list may depend on the
integer mode assignment, but the proved cardinality bound below supplies a
single assignment-independent finite index type.
-/
@[expose] noncomputable def chooseFixedFrequencyExpansion
    {B : Cubical.Box 4} (z : ℤ → ℝ) (hz : ∀ n, 0 ≤ z n)
    (hzpos : ∀ n, 0 < n → 0 < z n)
    (q : Link B → ℤ) (hq : ∀ e, q e ≠ 0) :
    List (CurrentExpansionTerm B) :=
  Classical.choose
    (exists_fixedFrequencySeparatedCurrentExpansion_withLineageActivity
      q z hq hz hzpos)

theorem chooseFixedFrequencyExpansion_spec
    {B : Cubical.Box 4} (z : ℤ → ℝ) (hz : ∀ n, 0 ≤ z n)
    (hzpos : ∀ n, 0 < n → 0 < z n)
    (q : Link B → ℤ) (hq : ∀ e, q e ≠ 0) :
    IsFixedFrequencyCurrentExpansion q z
        (chooseFixedFrequencyExpansion z hz hzpos q hq) ∧
      (chooseFixedFrequencyExpansion z hz hzpos q hq).length ≤
        currentExpansionPaddingSize B :=
  Classical.choose_spec
    (exists_fixedFrequencySeparatedCurrentExpansion_withLineageActivity
      q z hq hz hzpos)


end FroehlichSpencer.FS82.Currents

end
