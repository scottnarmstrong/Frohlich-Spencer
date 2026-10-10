/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import FroehlichSpencer.BKT.Charges.BasicLemmaIteration
public import FroehlichSpencer.BKT.Charges.EnsembleDefinitions

/-! # Numerical conversion in the Basic Lemma coefficient bounds

This module records the arithmetic converting lineage multiplier counts into
the coarse power of three and the reviewed exponential constant. The geometric
neighborhood and iteration-history estimates supplying the hypotheses are
separate. -/

@[expose] public section

namespace FroehlichSpencer.BKT

/-- The numerical comparison used for the refined constant. -/
theorem log_three_lt_twentyfive_nineteenths :
    Real.log 3 < (25 : ℝ) / 19 := by
  apply (Real.log_lt_iff_lt_exp (by norm_num)).2
  have hquarter : (5 : ℝ) / 4 ≤ Real.exp (1 / 4 : ℝ) := by
    have h := Real.add_one_le_exp (1 / 4 : ℝ)
    norm_num at h ⊢
    exact h
  have hsix : (25 : ℝ) / 19 ≤ Real.exp (6 / 19 : ℝ) := by
    have h := Real.add_one_le_exp (6 / 19 : ℝ)
    norm_num at h ⊢
    exact h
  have hone : ((5 : ℝ) / 4) ^ 4 ≤ Real.exp 1 := by
    calc
      ((5 : ℝ) / 4) ^ 4 ≤ Real.exp (1 / 4 : ℝ) ^ 4 := by
        gcongr
      _ = Real.exp 1 := by
        rw [← Real.exp_nat_mul]
        norm_num
  have hmul : (3 : ℝ) < (((5 : ℝ) / 4) ^ 4) * ((25 : ℝ) / 19) := by
    norm_num
  calc
    (3 : ℝ) < (((5 : ℝ) / 4) ^ 4) * ((25 : ℝ) / 19) := hmul
    _ ≤ Real.exp 1 * Real.exp (6 / 19 : ℝ) := by
      calc
        ((5 : ℝ) / 4) ^ 4 * ((25 : ℝ) / 19) ≤
            Real.exp 1 * ((25 : ℝ) / 19) :=
          mul_le_mul_of_nonneg_right hone (by positivity)
        _ ≤ Real.exp 1 * Real.exp (6 / 19 : ℝ) :=
          mul_le_mul_of_nonneg_left hsix (by positivity)
    _ = Real.exp (1 + 6 / 19) := by rw [← Real.exp_add]
    _ = Real.exp ((25 : ℝ) / 19) := by norm_num

/-- Every multiplier count `m ≤ n` contributes at most `3^n`. -/
theorem coarse_multiplier_bound (m n : ℕ) (hmn : m ≤ n) :
    (3 : ℝ) ^ m ≤ 3 ^ n := by
  exact_mod_cast (Nat.pow_le_pow_right (by omega : 1 ≤ 3) hmn)

/-- The refined numerical conversion: `n ≤ 76 A` implies
`3^m ≤ exp (100 A)`. -/
theorem refined_multiplier_bound (m A : ℕ) (hm : m ≤ 76 * A) :
    (3 : ℝ) ^ m ≤ Real.exp (100 * A) := by
  have hmR : (m : ℝ) ≤ 76 * A := by exact_mod_cast hm
  have hlog := log_three_lt_twentyfive_nineteenths.le
  have hexpArg : (m : ℝ) * Real.log 3 ≤ 100 * A := by
    calc
      (m : ℝ) * Real.log 3 ≤ (m : ℝ) * ((25 : ℝ) / 19) :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
      _ ≤ (76 * A : ℝ) * ((25 : ℝ) / 19) := by
        exact mul_le_mul_of_nonneg_right hmR (by positivity)
      _ = 100 * A := by ring
  calc
    (3 : ℝ) ^ m = Real.exp ((m : ℝ) * Real.log 3) := by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
    _ ≤ Real.exp (100 * A) := Real.exp_le_exp.mpr hexpArg

/-- Multiplying either numerical estimate by any nonnegative coefficient
product preserves the estimate. -/
theorem coarse_weighted_multiplier_bound (m n : ℕ) (hmn : m ≤ n)
    (P : ℝ) (hP : 0 ≤ P) :
    (3 : ℝ) ^ m * P ≤ 3 ^ n * P :=
  mul_le_mul_of_nonneg_right (coarse_multiplier_bound m n hmn) hP

/-- Weighted form of the refined coefficient multiplier estimate. -/
theorem refined_weighted_multiplier_bound (m A : ℕ) (hm : m ≤ 76 * A)
    (P : ℝ) (hP : 0 ≤ P) :
    (3 : ℝ) ^ m * P ≤ Real.exp (100 * A) * P :=
  mul_le_mul_of_nonneg_right (refined_multiplier_bound m A hm) hP

/-- The coarse L4.3 coefficient estimate follows once its branch history
gives the multiplier formula and the lineage charge count. -/
theorem coarse_absolute_coefficient_bound (Kout P : ℝ) (m n : ℕ)
    (hformula : |Kout| = (3 : ℝ) ^ m * P) (hP : 0 ≤ P) (hmn : m ≤ n) :
    |Kout| ≤ 3 ^ n * P := by
  rw [hformula]
  exact coarse_weighted_multiplier_bound m n hmn P hP

/-- The refined L4.3 coefficient estimate follows once the branch history
has multiplier at most `76 A`. The constant is exactly the reviewed `100`. -/
theorem refined_absolute_coefficient_bound (Kout P : ℝ) (m A : ℕ)
    (hformula : |Kout| = (3 : ℝ) ^ m * P) (hP : 0 ≤ P)
    (hm : m ≤ 76 * A) :
    |Kout| ≤ Real.exp (100 * A) * P := by
  rw [hformula]
  exact refined_weighted_multiplier_bound m A hm P hP

/-- The lineage-charging identity implies the coarse count bound. Here `P`
is the output lineage, `H` is the set of distinct charged input leaves, and
`N` is the set of input leaves within the selected conflict radius. -/
theorem lineageCharge_multiplier_le_neighborhood_sub_one {α : Type*}
    [DecidableEq α] (P H N : Finset α) (m : ℕ)
    (hPne : P.Nonempty) (hPN : P ⊆ N) (hHN : H ⊆ N \ P)
    (hm : m = P.card - 1 + H.card) :
    m ≤ N.card - 1 := by
  have hdisj : Disjoint P H := by
    apply Finset.disjoint_left.mpr
    intro a haP haH
    exact (Finset.mem_sdiff.mp (hHN haH)).2 haP
  have hcard : (P ∪ H).card = P.card + H.card := Finset.card_union_of_disjoint hdisj
  have hsub : P ∪ H ⊆ N := by
    intro a ha
    rcases Finset.mem_union.mp ha with haP | haH
    · exact hPN haP
    · exact (Finset.mem_sdiff.mp (hHN haH)).1
  have hle : P.card + H.card ≤ N.card := by
    rw [← hcard]
    exact Finset.card_le_card hsub
  have hPcard : 1 ≤ P.card := Finset.card_pos.mpr hPne
  omega

/-- The refined multiplier bound follows from the lineage charge identity and
the geometric estimate `|N| ≤ 76 A`. -/
theorem lineageCharge_refined_multiplier_bound {α : Type*} [DecidableEq α]
    (P H N : Finset α) (m A : ℕ)
    (hPne : P.Nonempty) (hPN : P ⊆ N) (hHN : H ⊆ N \ P)
    (hm : m = P.card - 1 + H.card) (hNA : N.card ≤ 76 * A) :
    (3 : ℝ) ^ m ≤ Real.exp (100 * A) := by
  have hmN := lineageCharge_multiplier_le_neighborhood_sub_one
    P H N m hPne hPN hHN hm
  exact refined_multiplier_bound m A (by omega)

/-- Coefficient-level coarse estimate from the lineage charging data. -/
theorem lineageCharge_coarse_coefficient_bound {α : Type*} [DecidableEq α]
    (Kout product : ℝ) (P H N : Finset α) (m : ℕ)
    (hformula : |Kout| = (3 : ℝ) ^ m * product)
    (hproduct : 0 ≤ product) (hPne : P.Nonempty) (hPN : P ⊆ N)
    (hHN : H ⊆ N \ P) (hm : m = P.card - 1 + H.card) :
    |Kout| ≤ 3 ^ N.card * product := by
  exact coarse_absolute_coefficient_bound Kout product m N.card hformula
    hproduct (by
      have hmN := lineageCharge_multiplier_le_neighborhood_sub_one
        P H N m hPne hPN hHN hm
      omega)

/-- Coefficient-level refined estimate from the lineage data and the
geometric neighborhood bound. -/
theorem lineageCharge_refined_coefficient_bound {α : Type*} [DecidableEq α]
    (Kout product : ℝ) (P H N : Finset α) (m A : ℕ)
    (hformula : |Kout| = (3 : ℝ) ^ m * product)
    (hproduct : 0 ≤ product) (hPne : P.Nonempty) (hPN : P ⊆ N)
    (hHN : H ⊆ N \ P) (hm : m = P.card - 1 + H.card)
    (hNA : N.card ≤ 76 * A) :
    |Kout| ≤ Real.exp (100 * A) * product := by
  exact refined_absolute_coefficient_bound Kout product m A hformula hproduct
    (by
      have hmN := lineageCharge_multiplier_le_neighborhood_sub_one
        P H N m hPne hPN hHN hm
      omega)

end FroehlichSpencer.BKT

end
