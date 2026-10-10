/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Currents.ActivityLineage
public import FroehlichSpencer.FS82.Currents.Geometry

/-!
# FS82 cubical current activity bounds

The finite-link neighborhood specializes the generic lineage activity bound
to Euclidean distance between dual-link supports.
-/

public section

open scoped BigOperators

namespace FroehlichSpencer.FS82.Currents


@[expose] noncomputable def oneNeighborSet {B : Cubical.Box 4}
    (P : Finset (Link B)) : Finset (Link B) :=
  Finset.univ.filter fun e => ∃ f ∈ P, linkDistance e f ≤ 1

theorem linkDistance_self {B : Cubical.Box 4} (e : Link B) :
    linkDistance e e = 0 := by
  exact linkDistance_zero_of_shared_vertex e e e.base (Or.inl rfl) (Or.inl rfl)

theorem activityNeighborhood_eq_oneNeighborSet {B : Cubical.Box 4}
    (P : Finset (Link B)) :
    ActivityLineage.activityNeighborhood Finset.univ P
      (fun e f => linkDistance e f ≤ 1) = oneNeighborSet P := by
  classical
  ext e
  simp only [ActivityLineage.activityNeighborhood, oneNeighborSet,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro (heP | ⟨f, hfP, hdist⟩)
    · exact ⟨e, heP, by rw [linkDistance_self]; norm_num⟩
    · exact ⟨f, hfP, hdist⟩
  · rintro ⟨f, hfP, hdist⟩
    exact Or.inr ⟨f, hfP, hdist⟩


theorem cubical_currentActivity_bound {B : Cubical.Box 4}
    {h : ActivityLineage (Link B)}
    (hg : ActivityLineage.Good (fun e f => linkDistance e f ≤ 1) h)
    (q : Link B → ℤ) (hq : ∀ e ∈ h.all, q e ≠ 0)
    (z : ℤ → ℝ) (hz : ∀ n, 0 ≤ z n) :
    ActivityLineage.coefficient (fun e => z (abs (q e))) h ≤
      (3 : ℝ) ^ (oneNeighborSet
        (currentSupport (ActivityLineage.value q h))).card *
        ∏ e ∈ currentSupport (ActivityLineage.value q h),
          z (abs (ActivityLineage.value q h e)) := by
  have hbound := ActivityLineage.coefficient_le_three_pow_activityNeighborhood
    hg (fun e f h => by simpa [linkDistance_symm] using h)
    Finset.univ (fun _ _ => Finset.mem_univ _) (fun e => z (abs (q e)))
    (fun e => hz (abs (q e)))
  have hsupp := ActivityLineage.currentSupport_value_eq_active hg q hq
  rw [activityNeighborhood_eq_oneNeighborSet] at hbound
  rw [← hsupp] at hbound
  have hprod :
      (∏ e ∈ currentSupport (ActivityLineage.value q h), z (abs (q e))) =
        ∏ e ∈ currentSupport (ActivityLineage.value q h),
          z (abs (ActivityLineage.value q h e)) := by
    apply Finset.prod_congr rfl
    intro e he
    have heActive : e ∈ h.active := by rw [← hsupp]; exact he
    have hfreq := ActivityLineage.value_abs_eq_input_abs_on_active hg q hq heActive
    exact congrArg z hfreq.symm
  rw [hprod] at hbound
  exact hbound

end FroehlichSpencer.FS82.Currents
