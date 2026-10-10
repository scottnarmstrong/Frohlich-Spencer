/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.PinnedCharges.BoundaryIsolationNeighbor

/-!
Facts about `euclideanSetDistance` and `euclideanSetDiameter` on nonempty finite sets of sites:
the set distance is the minimum of the site distances, it decreases when the sets grow, the distance
of a union is at least the smaller of the two distances, distinct lattice sites are at distance at
least one, and a diameter is either zero or at least one.

The support of `a ± b` for
support-disjoint `a, b` is the union of the supports.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic.PinnedCharges.SelectionG

open FroehlichSpencer.BKT

variable {L : ℕ}

theorem siteDist_nonneg (x y : Site L) : 0 ≤ euclideanSiteDistance x y :=
  Real.sqrt_nonneg _

theorem siteDist_self (x : Site L) : euclideanSiteDistance x x = 0 := by
  simp [euclideanSiteDistance]

theorem siteDist_comm (x y : Site L) : euclideanSiteDistance x y = euclideanSiteDistance y x := by
  unfold euclideanSiteDistance
  congr 1
  ring

theorem one_le_siteDist {x y : Site L} (h : x ≠ y) : 1 ≤ euclideanSiteDistance x y := by
  unfold euclideanSiteDistance
  rw [show (1 : ℝ) = Real.sqrt 1 by simp]
  apply Real.sqrt_le_sqrt
  by_cases h1 : x.1 = y.1
  · have h2 : x.2 ≠ y.2 := fun h2 => h (Prod.ext h1 h2)
    have h2v : x.2.val ≠ y.2.val := fun h' => h2 (Fin.ext h')
    have hsq : (1 : ℝ) ≤ ((x.2.val : ℝ) - y.2.val) ^ 2 := by
      rcases lt_or_gt_of_ne h2v with hlt | hlt
      · have : (x.2.val : ℝ) + 1 ≤ y.2.val := by exact_mod_cast hlt
        nlinarith
      · have : (y.2.val : ℝ) + 1 ≤ x.2.val := by exact_mod_cast hlt
        nlinarith
    nlinarith [sq_nonneg ((x.1.val : ℝ) - y.1.val)]
  · have h1v : x.1.val ≠ y.1.val := fun h' => h1 (Fin.ext h')
    have hsq : (1 : ℝ) ≤ ((x.1.val : ℝ) - y.1.val) ^ 2 := by
      rcases lt_or_gt_of_ne h1v with hlt | hlt
      · have : (x.1.val : ℝ) + 1 ≤ y.1.val := by exact_mod_cast hlt
        nlinarith
      · have : (y.1.val : ℝ) + 1 ≤ x.1.val := by exact_mod_cast hlt
        nlinarith
    nlinarith [sq_nonneg ((x.2.val : ℝ) - y.2.val)]

theorem setDist_le_siteDist {s t : Finset (Site L)} {x y : Site L} (hx : x ∈ s) (hy : y ∈ t) :
    euclideanSetDistance s t ≤ euclideanSiteDistance x y := by
  have hprod : (s.product t).Nonempty := ⟨(x, y), Finset.mem_product.mpr ⟨hx, hy⟩⟩
  unfold euclideanSetDistance
  rw [dite_eq_left hprod]
  exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨(x, y), Finset.mem_product.mpr ⟨hx, hy⟩, rfl⟩)

theorem le_setDist {s t : Finset (Site L)} (hs : s.Nonempty) (ht : t.Nonempty) {c : ℝ}
    (h : ∀ x ∈ s, ∀ y ∈ t, c ≤ euclideanSiteDistance x y) : c ≤ euclideanSetDistance s t := by
  have hprod : (s.product t).Nonempty := by
    obtain ⟨x, hx⟩ := hs
    obtain ⟨y, hy⟩ := ht
    exact ⟨(x, y), Finset.mem_product.mpr ⟨hx, hy⟩⟩
  unfold euclideanSetDistance
  rw [dite_eq_left hprod]
  refine Finset.le_min' _ _ _ fun r hr => ?_
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hr
  exact h p.1 (Finset.mem_product.mp hp).1 p.2 (Finset.mem_product.mp hp).2

theorem setDist_nonneg (s t : Finset (Site L)) : 0 ≤ euclideanSetDistance s t := by
  by_cases hs : s.Nonempty
  · by_cases ht : t.Nonempty
    · exact le_setDist hs ht fun x _ y _ => siteDist_nonneg x y
    · simp [euclideanSetDistance, Finset.not_nonempty_iff_eq_empty.mp ht]
  · simp [euclideanSetDistance, Finset.not_nonempty_iff_eq_empty.mp hs]

theorem setDist_comm (s t : Finset (Site L)) :
    euclideanSetDistance s t = euclideanSetDistance t s := by
  by_cases hs : s.Nonempty
  · by_cases ht : t.Nonempty
    · refine le_antisymm ?_ ?_
      · refine le_setDist ht hs fun y hy x hx => ?_
        rw [siteDist_comm]
        exact setDist_le_siteDist hx hy
      · refine le_setDist hs ht fun x hx y hy => ?_
        rw [siteDist_comm]
        exact setDist_le_siteDist hy hx
    · simp [euclideanSetDistance, Finset.not_nonempty_iff_eq_empty.mp ht]
  · simp [euclideanSetDistance, Finset.not_nonempty_iff_eq_empty.mp hs]

/-- Enlarging the two sets can only decrease the distance. -/
theorem setDist_le_of_subset {s t s' t' : Finset (Site L)} (hs : s' ⊆ s) (ht : t' ⊆ t)
    (hs' : s'.Nonempty) (ht' : t'.Nonempty) :
    euclideanSetDistance s t ≤ euclideanSetDistance s' t' :=
  le_setDist hs' ht' fun _ hx _ hy => setDist_le_siteDist (hs hx) (ht hy)

/-- The distance from a union is at least the smaller of the two distances. -/
theorem min_le_setDist_union {s s' t : Finset (Site L)} (hs : s.Nonempty) (ht : t.Nonempty) :
    min (euclideanSetDistance s t) (euclideanSetDistance s' t) ≤
      euclideanSetDistance (s ∪ s') t := by
  classical
  refine le_setDist (hs.mono Finset.subset_union_left) ht fun x hx y hy => ?_
  rcases Finset.mem_union.mp hx with hx | hx
  · exact (min_le_left _ _).trans (setDist_le_siteDist hx hy)
  · exact (min_le_right _ _).trans (setDist_le_siteDist hx hy)

theorem siteDist_le_diam {s : Finset (Site L)} {x y : Site L} (hx : x ∈ s) (hy : y ∈ s) :
    euclideanSiteDistance x y ≤ euclideanSetDiameter s := by
  have hprod : (s.product s).Nonempty := ⟨(x, y), Finset.mem_product.mpr ⟨hx, hy⟩⟩
  unfold euclideanSetDiameter
  rw [dite_eq_left hprod]
  exact Finset.le_max' ((s.product s).image fun p : Site L × Site L => euclideanSiteDistance p.1 p.2)
    (euclideanSiteDistance x y)
    (Finset.mem_image.mpr ⟨(x, y), Finset.mem_product.mpr ⟨hx, hy⟩, rfl⟩)

/-- The distance between two nonempty parts of a set is at most its diameter. -/
theorem setDist_le_diam {s s₁ s₂ : Finset (Site L)} (h₁ : s₁ ⊆ s) (h₂ : s₂ ⊆ s)
    (hs₁ : s₁.Nonempty) (hs₂ : s₂.Nonempty) :
    euclideanSetDistance s₁ s₂ ≤ euclideanSetDiameter s := by
  obtain ⟨x, hx⟩ := hs₁
  obtain ⟨y, hy⟩ := hs₂
  exact (setDist_le_siteDist hx hy).trans (siteDist_le_diam (h₁ hx) (h₂ hy))

theorem diam_nonneg (s : Finset (Site L)) : 0 ≤ euclideanSetDiameter s := by
  by_cases hs : s.Nonempty
  · obtain ⟨x, hx⟩ := hs
    exact (siteDist_nonneg x x).trans (siteDist_le_diam hx hx)
  · simp [euclideanSetDiameter, Finset.not_nonempty_iff_eq_empty.mp hs]

/-- A lattice diameter is zero or at least one. -/
theorem diam_eq_zero_or_one_le (s : Finset (Site L)) :
    euclideanSetDiameter s = 0 ∨ 1 ≤ euclideanSetDiameter s := by
  by_cases h : ∃ x ∈ s, ∃ y ∈ s, x ≠ y
  · obtain ⟨x, hx, y, hy, hxy⟩ := h
    exact Or.inr ((one_le_siteDist hxy).trans (siteDist_le_diam hx hy))
  · push Not at h
    left
    by_cases hs : (s.product s).Nonempty
    · unfold euclideanSetDiameter
      rw [dite_eq_left hs]
      obtain ⟨p, hp, hval⟩ := Finset.mem_image.mp (Finset.max'_mem
        ((s.product s).image fun p : Site L × Site L => euclideanSiteDistance p.1 p.2)
        (Finset.image_nonempty.mpr hs))
      rw [← hval, h p.1 (Finset.mem_product.mp hp).1 p.2 (Finset.mem_product.mp hp).2,
        siteDist_self]
    · rw [euclideanSetDiameter, dite_eq_right hs]

/-! ### Supports of sums -/

theorem chargeSupport_add_smul {a b : ChargeDensity L}
    (hdisj : Disjoint (chargeSupport a) (chargeSupport b)) {ε : ℤ} (hε : ε = 1 ∨ ε = -1) :
    chargeSupport (a + ε • b) = chargeSupport a ∪ chargeSupport b := by
  ext x
  simp only [chargeSupport, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hx : a x = 0 ∨ b x = 0 := by
    by_contra h
    push Not at h
    have ha : x ∈ chargeSupport a := by simp [chargeSupport, h.1]
    have hb : x ∈ chargeSupport b := by simp [chargeSupport, h.2]
    exact Finset.disjoint_left.mp hdisj ha hb
  rcases hε with rfl | rfl <;> rcases hx with h | h <;> simp [h]

theorem add_smul_eq_left {a b : ChargeDensity L}
    (hdisj : Disjoint (chargeSupport a) (chargeSupport b)) (ε : ℤ) {x : Site L}
    (hx : x ∈ chargeSupport a) : (a + ε • b) x = a x := by
  have hb : b x = 0 := by
    by_contra h
    exact Finset.disjoint_left.mp hdisj hx (by simp [chargeSupport, h])
  simp [hb]

theorem add_smul_eq_right {a b : ChargeDensity L}
    (hdisj : Disjoint (chargeSupport a) (chargeSupport b)) (ε : ℤ) {x : Site L}
    (hx : x ∈ chargeSupport b) : (a + ε • b) x = ε * b x := by
  have ha : a x = 0 := by
    by_contra h
    exact Finset.disjoint_left.mp hdisj (by simp [chargeSupport, h]) hx
  simp [ha]

end FroehlichSpencer.BKT.Generic.PinnedCharges.SelectionG

end
