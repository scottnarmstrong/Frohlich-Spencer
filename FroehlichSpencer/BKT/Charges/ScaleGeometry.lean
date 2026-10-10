/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Charges.EnsembleDefinitions
public import FroehlichSpencer.BKT.Charges.PatchIsolation
public import FroehlichSpencer.BKT.Charges.SquareDiameterBounds
import FroehlichSpencer.BKT.Surface.SquareFreeConnected
import FroehlichSpencer.BKT.Surface.SquarePeriodicConnected

/-! # Basic geometry of finite-set distances and scale ensembles

Realizing pairs for `squareDistance` and `squareDiameter`, symmetry, monotonicity,
uniform bounds by `2 * L`, positivity of distances between distinct points, and
monotonicity of scale ensembles in the separation threshold. -/

@[expose] public section

namespace FroehlichSpencer.BKT

theorem exists_squareDistance_eq (boundary : SquareBoundary) (L : ℕ)
    (s t : Finset (Fin L × Fin L)) (hs : s.Nonempty) (ht : t.Nonempty) :
    ∃ x ∈ s, ∃ y ∈ t, squareDistance boundary L s t = latticeDistance boundary L x y := by
  classical
  have hprod : (s.product t).Nonempty := by
    obtain ⟨a, ha⟩ := hs
    obtain ⟨b, hb⟩ := ht
    exact ⟨(a, b), Finset.mem_product.mpr ⟨ha, hb⟩⟩
  have hmem := Finset.min'_mem
    ((s.product t).image fun p => latticeDistance boundary L p.1 p.2)
    (Finset.image_nonempty.mpr hprod)
  obtain ⟨p, hp, hpe⟩ := Finset.mem_image.mp hmem
  rcases Finset.mem_product.mp hp with ⟨h1, h2⟩
  refine ⟨p.1, h1, p.2, h2, ?_⟩
  unfold squareDistance
  rw [dite_eq_left hprod]
  exact hpe.symm

theorem exists_squareDiameter_eq (boundary : SquareBoundary) (L : ℕ)
    (s : Finset (Fin L × Fin L)) (hs : s.Nonempty) :
    ∃ x ∈ s, ∃ y ∈ s, squareDiameter boundary L s = latticeDistance boundary L x y := by
  classical
  have hprod : (s.product s).Nonempty := by
    obtain ⟨a, ha⟩ := hs
    exact ⟨(a, a), Finset.mem_product.mpr ⟨ha, ha⟩⟩
  have hmem := Finset.max'_mem
    ((s.product s).image fun p => latticeDistance boundary L p.1 p.2)
    (Finset.image_nonempty.mpr hprod)
  obtain ⟨p, hp, hpe⟩ := Finset.mem_image.mp hmem
  rcases Finset.mem_product.mp hp with ⟨h1, h2⟩
  refine ⟨p.1, h1, p.2, h2, ?_⟩
  unfold squareDiameter
  rw [dite_eq_left hprod]
  exact hpe.symm

private theorem latticeDistance_symm (boundary : SquareBoundary) (L : ℕ)
    (x y : Fin L × Fin L) :
    latticeDistance boundary L x y = latticeDistance boundary L y x := by
  cases boundary <;> simp [latticeDistance, SimpleGraph.dist_comm]

private theorem squareDistance_eq_zero_of_empty (boundary : SquareBoundary) (L : ℕ)
    (s t : Finset (Fin L × Fin L)) (h : ¬ (s.Nonempty ∧ t.Nonempty)) :
    squareDistance boundary L s t = 0 := by
  have h' : ¬ (s.product t).Nonempty := by
    rintro ⟨⟨x, y⟩, hp⟩
    obtain ⟨hx, hy⟩ := Finset.mem_product.mp hp
    exact h ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
  unfold squareDistance
  rw [dite_eq_right h']

theorem squareDistance_symm (boundary : SquareBoundary) (L : ℕ)
    (s t : Finset (Fin L × Fin L)) :
    squareDistance boundary L s t = squareDistance boundary L t s := by
  by_cases h : s.Nonempty ∧ t.Nonempty
  · have key : ∀ s t : Finset (Fin L × Fin L), s.Nonempty → t.Nonempty →
        squareDistance boundary L s t ≤ squareDistance boundary L t s := by
      intro s t hs ht
      obtain ⟨x, hx, y, hy, he⟩ := exists_squareDistance_eq boundary L t s ht hs
      rw [he, latticeDistance_symm]
      exact squareDistance_le_latticeDistance_of_mem boundary L s t y x hy hx
    exact le_antisymm (key s t h.1 h.2) (key t s h.2 h.1)
  · rw [squareDistance_eq_zero_of_empty boundary L s t h,
      squareDistance_eq_zero_of_empty boundary L t s (fun h' => h ⟨h'.2, h'.1⟩)]

theorem squareDiameter_mono (boundary : SquareBoundary) (L : ℕ)
    {s t : Finset (Fin L × Fin L)} (hst : s ⊆ t) :
    squareDiameter boundary L s ≤ squareDiameter boundary L t := by
  by_cases hs : s.Nonempty
  · obtain ⟨x, hx, y, hy, he⟩ := exists_squareDiameter_eq boundary L s hs
    rw [he]
    exact latticeDistance_le_squareDiameter_of_mem boundary L t x y (hst hx) (hst hy)
  · have h1 : ¬ (s.product s).Nonempty := by
      simp [Finset.not_nonempty_iff_eq_empty.mp hs]
    unfold squareDiameter
    rw [dite_eq_right h1]
    exact Nat.zero_le _

theorem squareDistance_le_squareDiameter_of_subset (boundary : SquareBoundary) (L : ℕ)
    {s t u : Finset (Fin L × Fin L)} (hs : s.Nonempty) (ht : t.Nonempty)
    (hsu : s ⊆ u) (htu : t ⊆ u) :
    squareDistance boundary L s t ≤ squareDiameter boundary L u := by
  obtain ⟨x, hx, y, hy, he⟩ := exists_squareDistance_eq boundary L s t hs ht
  rw [he]
  exact latticeDistance_le_squareDiameter_of_mem boundary L u x y (hsu hx) (htu hy)

theorem latticeDistance_le_two_mul (boundary : SquareBoundary) {L : ℕ} (hL : 1 < L)
    (x y : Fin L × Fin L) : latticeDistance boundary L x y ≤ 2 * L := by
  have hx1 := x.1.isLt
  have hx2 := x.2.isLt
  have hy1 := y.1.isLt
  have hy2 := y.2.isLt
  cases boundary with
  | free =>
    have h := freeDistance_le_coordinateSum L x y
    by_cases h1 : x.1.val ≤ y.1.val <;> by_cases h2 : x.2.val ≤ y.2.val <;>
      simp only [h1, h2, ite_true, ite_false] at h <;> omega
  | periodic =>
    let p : LiftedPoint := ((x.1.val : ℤ), (x.2.val : ℤ))
    let q : LiftedPoint := ((y.1.val : ℤ), (y.2.val : ℤ))
    have hp : periodicProjection L (by omega) p = x := by
      apply Prod.ext
      · exact periodicCoordinate_finVal L (by omega) x.1
      · exact periodicCoordinate_finVal L (by omega) x.2
    have hq : periodicProjection L (by omega) q = y := by
      apply Prod.ext
      · exact periodicCoordinate_finVal L (by omega) y.1
      · exact periodicCoordinate_finVal L (by omega) y.2
    have h := periodicDistance_le_liftedCoordinateSum L hL x y p q hp hq
    simp only [p, q] at h
    by_cases h1 : x.1.val ≤ y.1.val <;> by_cases h2 : x.2.val ≤ y.2.val <;>
      simp [h1, h2] at h <;> omega

theorem squareDiameter_le_two_mul (boundary : SquareBoundary) {L : ℕ} (hL : 1 < L)
    (s : Finset (Fin L × Fin L)) : squareDiameter boundary L s ≤ 2 * L := by
  by_cases hs : s.Nonempty
  · obtain ⟨x, -, y, -, he⟩ := exists_squareDiameter_eq boundary L s hs
    rw [he]
    exact latticeDistance_le_two_mul boundary hL x y
  · have h1 : ¬ (s.product s).Nonempty := by
      simp [Finset.not_nonempty_iff_eq_empty.mp hs]
    unfold squareDiameter
    rw [dite_eq_right h1]
    exact Nat.zero_le _

theorem squareDistance_le_two_mul (boundary : SquareBoundary) {L : ℕ} (hL : 1 < L)
    (s t : Finset (Fin L × Fin L)) : squareDistance boundary L s t ≤ 2 * L := by
  by_cases h : (s.product t).Nonempty
  · obtain ⟨⟨x, y⟩, hp⟩ := h
    obtain ⟨hx, hy⟩ := Finset.mem_product.mp hp
    exact (squareDistance_le_latticeDistance_of_mem boundary L s t x y hx hy).trans
      (latticeDistance_le_two_mul boundary hL x y)
  · unfold squareDistance
    rw [dite_eq_right h]
    exact Nat.zero_le _

theorem one_le_latticeDistance_of_ne (boundary : SquareBoundary) {L : ℕ} (hL : 1 < L)
    {x y : Fin L × Fin L} (hxy : x ≠ y) : 1 ≤ latticeDistance boundary L x y := by
  rw [Nat.one_le_iff_ne_zero]
  cases boundary with
  | free =>
    have hc := squareFree_connected L hL
    intro h
    exact hxy ((hc.dist_eq_zero_iff).mp h)
  | periodic =>
    have hc := squarePeriodic_connected L hL
    intro h
    exact hxy ((hc.dist_eq_zero_iff).mp h)

theorem one_le_chargeDiameter_of_neutral (boundary : SquareBoundary) {L : ℕ} (hL : 1 < L)
    (ρ : ChargeDensity L) (hρ : ρ ≠ 0) (hneutral : ∑ x, ρ x = 0) :
    1 ≤ chargeDiameter boundary L ρ := by
  obtain ⟨x, hx⟩ : ∃ x, ρ x ≠ 0 := by
    by_contra h
    push Not at h
    exact hρ (funext h)
  obtain ⟨y, hyx, hy⟩ : ∃ y, y ≠ x ∧ ρ y ≠ 0 := by
    by_contra h
    push Not at h
    have : ∑ z, ρ z = ρ x :=
      Finset.sum_eq_single x (fun z _ hz => h z hz) (fun h' => absurd (Finset.mem_univ x) h')
    exact hx (this.symm.trans hneutral)
  have hxs : x ∈ chargeSupport ρ := by simp [chargeSupport, hx]
  have hys : y ∈ chargeSupport ρ := by simp [chargeSupport, hy]
  exact (one_le_latticeDistance_of_ne boundary hL hyx.symm).trans
    (latticeDistance_le_squareDiameter_of_mem boundary L _ x y hxs hys)

theorem IsChargeScaleEnsemble.mono {L : ℕ} {boundary : SquareBoundary} {E : ChargeEnsemble L}
    {s s' : ChargeScale} (hE : IsChargeScaleEnsemble boundary E s)
    (hss' : ChargeScale.separationThreshold s' ≤ ChargeScale.separationThreshold s) :
    IsChargeScaleEnsemble boundary E s' :=
  ⟨hE.1, fun ρ hρ σ hσ hne => lt_of_le_of_lt hss' (hE.2 ρ hρ σ hσ hne)⟩

end FroehlichSpencer.BKT

end
