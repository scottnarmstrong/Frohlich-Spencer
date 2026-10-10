/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module
public import FroehlichSpencer.BKT.Generic.PinnedCharges.Selection
public import FroehlichSpencer.BKT.Generic.PinnedCharges.BoundaryCutGeometry

/-! # Private sites for boundary-rejected cover squares

A square rejected by a boundary margin still has a private support site in a
minimum cover. The site lies in a strip controlled by that square's boundary
distance and diameter. The private-site assignment also gives the exact
one-scale cardinality bound; it does not sum over scales. -/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic.PinnedCharges

 theorem minimumCover_private_site_depth_le {L : ℕ}
    (Allowed : Finset (Site L) → Prop) (ρ : ChargeDensity L)
    (C : Finset (Finset (Site L)))
    (hC : IsAllowedMinimumSupportCover Allowed ρ C)
    {s : Finset (Site L)} (hs : s ∈ C) :
    ∃ x ∈ chargeSupport ρ, x ∈ s ∧
      (∀ t ∈ C, t ≠ s → x ∉ t) ∧
      (siteBoundaryDepth x : ℝ) ≤ euclideanBoundaryDistance s + euclideanSetDiameter s := by
  obtain ⟨x, hxρ, hxs, hprivate⟩ :=
    minimumSupportCover_square_has_private_site Allowed ρ C hC hs
  refine ⟨x, hxρ, hxs, hprivate, ?_⟩
  have hs' : s.Nonempty := ⟨x, hxs⟩
  have hsingle := euclideanBoundaryDistance_subset_le
    ({x} : Finset (Site L)) s ⟨x, Finset.mem_singleton_self x⟩ hs'
      (by intro y hy; simp only [Finset.mem_singleton] at hy; subst y; exact hxs)
  have hsingleEq : euclideanBoundaryDistance ({x} : Finset (Site L)) =
      (siteBoundaryDepth x : ℝ) := by
    simp [euclideanBoundaryDistance]
  rw [hsingleEq] at hsingle
  exact hsingle

theorem minimumCover_private_site_depth_lt_of_boundary_rejected {L : ℕ}
    (Allowed : Finset (Site L) → Prop) (ρ : ChargeDensity L)
    (C : Finset (Finset (Site L)))
    (hC : IsAllowedMinimumSupportCover Allowed ρ C)
    {s : Finset (Site L)} (hs : s ∈ C) (R : ℝ)
    (hR : euclideanBoundaryDistance s < R) :
    ∃ x ∈ chargeSupport ρ, x ∈ s ∧
      (∀ t ∈ C, t ≠ s → x ∉ t) ∧
      (siteBoundaryDepth x : ℝ) < R + euclideanSetDiameter s := by
  obtain ⟨x, hxρ, hxs, hprivate, hdepth⟩ :=
    minimumCover_private_site_depth_le Allowed ρ C hC hs
  refine ⟨x, hxρ, hxs, hprivate, ?_⟩
  linarith

theorem minimumCover_subfamily_card_le_supportCard {L : ℕ}
    (Allowed : Finset (Site L) → Prop) (ρ : ChargeDensity L)
    (C B : Finset (Finset (Site L)))
    (hC : IsAllowedMinimumSupportCover Allowed ρ C) (hB : B ⊆ C) :
    B.card ≤ (chargeSupport ρ).card := by
  classical
  let f : {s // s ∈ B} → {x // x ∈ chargeSupport ρ} := fun s =>
    ⟨Classical.choose (minimumSupportCover_square_has_private_site
        Allowed ρ C hC (s := s.1) (hB s.2)),
      (Classical.choose_spec (minimumSupportCover_square_has_private_site
        Allowed ρ C hC (s := s.1) (hB s.2))).1⟩
  have hinj : Function.Injective f := by
    intro s t hst
    apply Subtype.ext
    have hval := congrArg Subtype.val hst
    have hsSpec := Classical.choose_spec (minimumSupportCover_square_has_private_site
      Allowed ρ C hC (s := s.1) (hB s.2))
    have htSpec := Classical.choose_spec (minimumSupportCover_square_has_private_site
      Allowed ρ C hC (s := t.1) (hB t.2))
    by_contra hne
    have hxt : (f s).1 ∈ t.1 := by rw [hval]; exact htSpec.2.1
    exact hsSpec.2.2 t.1 (hB t.2) (Ne.symm hne) hxt
  have hcard := Fintype.card_le_of_injective f hinj
  rw [Fintype.card_coe B, Fintype.card_coe (chargeSupport ρ)] at hcard
  exact hcard

end FroehlichSpencer.BKT.Generic.PinnedCharges

end
