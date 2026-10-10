/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.PinnedCharges.TerminalProfileA3Components
public import FroehlichSpencer.BKT.Generic.PinnedCharges.TerminalProfileA3DecompGraph

/-! # Geometric estimates for the max-scale decomposition -/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic.PinnedCharges.Layer

open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Generic.PinnedCharges.SelectionG

variable {L : ℕ}

/-- A support point belongs to its expanded neighborhood. -/
theorem profileA3_support_subset_neutralNeighborhood (σ : ChargeDensity L)
    {x : Site L} (hx : x ∈ chargeSupport σ) : x ∈ profileA3NeutralNeighborhood σ := by
  change x ∈ boundaryEnergyNeighborhood (8 * boundaryAdjustedSize σ + 2) (chargeSupport σ)
  rw [mem_boundaryEnergyNeighborhood_iff]
  exact ⟨x, hx, by
    have hd := boundaryAdjustedSize_nonneg σ
    calc
      euclideanSiteDistance x x = 0 := by simp [euclideanSiteDistance]
      _ ≤ 8 * boundaryAdjustedSize σ + 2 := by linarith⟩

/-- Overlapping neighborhoods give a controlled support-to-support bridge. -/
theorem profileA3_support_distance_of_neighborhood_overlap
    (σ τ : ChargeDensity L) (hσ : σ ≠ 0) (hτ : τ ≠ 0)
    (hoverlap : (profileA3NeutralNeighborhood σ ∩
      profileA3NeutralNeighborhood τ).Nonempty) :
    euclideanSetDistance (chargeSupport σ) (chargeSupport τ) ≤
      30 * boundaryAdjustedSize σ + 30 * boundaryAdjustedSize τ := by
  obtain ⟨x, hx⟩ := hoverlap
  have hxσ : x ∈ profileA3NeutralNeighborhood σ := (Finset.mem_inter.mp hx).1
  have hxτ : x ∈ profileA3NeutralNeighborhood τ := (Finset.mem_inter.mp hx).2
  obtain ⟨a, ha⟩ := chargeSupport_nonempty_of_ne_zero σ hσ
  obtain ⟨b, hb⟩ := chargeSupport_nonempty_of_ne_zero τ hτ
  have hσsize : 1 ≤ boundaryAdjustedSize σ := one_le_boundaryAdjustedSize hσ
  have hτsize : 1 ≤ boundaryAdjustedSize τ := one_le_boundaryAdjustedSize hτ
  have haN : a ∈ profileA3NeutralNeighborhood σ :=
    profileA3_support_subset_neutralNeighborhood σ ha
  have hbN : b ∈ profileA3NeutralNeighborhood τ :=
    profileA3_support_subset_neutralNeighborhood τ hb
  have hax := profileA3_neutralNeighborhood_graph_diameter σ hσsize haN hxσ
  have hxb := profileA3_neutralNeighborhood_graph_diameter τ hτsize hxτ hbN
  have hgraph : profileA3GraphLength a b ≤
      30 * boundaryAdjustedSize σ + 30 * boundaryAdjustedSize τ := by
    calc
      profileA3GraphLength a b ≤ profileA3GraphLength a x + profileA3GraphLength x b :=
        profileA3GraphLength_triangle a x b
      _ ≤ _ := by linarith
  exact (setDist_le_siteDist ha hb).trans
    ((euclideanSiteDistance_le_profileA3GraphLength a b).trans hgraph)

/-- At the Appendix-D constants, two high neighborhoods cannot overlap. -/
theorem profileA3_high_neighborhoods_not_overlap
    (D : ℝ) (σ τ : ChargeDensity L) (hD : 1 ≤ D)
    (hσ0 : σ ≠ 0) (hτ0 : τ ≠ 0)
    (hσhi : D / 10 ≤ boundaryAdjustedSize σ)
    (hτhi : D / 10 ≤ boundaryAdjustedSize τ)
    (hσmax : boundaryAdjustedSize σ ≤ D)
    (hτmax : boundaryAdjustedSize τ ≤ D)
    (hsep : (65536 : ℝ) * min (boundaryAdjustedSize σ) (boundaryAdjustedSize τ) ^
      (7 / 4 : ℝ) ≤ euclideanSetDistance (chargeSupport σ) (chargeSupport τ)) :
    ¬ (profileA3NeutralNeighborhood σ ∩ profileA3NeutralNeighborhood τ).Nonempty := by
  intro hoverlap
  have hbridge := profileA3_support_distance_of_neighborhood_overlap σ τ hσ0 hτ0 hoverlap
  have hminlo : D / 10 ≤ min (boundaryAdjustedSize σ) (boundaryAdjustedSize τ) :=
    le_min hσhi hτhi
  have hminpow : (D / 10) ^ (7 / 4 : ℝ) ≤
      min (boundaryAdjustedSize σ) (boundaryAdjustedSize τ) ^ (7 / 4 : ℝ) :=
    Real.rpow_le_rpow (by positivity) hminlo (by norm_num)
  have hscale := profileA3_highThreshold_power_lower D hD
  have hlarge : 64 * D < (65536 : ℝ) * min (boundaryAdjustedSize σ)
      (boundaryAdjustedSize τ) ^ (7 / 4 : ℝ) := by
    nlinarith [hminpow, hscale]
  have hbridge' : euclideanSetDistance (chargeSupport σ) (chargeSupport τ) ≤ 60 * D := by
    nlinarith [hbridge, hσmax, hτmax]
  linarith

/-- A low-only piece of diameter `4D` cannot attach to two distinct high neighborhoods. -/
theorem profileA3_lowPiece_attaches_to_at_most_one_high
    (D : ℝ) (σ τ : ChargeDensity L) (S : Finset (Site L))
    (hD : 1 ≤ D) (hσ0 : σ ≠ 0) (hτ0 : τ ≠ 0) (_hne : σ ≠ τ)
    (hσhi : D / 10 ≤ boundaryAdjustedSize σ)
    (hτhi : D / 10 ≤ boundaryAdjustedSize τ)
    (hσmax : boundaryAdjustedSize σ ≤ D)
    (hτmax : boundaryAdjustedSize τ ≤ D)
    (hsep : (65536 : ℝ) * min (boundaryAdjustedSize σ) (boundaryAdjustedSize τ) ^
      (7 / 4 : ℝ) ≤ euclideanSetDistance (chargeSupport σ) (chargeSupport τ))
    (hdiam : ∀ x ∈ S, ∀ y ∈ S,
      profileA3GraphLength x y ≤ 4 * D)
    (hleft : (profileA3NeutralNeighborhood σ ∩ S).Nonempty)
    (hright : (profileA3NeutralNeighborhood τ ∩ S).Nonempty) : False := by
  obtain ⟨x, hx⟩ := hleft
  obtain ⟨y, hy⟩ := hright
  have hxσ : x ∈ profileA3NeutralNeighborhood σ := (Finset.mem_inter.mp hx).1
  have hxS : x ∈ S := (Finset.mem_inter.mp hx).2
  have hyτ : y ∈ profileA3NeutralNeighborhood τ := (Finset.mem_inter.mp hy).1
  have hyS : y ∈ S := (Finset.mem_inter.mp hy).2
  obtain ⟨a, ha⟩ := chargeSupport_nonempty_of_ne_zero σ hσ0
  obtain ⟨b, hb⟩ := chargeSupport_nonempty_of_ne_zero τ hτ0
  have hσsize : 1 ≤ boundaryAdjustedSize σ := one_le_boundaryAdjustedSize hσ0
  have hτsize : 1 ≤ boundaryAdjustedSize τ := one_le_boundaryAdjustedSize hτ0
  have haN : a ∈ profileA3NeutralNeighborhood σ :=
    profileA3_support_subset_neutralNeighborhood σ ha
  have hbN : b ∈ profileA3NeutralNeighborhood τ :=
    profileA3_support_subset_neutralNeighborhood τ hb
  have hax := profileA3_neutralNeighborhood_graph_diameter σ hσsize haN hxσ
  have hxy := hdiam x hxS y hyS
  have hyb := profileA3_neutralNeighborhood_graph_diameter τ hτsize hyτ hbN
  have hgraph : profileA3GraphLength a b ≤ 64 * D := by
    have htri₁ := profileA3GraphLength_triangle a x b
    have htri₂ := profileA3GraphLength_triangle x y b
    have hyb' : profileA3GraphLength y b ≤ 30 * boundaryAdjustedSize τ := hyb
    have hax' : profileA3GraphLength a x ≤ 30 * boundaryAdjustedSize σ := by
      simpa [profileA3GraphLength_comm] using hax
    nlinarith
  have hdist : euclideanSetDistance (chargeSupport σ) (chargeSupport τ) ≤ 64 * D := by
    calc
      euclideanSetDistance (chargeSupport σ) (chargeSupport τ) ≤ euclideanSiteDistance a b :=
        setDist_le_siteDist ha hb
      _ ≤ profileA3GraphLength a b := euclideanSiteDistance_le_profileA3GraphLength a b
      _ ≤ 64 * D := hgraph
  have hminlo : D / 10 ≤ min (boundaryAdjustedSize σ) (boundaryAdjustedSize τ) :=
    le_min hσhi hτhi
  have hminpow : (D / 10) ^ (7 / 4 : ℝ) ≤
      min (boundaryAdjustedSize σ) (boundaryAdjustedSize τ) ^ (7 / 4 : ℝ) :=
    Real.rpow_le_rpow (by positivity) hminlo (by norm_num)
  have hscale := profileA3_highThreshold_power_lower D hD
  have hlarge : 64 * D < (65536 : ℝ) * min (boundaryAdjustedSize σ)
      (boundaryAdjustedSize τ) ^ (7 / 4 : ℝ) := by
    nlinarith [hminpow, hscale]
  linarith

end FroehlichSpencer.BKT.Generic.PinnedCharges.Layer

end
