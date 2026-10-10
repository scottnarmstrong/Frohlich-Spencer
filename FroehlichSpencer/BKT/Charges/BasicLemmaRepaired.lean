/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Charges.BasicLemmaCoefficientBounds
public import FroehlichSpencer.BKT.Charges.SupportCover

/-! # Repaired L4.3 lineage and coefficient-count interface

This module assembles the repaired connected-lineage and keep-charge
certificates with the multiplier estimates. The remaining finite-square input
to the refined estimate is stated explicitly as the neighborhood-cardinality
hypothesis `hNA`; the scale-cell proof is kept separate from the iteration.
-/

@[expose] public section

namespace FroehlichSpencer.BKT

/-- The original inputs within conflict radius `2^k` of an output density. -/
noncomputable def basicLemmaNeighborhood {L : ℕ} (boundary : SquareBoundary) (k : ℕ)
    (E : ChargeEnsemble L) (ρ : ChargeDensity L) : ChargeEnsemble L :=
  E.filter fun σ => densityDistance boundary L σ ρ ≤ 2 ^ k

/-- KP's previous scale, retaining the separate `A_{-1}` endpoint at `k=0`. -/
def basicLemmaPreviousScale : ℕ → ChargeScale
  | 0 => .minusOne
  | k + 1 => .ofNat k

/-- Common support points give zero density distance. -/
theorem densityDistance_eq_zero_of_common_support {L : ℕ}
    (boundary : SquareBoundary) (ρ σ : ChargeDensity L)
    {x : Fin L × Fin L} (hxρ : x ∈ chargeSupport ρ)
    (hxσ : x ∈ chargeSupport σ) :
    densityDistance boundary L ρ σ = 0 := by
  have hle := squareDistance_le_latticeDistance_of_mem boundary L
    (chargeSupport ρ) (chargeSupport σ) x x hxρ hxσ
  have hself : latticeDistance boundary L x x = 0 := by
    cases boundary <;> simp [latticeDistance]
  change squareDistance boundary L (chargeSupport ρ) (chargeSupport σ) ≤
    latticeDistance boundary L x x at hle
  rw [hself] at hle
  change squareDistance boundary L (chargeSupport ρ) (chargeSupport σ) = 0
  omega

/-- Every active input leaf remains in the final factor's conflict
neighborhood: the certified support-union identity gives a common site. -/
theorem ChargeMergeHistory.good_activeLeaves_subset_neighborhood {L : ℕ}
    {boundary : SquareBoundary} {k : ℕ} {E : ChargeEnsemble L}
    {ρ : ChargeDensity L} (h : ChargeMergeHistory boundary k E ρ)
    (hg : h.Good) (hE : IsBKTEnsemble E) :
    h.leaves ⊆ basicLemmaNeighborhood boundary k E ρ := by
  intro σ hσ
  have hσE : σ ∈ E := h.leaves_subset hσ
  obtain ⟨x, hx⟩ := exists_coordinate_ne_zero σ (hE.1 σ hσE)
  have hxσ : x ∈ chargeSupport σ := by
    simp [chargeSupport, hx]
  have hxρ : x ∈ chargeSupport ρ := by
    rw [h.good_support_eq_activeLeaves hg hE]
    exact Finset.mem_biUnion.mpr ⟨σ, hσ, hxσ⟩
  have hdist := densityDistance_eq_zero_of_common_support boundary σ ρ hxσ hxρ
  simp only [basicLemmaNeighborhood, Finset.mem_filter]
  exact ⟨hσE, by rw [hdist]; exact Nat.zero_le _⟩

/-- A cell of diameter at most the separation threshold can meet the support
of at most one member of a separated ensemble. -/
theorem atMostOne_chargeSupport_meets_cell {L : ℕ}
    (boundary : SquareBoundary) (scale : ChargeScale) (E : ChargeEnsemble L)
    (hE : IsChargeScaleEnsemble boundary E scale)
    (C : Finset (Fin L × Fin L))
    (hdiam : squareDiameter boundary L C ≤ ChargeScale.separationThreshold scale) :
    (E.filter fun ρ => ∃ x ∈ chargeSupport ρ, x ∈ C).card ≤ 1 := by
  classical
  rw [Finset.card_le_one]
  intro ρ hρ σ hσ
  have hρE := (Finset.mem_filter.mp hρ).1
  have hσE := (Finset.mem_filter.mp hσ).1
  obtain ⟨x, hxρ, hxC⟩ := (Finset.mem_filter.mp hρ).2
  obtain ⟨y, hyσ, hyC⟩ := (Finset.mem_filter.mp hσ).2
  by_contra hne
  have hsep := hE.2 ρ hρE σ hσE hne
  have hρσ := squareDistance_le_latticeDistance_of_mem boundary L
    (chargeSupport ρ) (chargeSupport σ) x y hxρ hyσ
  have hxy := latticeDistance_le_squareDiameter_of_mem boundary L C x y hxC hyC
  exact (not_lt_of_ge (hρσ.trans (hxy.trans hdiam))) hsep

/-- A finite cover by cells of diameter below the input separation scale
bounds the number of nearby source densities by the number of cells. -/
theorem basicLemmaNeighborhood_card_le_cellCover {L : ℕ}
    (boundary : SquareBoundary) (k : ℕ) (E : ChargeEnsemble L)
    (hE : IsChargeScaleEnsemble boundary E (basicLemmaPreviousScale k))
    (ρ : ChargeDensity L)
    (Cells : Finset (Finset (Fin L × Fin L)))
    (hdiam : ∀ C ∈ Cells,
      squareDiameter boundary L C ≤
        ChargeScale.separationThreshold (basicLemmaPreviousScale k))
    (hcover : ∀ q ∈ basicLemmaNeighborhood boundary k E ρ,
      ∃ C ∈ Cells, ∃ x ∈ chargeSupport q, x ∈ C) :
    (basicLemmaNeighborhood boundary k E ρ).card ≤ Cells.card := by
  classical
  let f : ChargeDensity L → Finset (Fin L × Fin L) := fun q =>
    if hq : q ∈ basicLemmaNeighborhood boundary k E ρ then
      Classical.choose (hcover q hq) else ∅
  -- Choose one covering cell for each density; the diameter lemma makes the
  -- assignment injective.
  have hf : ∀ q ∈ basicLemmaNeighborhood boundary k E ρ,
    f q ∈ Cells ∧ ∃ x ∈ chargeSupport q, x ∈ f q := by
    intro q hq
    simpa [f, hq] using Classical.choose_spec (hcover q hq)
  apply Finset.card_le_card_of_injOn f (fun q hq => (hf q hq).1)
  intro q hq r hr hfr
  by_contra hne
  have hcard := atMostOne_chargeSupport_meets_cell boundary
    (basicLemmaPreviousScale k) E hE (f q)
    (hdiam (f q) ((hf q hq).1))
  have hqhit : q ∈ E.filter (fun τ => ∃ x ∈ chargeSupport τ, x ∈ f q) := by
    simp only [Finset.mem_filter]
    exact ⟨(Finset.mem_filter.mp hq).1, (hf q hq).2⟩
  have hrhit : r ∈ E.filter (fun τ => ∃ x ∈ chargeSupport τ, x ∈ f q) := by
    simp only [Finset.mem_filter]
    refine ⟨(Finset.mem_filter.mp hr).1, ?_⟩
    simpa [hfr] using (hf r hr).2
  exact hne (Finset.card_le_one.mp hcard q hqhit r hrhit)

/-- A terminal factor's exact merge/keep accounting implies the coarse
multiplier estimate against the full input conflict neighborhood. -/
theorem IsChargeProductExpansion.factor_repairedMultiplierBound
    {L : ℕ} {boundary : SquareBoundary} {k : ℕ} {E : ChargeEnsemble L}
    {K : ChargeDensity L → ℝ} {T : List (ChargeProductTerm L)}
    (hT : IsChargeProductExpansion boundary k E K T)
    (hE : IsBKTEnsemble E) (t : ChargeProductTerm L) (ht : t ∈ T)
    (ρ : ChargeDensity L) (hρ : ρ ∈ t.ensemble) :
    ∃ c : CertifiedChargeMergeHistory boundary k E ρ, ∃ H : ChargeEnsemble L,
      H ⊆ E ∧ Disjoint H c.history.leaves ∧
      c.history.multiplierCount = c.history.leaves.card - 1 + H.card ∧
      (∀ q ∈ H, densityDistance boundary L q ρ ≤ 2 ^ k) ∧
      (∀ a ∈ c.history.allLeaves, ∀ b ∈ c.history.allLeaves,
        SourceConflictPath boundary L k a b) ∧
      c.history.multiplierCount ≤
        (basicLemmaNeighborhood boundary k E ρ).card - 1 ∧
      (3 : ℝ) ^ c.history.multiplierCount ≤
        3 ^ (basicLemmaNeighborhood boundary k E ρ).card := by
  obtain ⟨family⟩ := hT.ancestry t ht
  let c := family.history ρ hρ
  obtain ⟨H, hHE, hdisj, hformula, hnear⟩ :=
    c.history.good_lineage_keepChargeAccounting c.good hE
  have hPne := c.history.leaves_nonempty
  have hPN := c.history.good_activeLeaves_subset_neighborhood c.good hE
  have hHN : H ⊆ basicLemmaNeighborhood boundary k E ρ \ c.history.leaves := by
    intro q hq
    refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
    · simp only [basicLemmaNeighborhood, Finset.mem_filter]
      exact ⟨hHE hq, hnear q hq⟩
    · exact fun hqP => (Finset.disjoint_left.mp hdisj) hq hqP
  have hmN := lineageCharge_multiplier_le_neighborhood_sub_one
    c.history.leaves H (basicLemmaNeighborhood boundary k E ρ)
    c.history.multiplierCount hPne hPN hHN hformula
  refine ⟨c, H, hHE, hdisj, hformula, hnear,
    c.history.good_sourceConnected c.good hE, hmN, ?_⟩
  exact coarse_multiplier_bound _ _ (by omega)

/-- Refined multiplier estimate, once the square-neighborhood count is
supplied. It is exactly the interface consumed by the geometric cell lemma. -/
theorem IsChargeProductExpansion.factor_repairedRefinedMultiplierBound
    {L : ℕ} {boundary : SquareBoundary} {k : ℕ} {E : ChargeEnsemble L}
    {K : ChargeDensity L → ℝ} {T : List (ChargeProductTerm L)}
    (hT : IsChargeProductExpansion boundary k E K T)
    (hE : IsBKTEnsemble E) (t : ChargeProductTerm L) (ht : t ∈ T)
    (ρ : ChargeDensity L) (hρ : ρ ∈ t.ensemble)
    (hNA : (basicLemmaNeighborhood boundary k E ρ).card ≤
      76 * chargeA boundary L ρ (basicLemmaPreviousScale k)) :
    ∃ c : CertifiedChargeMergeHistory boundary k E ρ,
      c.history.multiplierCount ≤ 76 * chargeA boundary L ρ (basicLemmaPreviousScale k) ∧
      (3 : ℝ) ^ c.history.multiplierCount ≤
        Real.exp (100 * chargeA boundary L ρ (basicLemmaPreviousScale k)) := by
  obtain ⟨c, H, hHE, hdisj, hformula, hnear, hconnected, hmN, hcoarse⟩ :=
    hT.factor_repairedMultiplierBound hE t ht ρ hρ
  refine ⟨c, ?_, ?_⟩
  · omega
  · exact refined_multiplier_bound _ _ (by omega)

/-- The refined coefficient estimate once the finite-square count
`n_E(ρ) ≤ 76 A_{k−1}(ρ)` is available. -/
theorem IsChargeProductExpansion.factor_repairedRefinedCoefficientBound
    {L : ℕ} {boundary : SquareBoundary} {k : ℕ} {E : ChargeEnsemble L}
    {K : ChargeDensity L → ℝ} {T : List (ChargeProductTerm L)}
    (hT : IsChargeProductExpansion boundary k E K T)
    (hE : IsBKTEnsemble E) (t : ChargeProductTerm L) (ht : t ∈ T)
    (ρ : ChargeDensity L) (hρ : ρ ∈ t.ensemble)
    (hNA : (basicLemmaNeighborhood boundary k E ρ).card ≤
      76 * chargeA boundary L ρ (basicLemmaPreviousScale k)) :
    ∃ c : CertifiedChargeMergeHistory boundary k E ρ,
      |t.coefficient ρ| ≤
        Real.exp (100 * chargeA boundary L ρ (basicLemmaPreviousScale k)) *
          c.history.activeLineageProduct K := by
  obtain ⟨family, hcoeff⟩ := hT.coefficientLineage t ht
  let c := family.history ρ hρ
  obtain ⟨H, hHE, hdisj, hformula, hnear⟩ :=
    c.history.good_lineage_keepChargeAccounting c.good hE
  have hPne := c.history.leaves_nonempty
  have hPN := c.history.good_activeLeaves_subset_neighborhood c.good hE
  have hHN : H ⊆ basicLemmaNeighborhood boundary k E ρ \ c.history.leaves := by
    intro q hq
    refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
    · simp only [basicLemmaNeighborhood, Finset.mem_filter]
      exact ⟨hHE hq, hnear q hq⟩
    · exact fun hqP => (Finset.disjoint_left.mp hdisj) hq hqP
  have hcoeffProduct : |t.coefficient ρ| =
      (3 : ℝ) ^ c.history.multiplierCount * c.history.activeLineageProduct K := by
    calc
      |t.coefficient ρ| = |c.history.lineageValue K| := congrArg abs (hcoeff ρ hρ)
      _ = c.history.lineageMagnitude K :=
        c.history.abs_lineageValue_eq_lineageMagnitude K
      _ = (3 : ℝ) ^ c.history.multiplierCount * c.history.activeLineageProduct K :=
        c.history.lineageMagnitude_eq_multiplier_product c.good K
  have hproduct : 0 ≤ c.history.activeLineageProduct K := by
    unfold ChargeMergeHistory.activeLineageProduct
    exact Finset.prod_nonneg fun q hq => abs_nonneg (K q)
  have hbound := lineageCharge_refined_coefficient_bound
    (t.coefficient ρ) (c.history.activeLineageProduct K) c.history.leaves H
    (basicLemmaNeighborhood boundary k E ρ) c.history.multiplierCount
    (chargeA boundary L ρ (basicLemmaPreviousScale k)) hcoeffProduct hproduct
    hPne hPN hHN hformula hNA
  exact ⟨c, hbound⟩

/-- Full finite convex expansion with the repaired ancestry properties and
coarse multiplier bounds. The refined coefficient conclusion follows from
`factor_repairedRefinedMultiplierBound` after the geometric neighborhood
estimate is supplied. -/
theorem exists_repairedBasicLemma_expansion {L : ℕ} (boundary : SquareBoundary)
    (k : ℕ) (E : ChargeEnsemble L) (hE : IsBKTEnsemble E)
    (K : ChargeDensity L → ℝ) :
    ∃ T : List (ChargeProductTerm L),
      IsChargeProductExpansion boundary k E K T ∧
      ∀ t ∈ T, ∀ ρ ∈ t.ensemble,
        ∃ c : CertifiedChargeMergeHistory boundary k E ρ, ∃ H : ChargeEnsemble L,
          H ⊆ E ∧ Disjoint H c.history.leaves ∧
          c.history.multiplierCount = c.history.leaves.card - 1 + H.card ∧
          (∀ q ∈ H, densityDistance boundary L q ρ ≤ 2 ^ k) ∧
          (∀ a ∈ c.history.allLeaves, ∀ b ∈ c.history.allLeaves,
            SourceConflictPath boundary L k a b) ∧
          c.history.multiplierCount ≤
            (basicLemmaNeighborhood boundary k E ρ).card - 1 ∧
          (3 : ℝ) ^ c.history.multiplierCount ≤
            3 ^ (basicLemmaNeighborhood boundary k E ρ).card := by
  obtain ⟨T, hT⟩ := exists_chargeProductExpansion boundary k E hE K
  refine ⟨T, hT, ?_⟩
  intro t ht ρ hρ
  obtain ⟨c', H, hHE, hdisj, hformula, hnear, hconnected', hmN', hcoef'⟩ :=
    hT.factor_repairedMultiplierBound hE t ht ρ hρ
  exact ⟨c', H, hHE, hdisj, hformula, hnear, hconnected', hmN', hcoef'⟩

end FroehlichSpencer.BKT

end
