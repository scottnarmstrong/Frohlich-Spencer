/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Charges.ScaleProcess
public import FroehlichSpencer.BKT.Charges.MergeHistoryLeaves
public import FroehlichSpencer.BKT.Charges.BasicLemmaRepaired
public import FroehlichSpencer.BKT.Charges.BasicLemmaCoefficientBounds
public import FroehlichSpencer.BKT.Charges.BasicLemmaCellPacking

/-!
# KP Lemma 4.3 in the form used by the scale process

The expansion `IsChargeProductExpansion` (finite convex identity with `k`-separated outputs) and its
certified merge histories (active leaves, keep-charge accounting, `MergeHistoryLeaves`) prove
the connected-lineage and coefficient assertions in KP Lemma 4.3.

The finite-square estimate is
supplied by `BasicLemmaCellPacking`.

* `basicLemmaLineageFormulaStatement` — the lineage product formula (the lineage identity): along a
  certified history family of each branch, `|K'(ϱ)| = 3^{m(ϱ)} ∏_{ϱ' ∈ P(ϱ)} |K(ϱ')|`;
* `basicLemmaNeighborhoodCountStatement` — the neighbourhood count `n_E(ϱ) ≤ 76 A_{k−1}(ϱ)`
  for a `(k−1)`-separated `E`.

`basicLemmaStepStatement_of_lineageFormula` combines the lineage formula and the neighbourhood
count. Both inputs are proved below; `basicLemmaStepStatement` gives the resulting estimate.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT

open Finset

/-- The lineage product formula of KP Lemma 4.3 (the lineage identity). Every branch of
some expansion carries a certified history family along which
`|K'(ϱ)| = 3^{m(ϱ)} ∏_{ϱ' ∈ P(ϱ)} |K(ϱ')|`, with `m` the multiplier count and `P(ϱ)` the active
leaves. -/
def basicLemmaLineageFormulaStatement : Prop :=
  ∀ (boundary : SquareBoundary) (L k : ℕ) (E : ChargeEnsemble L), IsBKTEnsemble E →
    ∀ K : ChargeDensity L → ℝ, ∃ T : List (ChargeProductTerm L),
      IsChargeProductExpansion boundary k E K T ∧
      ∀ t ∈ T, ∃ fam : CertifiedChargeHistoryFamily boundary k E t.ensemble,
        ∀ ρ (hρ : ρ ∈ t.ensemble),
          |t.coefficient ρ| = (3 : ℝ) ^ (fam.history ρ hρ).history.multiplierCount *
            ∏ σ ∈ (fam.history ρ hρ).history.leaves, |K σ|

/-- The refined neighbourhood count of KP Lemma 4.3 (: for a
`(k−1)`-separated ensemble `E` on a square domain and a density `ϱ` compatible with `E`, at most
`76 A_{k−1}(ϱ)` members of `E` lie within distance `2^k` of `ϱ`. -/
def basicLemmaNeighborhoodCountStatement : Prop :=
  ∀ (boundary : SquareBoundary) (L k : ℕ), 1 < L → (boundary = .free ∨ Even L) →
    ∀ E : ChargeEnsemble L, IsChargeScaleEnsemble boundary E (basicLemmaPreviousScale k) →
    ∀ ρ : ChargeDensity L, IsCompatible E ρ →
      (basicLemmaNeighborhood boundary k E ρ).card ≤
        76 * chargeA boundary L ρ (basicLemmaPreviousScale k)

/-- Every output coefficient satisfies the exact lineage product formula. -/
theorem basicLemmaLineageFormula : basicLemmaLineageFormulaStatement := by
  intro boundary L k E hE K
  obtain ⟨T, hT⟩ := exists_chargeProductExpansion boundary k E hE K
  refine ⟨T, hT, ?_⟩
  intro t ht
  obtain ⟨family, hcoeff⟩ := hT.coefficientLineage t ht
  refine ⟨family, ?_⟩
  intro ρ hρ
  let c := family.history ρ hρ
  calc
    |t.coefficient ρ| = |c.history.lineageValue K| := congrArg abs (hcoeff ρ hρ)
    _ = c.history.lineageMagnitude K := c.history.abs_lineageValue_eq_lineageMagnitude K
    _ = (3 : ℝ) ^ c.history.multiplierCount * c.history.activeLineageProduct K :=
      c.history.lineageMagnitude_eq_multiplier_product c.good K
    _ = (3 : ℝ) ^ c.history.multiplierCount *
        ∏ σ ∈ c.history.leaves, |K σ| := rfl

/--
The finite-square  count holds on both  square carriers.
-/
theorem basicLemmaNeighborhoodCount : basicLemmaNeighborhoodCountStatement := by
  intro boundary L k hL _hdom E hE ρ hρ
  exact basicLemmaNeighborhood_count boundary hL k E hE ρ hρ


theorem basicLemmaStepStatement_of_lineageFormula (hlin : basicLemmaLineageFormulaStatement)
    (hcount : basicLemmaNeighborhoodCountStatement) (boundary : SquareBoundary) {L : ℕ}
    (hL : 1 < L) (hdom : boundary = .free ∨ Even L) : BasicLemmaStepStatement boundary L := by
  classical
  intro k E hE K
  obtain ⟨T, hT, hfam⟩ := hlin boundary L k E hE.1 K
  have hmem : ∀ i : Fin T.length, chargeProductTermAt T i ∈ T := fun i => List.get_mem T i
  choose fam hfamK using fun i : Fin T.length => hfam (chargeProductTermAt T i) (hmem i)
  refine ⟨T.length, fun i => (chargeProductTermAt T i).ensemble,
    fun i => (chargeProductTermAt T i).coefficient, fun i => (chargeProductTermAt T i).weight,
    fun i => hT.positive _ (hmem i), ?_, fun ψ => ?_, fun i => ⟨hT.terminal _ (hmem i), ?_⟩⟩
  · rw [← chargeProductTermWeightSum_eq_fin]
    exact hT.normalized
  · rw [hT.identity ψ, chargeProductTermExpressionSum_eq_fin]
  · set t := chargeProductTermAt T i
    let par : ChargeDensity L → ChargeEnsemble L := fun a =>
      if ha : a ∈ t.ensemble then ((fam i).history a ha).history.leaves else ∅
    have hpar : ∀ a (ha : a ∈ t.ensemble), par a = ((fam i).history a ha).history.leaves :=
      fun a ha => by simp [par, ha]
    refine ⟨par, fun a ha a' ha' hne => ?_, fun a ha => ?_⟩
    · rw [hpar a ha, hpar a' ha']
      exact Finset.disjoint_of_subset_left (ChargeMergeHistory.leaves_subset_allLeaves _)
        (Finset.disjoint_of_subset_right (ChargeMergeHistory.leaves_subset_allLeaves _)
          ((fam i).disjoint a ha a' ha' hne))
    · set c := (fam i).history a ha
      have hg := c.good
      rw [hpar a ha]
      refine
        { parents_subset := c.history.leaves_subset
          parents_nonempty := c.history.leaves_nonempty
          support_eq := c.history.good_support_eq_activeLeaves hg hE.1
          sign := c.history.good_sign_on_leaf hg hE.1
          connected := c.history.good_leaves_connected hg hE.1
          coefficient := ?_ }
      obtain ⟨H, hHE, hdisj, hformula, hnear⟩ :=
        c.history.good_lineage_keepChargeAccounting hg hE.1
      have hPN := c.history.good_activeLeaves_subset_neighborhood hg hE.1
      have hHN : H ⊆ basicLemmaNeighborhood boundary k E a \ c.history.leaves := by
        intro q hq
        refine Finset.mem_sdiff.mpr ⟨?_, fun hqP => Finset.disjoint_left.mp hdisj hq hqP⟩
        simp only [basicLemmaNeighborhood, Finset.mem_filter]
        exact ⟨hHE hq, hnear q hq⟩
      have hNA := hcount boundary L k hL hdom E hE a (hT.parented t (hmem i) a ha)
      have h3 := lineageCharge_refined_multiplier_bound c.history.leaves H
        (basicLemmaNeighborhood boundary k E a) c.history.multiplierCount
        (chargeA boundary L a (basicLemmaPreviousScale k)) c.history.leaves_nonempty hPN hHN
        hformula hNA
      rw [hfamK i a ha]
      exact mul_le_mul_of_nonneg_right h3 (Finset.prod_nonneg fun _ _ => abs_nonneg _)

/-- The closed KP Lemma 4.3 interface for the scale process. -/
theorem basicLemmaStepStatement (boundary : SquareBoundary) {L : ℕ}
    (hL : 1 < L) (hdom : boundary = .free ∨ Even L) :
    BasicLemmaStepStatement boundary L :=
  basicLemmaStepStatement_of_lineageFormula basicLemmaLineageFormula basicLemmaNeighborhoodCount
    boundary hL hdom

/-- Full repaired L4.3: a positive normalized finite expansion identity into
`k`-separated ensembles, parented by the original ensemble, with connected
source ancestry, exact signed lineage products, and both coefficient bounds. -/
theorem exists_repairedBasicLemma_full {L : ℕ} (boundary : SquareBoundary)
    (hL : 1 < L) (k : ℕ) (E : ChargeEnsemble L)
    (hE : IsChargeScaleEnsemble boundary E (basicLemmaPreviousScale k))
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
          t.coefficient ρ = (3 : ℝ) ^ c.history.multiplierCount *
            ∏ σ ∈ c.history.leaves, K σ ∧
          |t.coefficient ρ| ≤
            3 ^ (basicLemmaNeighborhood boundary k E ρ).card *
              c.history.activeLineageProduct K ∧
          |t.coefficient ρ| ≤
            Real.exp (100 * chargeA boundary L ρ (basicLemmaPreviousScale k)) *
              c.history.activeLineageProduct K := by
  classical
  obtain ⟨T, hT⟩ := exists_chargeProductExpansion boundary k E hE.1 K
  refine ⟨T, hT, ?_⟩
  intro t ht ρ hρ
  obtain ⟨family, hcoeff⟩ := hT.coefficientLineage t ht
  let c := family.history ρ hρ
  obtain ⟨H, hHE, hdisj, hformula, hnear⟩ :=
    c.history.good_lineage_keepChargeAccounting c.good hE.1
  have hPN : c.history.leaves ⊆ basicLemmaNeighborhood boundary k E ρ :=
    c.history.good_activeLeaves_subset_neighborhood c.good hE.1
  have hHN : H ⊆ basicLemmaNeighborhood boundary k E ρ \ c.history.leaves := by
    intro q hq
    refine Finset.mem_sdiff.mpr ⟨?_, fun hqP => Finset.disjoint_left.mp hdisj hq hqP⟩
    simp only [basicLemmaNeighborhood, Finset.mem_filter]
    exact ⟨hHE hq, hnear q hq⟩
  have hsigned : t.coefficient ρ = (3 : ℝ) ^ c.history.multiplierCount *
      ∏ σ ∈ c.history.leaves, K σ := by
    calc
      t.coefficient ρ = c.history.lineageValue K := hcoeff ρ hρ
      _ = (3 : ℝ) ^ c.history.multiplierCount *
          ∏ σ ∈ c.history.leaves, K σ :=
        c.history.lineageValue_eq_multiplier_product c.good K
  have habs : |t.coefficient ρ| =
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
  have hcoarse := lineageCharge_coarse_coefficient_bound
    (t.coefficient ρ) (c.history.activeLineageProduct K) c.history.leaves H
    (basicLemmaNeighborhood boundary k E ρ) c.history.multiplierCount
    habs hproduct c.history.leaves_nonempty hPN hHN hformula
  have hcompat : IsCompatible E ρ := hT.parented t ht ρ hρ
  have hNA := basicLemmaNeighborhood_count boundary hL k E hE ρ hcompat
  have hrefined := lineageCharge_refined_coefficient_bound
    (t.coefficient ρ) (c.history.activeLineageProduct K) c.history.leaves H
    (basicLemmaNeighborhood boundary k E ρ) c.history.multiplierCount
    (chargeA boundary L ρ (basicLemmaPreviousScale k)) habs hproduct
    c.history.leaves_nonempty hPN hHN hformula hNA
  exact ⟨c, H, hHE, hdisj, hformula, hnear,
    c.history.good_sourceConnected c.good hE.1, hsigned, hcoarse, hrefined⟩

end FroehlichSpencer.BKT

end
