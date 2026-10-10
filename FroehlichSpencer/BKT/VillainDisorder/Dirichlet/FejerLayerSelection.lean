/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.VillainDisorder.Dirichlet.FejerLayerMixture
public import FroehlichSpencer.BKT.Generic.PinnedCharges.LayerMixture
public import FroehlichSpencer.BKT.Generic.PinnedCharges.LayerRun

/-! # Fejér branches through the Appendix D selector

The four-branch selection depends on supports and scales, not on the coefficient values.  A run
from the Fejér activities can therefore be replayed from the larger comb activities with exactly
the same terminal geometry.  The coefficient rewrites preserve pointwise domination, which gives
the cutoff-uniform entropy bound from the already proved comb estimate.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.VillainDisorder.Dirichlet

open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Generic.PinnedCharges
open FroehlichSpencer.BKT.Generic.PinnedCharges.Layer
open FroehlichSpencer.BKT.Generic.PinnedCharges.SelectionG

/--
Two selector states have the same geometric data when scale, active and  charges agree.
-/
def sameSelShape {L : ℕ} (S T : SelConfig L) : Prop :=
  S.j = T.j ∧ S.A = T.A ∧ S.F = T.F

/-- A terminal Fejér selector branch can be paired with a comb terminal having the same geometry,
and whose coefficients dominate the Fejér coefficients. -/
def HasCombTerminalReference {L N : ℕ} (T : SelConfig L) : Prop :=
  ∃ T', IsCombTerminal N T' ∧ sameSelShape T T' ∧ ∀ ρ, |T.K ρ| ≤ |T'.K ρ|

private theorem abs_pairRewriteFirstCoefficient_le {L : ℕ} {K K' : ChargeDensity L → ℝ}
    (hK : ∀ ρ, |K ρ| ≤ |K' ρ|) (a ρ : ChargeDensity L) :
    |pairRewriteFirstCoefficient K a ρ| ≤ |pairRewriteFirstCoefficient K' a ρ| := by
  by_cases hρ : ρ = a
  · simpa [pairRewriteFirstCoefficient, hρ, abs_mul] using
      mul_le_mul_of_nonneg_left (hK a) (abs_nonneg (3 : ℝ))
  · simp [pairRewriteFirstCoefficient, hρ, hK ρ]

private theorem abs_pairRewriteSecondCoefficient_le {L : ℕ} {K K' : ChargeDensity L → ℝ}
    (hK : ∀ ρ, |K ρ| ≤ |K' ρ|) (a ρ : ChargeDensity L) :
    |pairRewriteSecondCoefficient K a ρ| ≤ |pairRewriteSecondCoefficient K' a ρ| := by
  by_cases hρ : ρ = a
  · simpa [pairRewriteSecondCoefficient, hρ, abs_mul] using
      mul_le_mul_of_nonneg_left (hK a) (abs_nonneg (3 : ℝ))
  · simp [pairRewriteSecondCoefficient, hρ, hK ρ]

private theorem abs_pairRewriteDifferenceCoefficient_le {L : ℕ}
    {K K' : ChargeDensity L → ℝ} (hK : ∀ ρ, |K ρ| ≤ |K' ρ|)
    (a c ρ : ChargeDensity L) :
    |pairRewriteDifferenceCoefficient K a c ρ| ≤
      |pairRewriteDifferenceCoefficient K' a c ρ| := by
  by_cases hρ : ρ = a - c
  · simp only [pairRewriteDifferenceCoefficient, ite_eq_left hρ, abs_mul,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
    have hprod : |K a| * |K c| ≤ |K' a| * |K' c| :=
      mul_le_mul (hK a) (hK c) (abs_nonneg _) (abs_nonneg _)
    calc
      3 * |K a| * |K c| = 3 * (|K a| * |K c|) := by ring
      _ ≤ 3 * (|K' a| * |K' c|) :=
        mul_le_mul_of_nonneg_left hprod (by norm_num)
      _ = 3 * |K' a| * |K' c| := by ring
  · simp [pairRewriteDifferenceCoefficient, hρ, hK ρ]

private theorem abs_pairRewriteSumCoefficient_le {L : ℕ}
    {K K' : ChargeDensity L → ℝ} (hK : ∀ ρ, |K ρ| ≤ |K' ρ|)
    (a c ρ : ChargeDensity L) :
    |pairRewriteSumCoefficient K a c ρ| ≤
      |pairRewriteSumCoefficient K' a c ρ| := by
  by_cases hρ : ρ = a + c
  · simp only [pairRewriteSumCoefficient, ite_eq_left hρ, abs_mul,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
    have hprod : |K a| * |K c| ≤ |K' a| * |K' c| :=
      mul_le_mul (hK a) (hK c) (abs_nonneg _) (abs_nonneg _)
    calc
      3 * |K a| * |K c| = 3 * (|K a| * |K c|) := by ring
      _ ≤ 3 * (|K' a| * |K' c|) :=
        mul_le_mul_of_nonneg_left hprod (by norm_num)
      _ = 3 * |K' a| * |K' c| := by ring
  · simp [pairRewriteSumCoefficient, hρ, hK ρ]

/-- Replay one selection step with the same geometric data and a dominating coefficient function. -/
theorem selStep_replay_dom {L : ℕ} {M α : ℝ} {S T S' : SelConfig L}
    (hstep : SelStep M α S T) (hshape : sameSelShape S' S)
    (hdom : ∀ ρ, |S.K ρ| ≤ |S'.K ρ|) :
    ∃ T', SelStep M α S' T' ∧ sameSelShape T' T ∧
      ∀ ρ, |T.K ρ| ≤ |T'.K ρ| := by
  rcases hshape with ⟨hj, hA, hF⟩
  have hscale : S'.scale = S.scale := by simp [SelConfig.scale, hj]
  cases hstep with
  | keepLeft ha hc hne hD =>
      refine ⟨⟨S'.j, S'.A.erase _, S'.F, pairRewriteFirstCoefficient S'.K _⟩,
        SelStep.keepLeft ?_ ?_ hne ?_, ?_, ?_⟩
      · rw [hA]
        exact ha
      · rw [hA]
        exact hc
      · simpa [hscale] using hD
      · simp [sameSelShape, hj, hA, hF]
      · intro ρ
        exact abs_pairRewriteFirstCoefficient_le hdom _ _
  | keepRight ha hc hne hD =>
      refine ⟨⟨S'.j, S'.A.erase _, S'.F, pairRewriteSecondCoefficient S'.K _⟩,
        SelStep.keepRight ?_ ?_ hne ?_, ?_, ?_⟩
      · rw [hA]
        exact ha
      · rw [hA]
        exact hc
      · simpa [hscale] using hD
      · simp [sameSelShape, hj, hA, hF]
      · intro ρ
        exact abs_pairRewriteSecondCoefficient_le hdom _ _
  | mergeSub ha hc hne hD =>
      refine ⟨⟨S'.j, insert (_ - _) ((S'.A.erase _).erase _), S'.F,
          pairRewriteDifferenceCoefficient S'.K _ _⟩,
        SelStep.mergeSub ?_ ?_ hne ?_, ?_, ?_⟩
      · rw [hA]
        exact ha
      · rw [hA]
        exact hc
      · simpa [hscale] using hD
      · simp [sameSelShape, hj, hA, hF]
      · intro ρ
        exact abs_pairRewriteDifferenceCoefficient_le hdom _ _ _
  | mergeAdd ha hc hne hD =>
      refine ⟨⟨S'.j, insert (_ + _) ((S'.A.erase _).erase _), S'.F,
          pairRewriteSumCoefficient S'.K _ _⟩,
        SelStep.mergeAdd ?_ ?_ hne ?_, ?_, ?_⟩
      · rw [hA]
        exact ha
      · rw [hA]
        exact hc
      · simpa [hscale] using hD
      · simp [sameSelShape, hj, hA, hF]
      · intro ρ
        exact abs_pairRewriteSumCoefficient_le hdom _ _ _
  | @freeze J hfar hJ =>
      have hfar' : ∀ ρ ∈ S'.A, ∀ σ ∈ S'.A, ρ ≠ σ →
          2 * S'.scale < euclideanSetDistance (chargeSupport ρ) (chargeSupport σ) := by
        intro ρ hρ σ hσ hne
        exact (hscale ▸ hfar ρ (hA ▸ hρ) σ (hA ▸ hσ) hne)
      have hJ' : IsMaximalFreezeSet M α S'.A J := by
        simpa [hA] using hJ
      refine ⟨⟨S'.j + 1, S'.A \ _, S'.F ∪ _, S'.K⟩,
        SelStep.freeze hfar' hJ', ?_, ?_⟩
      · simp [sameSelShape, hj, hA, hF]
      · exact hdom

/-- Replay an entire finite selection path while preserving its terminal geometry and coefficient
domination. -/
theorem selReach_replay_dom {L : ℕ} {M α : ℝ} {S T S' : SelConfig L}
    (hreach : SelReach M α S T) (hshape : sameSelShape S' S)
    (hdom : ∀ ρ, |S.K ρ| ≤ |S'.K ρ|) :
    ∃ T', SelReach M α S' T' ∧ sameSelShape T' T ∧
      ∀ ρ, |T.K ρ| ≤ |T'.K ρ| := by
  revert S' hshape hdom
  induction hreach with
  | refl =>
      intro S' hshape hdom
      exact ⟨S', Relation.ReflTransGen.refl, hshape, hdom⟩
  | @tail U V hreach hstep ih =>
      intro S' hshape hdom
      obtain ⟨U', hreach', hshape', hdom'⟩ := ih hshape hdom
      obtain ⟨T', hstep', hshape'', hdom''⟩ :=
        selStep_replay_dom hstep hshape' hdom'
      exact ⟨T', Relation.ReflTransGen.tail hreach' hstep', hshape'', hdom''⟩

/-- The run expansion from the Fejér activities on one frequency assignment. -/
def fejerRuns {L : ℕ} (N : ℕ) (f : Site L → ℕ) : List (ℝ × SelConfig L) :=
  if hf : ∀ x, 1 ≤ f x then
    Classical.choose (exists_runExpansion one_lt_chargeCoverScale one_le_chargeCoverExponent
      (SelConfig.start_valid one_lt_chargeCoverScale one_le_chargeCoverExponent
        (singleSiteEnsemble_pinned hf) (singleSiteEnsemble_card_support hf) (fejerActivity N)))
  else []

/-- The convex mixture of all Fejér frequency assignments and their terminal selector branches. -/
def fejerBranches (L N : ℕ) : List (ℝ × SelConfig L) :=
  (combAssignments L N).toList.flatMap fun f =>
    scaleRun (∏ x, combWeight N (f x)) (fejerRuns N f)

theorem fejerRuns_spec {L N : ℕ} (f : Site L → ℕ) (hf : ∀ x, 1 ≤ f x) :
    IsRunExpansion (chargeCoverScale : ℝ) chargeCoverExponent
      (SelConfig.start (singleSiteEnsemble f) (fejerActivity N)) (fejerRuns N f) := by
  unfold fejerRuns
  split_ifs
  exact Classical.choose_spec (exists_runExpansion one_lt_chargeCoverScale
    one_le_chargeCoverExponent (SelConfig.start_valid one_lt_chargeCoverScale
      one_le_chargeCoverExponent (singleSiteEnsemble_pinned hf)
        (singleSiteEnsemble_card_support hf) (fejerActivity N)))

/-- Fejér assignments have positive mass, comb-terminal reference geometry, and total mass one;
their branch expansion is the sitewise Fejér product. -/
theorem fejerBranches_spec {L N : ℕ} (hN : 1 ≤ N) :
    (∀ b ∈ fejerBranches L N,
      0 < b.1 ∧ b.2.A = ∅ ∧ HasCombTerminalReference (L := L) (N := N) b.2) ∧
      ((fejerBranches L N).map fun b => b.1).sum = 1 ∧
      ∀ φ : Site L → ℝ,
        ∏ x, fejerPolynomial N (φ x) =
          ((fejerBranches L N).map fun b => b.1 *
            chargeFactorProduct b.2.F b.2.K φ).sum := by
  classical
  refine ⟨fun b hb => ?_, ?_, fun φ => ?_⟩
  · obtain ⟨f, hfmem, hb⟩ := List.mem_flatMap.mp hb
    have hf := mem_combAssignments (Finset.mem_toList.mp hfmem)
    obtain ⟨b', hb', rfl⟩ := List.mem_map.mp hb
    have hrun := fejerRuns_spec (N := N) f (fun x => (hf x).1)
    obtain ⟨hw, hA, hreach⟩ := hrun.1 b' hb'
    have hshape0 : sameSelShape
        (SelConfig.start (singleSiteEnsemble f) (combActivity N))
        (SelConfig.start (singleSiteEnsemble f) (fejerActivity N)) := by
      simp [sameSelShape, SelConfig.start]
    have hdom0 : ∀ ρ : ChargeDensity L,
        |fejerActivity N ρ| ≤ |combActivity N ρ| :=
      fun ρ => fejerActivity_abs_le_combActivity (L := L) (N := N) ρ
    obtain ⟨T', hreach', hshape', hdom'⟩ :=
      selReach_replay_dom hreach hshape0 hdom0
    have hshape'' : sameSelShape b'.2 T' := by
      rcases hshape' with ⟨hj, hA', hF⟩
      exact ⟨hj.symm, hA'.symm, hF.symm⟩
    have hA' : T'.A = ∅ := by
      rcases hshape' with ⟨_, hA', _⟩
      rw [hA', hA]
    have hcomb : IsCombTerminal N T' :=
      ⟨hA', f, hf, hreach'⟩
    have hw' : 0 < (∏ x, combWeight N (f x)) * b'.1 :=
      mul_pos (Finset.prod_pos fun x _ => combWeight_pos hN (f x)) hw
    refine ⟨hw', hA, T', hcomb, hshape'', hdom'⟩
  · unfold fejerBranches
    rw [sum_map_flatMap]
    have hinner : ∀ f ∈ (combAssignments L N).toList,
        ((scaleRun (∏ x, combWeight N (f x)) (fejerRuns N f)).map fun b => b.1).sum =
          ∏ x, combWeight N (f x) := by
      intro f hfmem
      have hf := mem_combAssignments (Finset.mem_toList.mp hfmem)
      rw [sum_scaleRun_weight,
        (fejerRuns_spec (N := N) f (fun x => (hf x).1)).2.1, mul_one]
    rw [List.map_congr_left hinner, Finset.sum_map_toList]
    unfold combAssignments
    rw [← Finset.prod_univ_sum]
    exact Finset.prod_eq_one fun x _ => sum_combWeight hN
  · rw [prod_fejerPolynomial_eq_singleSiteMixture hN]
    unfold fejerBranches
    rw [sum_map_flatMap]
    have hinner : ∀ f ∈ (combAssignments L N).toList,
        ((scaleRun (∏ x, combWeight N (f x)) (fejerRuns N f)).map
          fun b => b.1 * chargeFactorProduct b.2.F b.2.K φ).sum =
          (∏ x, combWeight N (f x)) *
            chargeFactorProduct (singleSiteEnsemble f) (fejerActivity N) φ := by
      intro f hfmem
      have hf := mem_combAssignments (Finset.mem_toList.mp hfmem)
      rw [sum_scaleRun_prod]
      have hspec := (fejerRuns_spec (N := N) f (fun x => (hf x).1)).2.2 φ
      have hspec' : chargeFactorProduct (singleSiteEnsemble f) (fejerActivity N) φ =
          ((fejerRuns N f).map fun b : ℝ × SelConfig L =>
            b.1 * chargeFactorProduct b.2.F b.2.K φ).sum := by
        simpa only [SelConfig.start, Finset.union_empty] using hspec
      have hmul := congrArg (fun y => (∏ x, combWeight N (f x)) * y) hspec'
      exact hmul.symm
    rw [List.map_congr_left hinner, Finset.sum_map_toList]
    unfold combAssignments
    rfl

end FroehlichSpencer.BKT.VillainDisorder.Dirichlet

end
