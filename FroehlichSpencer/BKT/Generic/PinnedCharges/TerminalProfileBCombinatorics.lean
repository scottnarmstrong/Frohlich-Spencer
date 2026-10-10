/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.PinnedCharges.TerminalProfileGSplit
public import FroehlichSpencer.BKT.Generic.PinnedCharges.BoundaryEnergyPairing
public import FroehlichSpencer.BKT.Generic.PinnedCharges.SelectionGGeometry
public import FroehlichSpencer.BKT.Generic.PinnedCharges.SelectionGFreeze

/-! # The finite laminar-family estimate for neutral selected clusters -/

@[expose] public section

namespace FroehlichSpencer.BKT.Generic.PinnedCharges.Layer

open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Rotator
open FroehlichSpencer.BKT.Generic.PinnedCharges.SelectionG

variable {α : Type*} [DecidableEq α]

/-- A family is laminar when any two distinct members are nested or disjoint. -/
def IsLaminarFamily (F : Finset (Finset α)) : Prop :=
  ∀ A ∈ F, ∀ B ∈ F, A ≠ B → Disjoint A B ∨ A ⊆ B ∨ B ⊆ A

/-- A laminar family of sets of size at least two has at most `|U|` members. -/
theorem laminarFamily_card_bounds
    (U : Finset α) (F : Finset (Finset α))
    (hsub : ∀ A ∈ F, A ⊆ U)
    (hsize : ∀ A ∈ F, 2 ≤ A.card)
    (hlam : IsLaminarFamily F) : F.card ≤ U.card ∧
      (F.Nonempty → F.card + 1 ≤ U.card) := by
  classical
  let P : ℕ → Prop := fun n =>
    ∀ U : Finset α, U.card = n → ∀ F : Finset (Finset α),
      (∀ A ∈ F, A ⊆ U) → (∀ A ∈ F, 2 ≤ A.card) → IsLaminarFamily F →
        F.card ≤ n ∧ (F.Nonempty → F.card + 1 ≤ n)
  have hP : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro U hUn F hsub hsize hlam
        by_cases hF : F.Nonempty
        · have hUtwo : 2 ≤ U.card := by
            obtain ⟨A, hA⟩ := hF
            exact (hsize A hA).trans (Finset.card_le_card (hsub A hA))
          let c := (F.image Finset.card).min' (Finset.image_nonempty.mpr hF)
          have hc_mem : c ∈ F.image Finset.card := Finset.min'_mem _ _
          obtain ⟨A, hA, hAc⟩ := Finset.mem_image.mp hc_mem
          have hAmin (B : Finset α) (hB : B ∈ F) : A.card ≤ B.card := by
            rw [hAc]
            exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨B, hB, rfl⟩)
          have hA2 := hsize A hA
          have hApos : 0 < A.card := by omega
          obtain ⟨a, ha⟩ := Finset.card_pos.mp hApos
          let F₀ := F.erase A
          let F' := F₀.image fun B : Finset α => B.erase a
          have hclass (B : Finset α) (hB : B ∈ F₀) :
              Disjoint A B ∨ A ⊆ B := by
            have hBF : B ∈ F := Finset.mem_of_mem_erase hB
            have hBA : B ≠ A := (Finset.mem_erase.mp hB).1
            rcases hlam A hA B hBF hBA.symm with hd | hrest
            · exact Or.inl hd
            · rcases hrest with hAB | hBA'
              · exact Or.inr hAB
              · have hlt : B.card < A.card :=
                  Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hBA', hBA⟩)
                exact (not_lt_of_ge (hAmin B hBF) hlt).elim
          have hEraseA : (A.erase a).Nonempty := by
            have hcA := Finset.card_erase_of_mem ha
            have : 0 < (A.erase a).card := by rw [hcA]; omega
            exact Finset.card_pos.mp this
          have hInject : Set.InjOn (fun B : Finset α => B.erase a) F₀ := by
            intro B hB C hC hEq
            change B.erase a = C.erase a at hEq
            have hBF : B ∈ F := Finset.mem_of_mem_erase hB
            have hCF : C ∈ F := Finset.mem_of_mem_erase hC
            rcases hclass B hB with hdB | hAB
            · rcases hclass C hC with hdC | hAC
              · simpa [Finset.erase_eq_of_notMem (fun haB =>
                    (Finset.disjoint_left.mp hdB) ha haB),
                  Finset.erase_eq_of_notMem (fun haC =>
                    (Finset.disjoint_left.mp hdC) ha haC)] using hEq
              · have hsubC : A.erase a ⊆ B.erase a := by
                  have hsub : A.erase a ⊆ C.erase a := Finset.erase_subset_erase a hAC
                  rw [← hEq] at hsub
                  exact hsub
                obtain ⟨x, hx⟩ := hEraseA
                have hxA : x ∈ A := Finset.mem_of_mem_erase hx
                have hxB : x ∈ B.erase a := hsubC hx
                exact False.elim ((Finset.disjoint_left.mp hdB) hxA
                  (Finset.mem_of_mem_erase hxB))
            · rcases hclass C hC with hdC | hAC
              · have hsubA : A.erase a ⊆ C.erase a := by
                  have hsub : A.erase a ⊆ B.erase a := Finset.erase_subset_erase a hAB
                  rw [hEq] at hsub
                  exact hsub
                obtain ⟨x, hx⟩ := hEraseA
                have hxA : x ∈ A := Finset.mem_of_mem_erase hx
                have hxC : x ∈ C.erase a := hsubA hx
                exact False.elim ((Finset.disjoint_left.mp hdC) hxA
                  (Finset.mem_of_mem_erase hxC))
              · have haB : a ∈ B := hAB ha
                have haC : a ∈ C := hAC ha
                have hIns : insert a (B.erase a) = insert a (C.erase a) :=
                  congrArg (insert a) hEq
                simpa [Finset.insert_erase haB, Finset.insert_erase haC] using hIns
          have hFcard : F'.card = F.card - 1 := by
            dsimp [F', F₀]
            rw [Finset.card_image_iff.mpr hInject, Finset.card_erase_of_mem hA]
          have hFsub' : ∀ B ∈ F', B ⊆ U.erase a := by
            intro B hB
            obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hB
            have hCA := hsub C (Finset.mem_of_mem_erase hC)
            intro x hx
            rcases Finset.mem_erase.mp hx with ⟨hxa, hxC⟩
            exact Finset.mem_erase.mpr ⟨hxa, hCA hxC⟩
          have hFsize' : ∀ B ∈ F', 2 ≤ B.card := by
            intro B hB
            obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hB
            rcases hclass C hC with hd | hAC
            · have haC : a ∉ C := by
                intro haC
                exact (Finset.disjoint_left.mp hd) ha haC
              simpa [Finset.erase_eq_of_notMem haC] using hsize C (Finset.mem_of_mem_erase hC)
            · have haC : a ∈ C := hAC ha
              have hneq : C ≠ A := (Finset.mem_erase.mp hC).1
              have hlt : A.card < C.card :=
                Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hAC, hneq.symm⟩)
              rw [Finset.card_erase_of_mem haC]
              have hA2 := hsize A hA
              omega
          have hlam' : IsLaminarFamily F' := by
            intro B hB C hC hne
            obtain ⟨B₀, hB₀, rfl⟩ := Finset.mem_image.mp hB
            obtain ⟨C₀, hC₀, rfl⟩ := Finset.mem_image.mp hC
            have hB0F := Finset.mem_of_mem_erase hB₀
            have hC0F := Finset.mem_of_mem_erase hC₀
            rcases hlam B₀ hB0F C₀ hC0F (by
              intro hEq
              exact hne (congrArg (fun X : Finset α => X.erase a) hEq)) with hd | hBC | hCB
            · left
              rw [Finset.disjoint_left]
              intro x hxB hxC
              exact Finset.disjoint_left.mp hd (Finset.mem_of_mem_erase hxB)
                (Finset.mem_of_mem_erase hxC)
            · exact Or.inr (Or.inl (Finset.erase_subset_erase a hBC))
            · exact Or.inr (Or.inr (Finset.erase_subset_erase a hCB))
          have hUcard : (U.erase a).card = n - 1 := by
            rw [Finset.card_erase_of_mem (hsub A hA ha)]
            omega
          have hrec := ih (n - 1) (by omega) (U.erase a) hUcard F'
            hFsub' hFsize' hlam'
          rw [hFcard] at hrec
          refine ⟨?_, ?_⟩
          · omega
          · intro hFne
            by_cases hF' : F'.Nonempty
            · have hs := hrec.2 hF'
              omega
            · have hF'empty : F' = ∅ := Finset.not_nonempty_iff_eq_empty.mp hF'
              have hF'card : F'.card = 0 := by rw [hF'empty]; simp
              have hFpos : 0 < F.card := Finset.card_pos.mpr hF
              have hFone : F.card = 1 := by rw [hFcard] at hF'card; omega
              have hn2 : 2 ≤ n := by simpa [hUn] using hUtwo
              omega
        · have hFeq : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hF
          rw [hFeq]
          refine ⟨by simp, ?_⟩
          intro hFn
          simp at hFn
  exact hP U.card U rfl F hsub hsize hlam

/-- A laminar family of sets of size at least two has at most `|U|` members. -/
theorem laminarFamily_card_le_universe
    (U : Finset α) (F : Finset (Finset α))
    (hsub : ∀ A ∈ F, A ⊆ U)
    (hsize : ∀ A ∈ F, 2 ≤ A.card)
    (hlam : IsLaminarFamily F) : F.card ≤ U.card :=
  (laminarFamily_card_bounds U F hsub hsize hlam).1

/-- A nonempty laminar family of sets of size at least two has at most `|U|-1` members. -/
theorem laminarFamily_card_add_one_le_universe_of_nonempty
    (U : Finset α) (F : Finset (Finset α)) (hF : F.Nonempty)
    (hsub : ∀ A ∈ F, A ⊆ U)
    (hsize : ∀ A ∈ F, 2 ≤ A.card)
    (hlam : IsLaminarFamily F) : F.card + 1 ≤ U.card := by
  exact (laminarFamily_card_bounds U F hsub hsize hlam).2 hF

variable {L : ℕ}

/-- At a selected scale, if the restricted cluster's diameter is no larger than the nominal side,
Appendix D isolation makes its total charge nonzero. -/
theorem selectedRestriction_charged_of_diameter_le_scale
    (j : ℕ) (ρ : ChargeDensity L) (N : Finset (ChargeDensity L))
    (hN : HasBoundaryIsolation (chargeCoverScale : ℝ) chargeCoverExponent N)
    (hρ : ρ ∈ N) (C : Finset (Finset (Site L)))
    (hC : IsMinimumSquareCover .free L j ρ C) (s : Finset (Site L))
    (hs : s ∈ pinnedPPrime (chargeCoverScale : ℝ) chargeCoverExponent j ρ C)
    (hdiam : chargeEuclideanDiameter (chargeRestriction ρ s) ≤ (2 : ℝ) ^ j) :
    totalCharge (chargeRestriction ρ s) ≠ 0 := by
  classical
  let child := chargeRestriction ρ s
  have hsC : s ∈ C := pinnedPPrime_mem_of_minimumCover
    chargeCoverScale chargeCoverExponent j ρ C hC hs |>.1
  have hchildconst : IsConstituent ρ child := by
    simpa [child] using boundaryEnergy_squareRestriction_isConstituent j ρ C hC hsC
  by_cases hsingle : C.card = 1
  · have hkeep : totalCharge ρ ≠ 0 ∧
        singletonBoundaryMargin j ≤ chargeBoundaryDistance ρ := by
      by_contra hkeep
      have hempty := pinnedPPrime_eq_empty_of_singleton_exception_fails
        (chargeCoverScale : ℝ) chargeCoverExponent j ρ C hsingle hkeep
      rw [hempty] at hs
      exact Finset.notMem_empty _ hs
    obtain ⟨u, hu⟩ := Finset.card_eq_one.mp hsingle
    have hus : s = u := by simpa [hu] using hsC
    have hsupport : chargeSupport ρ ⊆ s := by
      intro x hx
      obtain ⟨t, ht, hxt⟩ := hC.1.2 x hx
      have htu : t = u := by simpa [hu] using ht
      simpa [hus, htu] using hxt
    have hsame : child = ρ := by
      funext x
      by_cases hxs : x ∈ s
      · simp [child, chargeRestriction, hxs]
      · have hxzero : ρ x = 0 := by
          by_contra hxne
          exact hxs (hsupport (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxne⟩))
        simp [child, chargeRestriction, hxs, hxzero]
    change totalCharge child ≠ 0
    rw [hsame]
    exact hkeep.1
  · have hsdata := (mem_pinnedPPrime_of_cover_card_ne_one
        (chargeCoverScale : ℝ) chargeCoverExponent j ρ C hsingle s).1 hs
    rcases hsdata with ⟨hsC, hsep, _hboundary⟩
    obtain ⟨x₀, hx₀ρ, hx₀s, _⟩ :=
      minimumCover_square_has_private_support_site j ρ C hC hsC
    let residual : ChargeDensity L := fun x => ρ x - child x
    have hchildne : child ≠ 0 := hchildconst.1
    have hresne : residual ≠ 0 := by
      obtain ⟨t, ht, hts⟩ : ∃ t ∈ C, t ≠ s := by
        by_contra h
        have hall : ∀ t ∈ C, t = s := by
          intro u hu
          by_contra hne
          exact h ⟨u, hu, hne⟩
        have hcard : C.card ≤ 1 := Finset.card_le_one.mpr fun a ha b hb =>
          (hall a ha).trans (hall b hb).symm
        have hpos : 0 < C.card := Finset.card_pos.mpr ⟨s, hsC⟩
        omega
      obtain ⟨x₁, hx₁ρ, hx₁t, hprivate₁⟩ :=
        minimumCover_square_has_private_support_site j ρ C hC ht
      have hx₁s : x₁ ∉ s := by
        intro hx
        exact hprivate₁ s hsC (Ne.symm hts) hx
      have hρx₁ : ρ x₁ ≠ 0 := (Finset.mem_filter.mp hx₁ρ).2
      have hval : residual x₁ ≠ 0 := by
        simpa [residual, child, chargeRestriction, hx₁s] using hρx₁
      exact fun hz => hval (congrFun hz x₁)
    have hresOutside : ∀ x ∈ chargeSupport residual, x ∉ s := by
      intro x hx hxs
      have hxzero : residual x = 0 := by simp [residual, child, chargeRestriction, hxs]
      exact (Finset.mem_filter.mp hx).2 hxzero
    have hpairEvery {x y : Site L} (hx : x ∈ chargeSupport child)
        (hy : y ∈ chargeSupport residual) :
        2 * (chargeCoverScale : ℝ) * ((2 : ℝ) ^ j) ^ chargeCoverExponent ≤
          euclideanSiteDistance x y := by
      have hxs : x ∈ s := (mem_chargeSupport_restriction_iff ρ s x).mp hx |>.1
      have hys : y ∉ s := hresOutside y hy
      have hρy : ρ y ≠ 0 := by
        simpa [residual, child, chargeRestriction, hys] using
          (Finset.mem_filter.mp hy).2
      obtain ⟨t, ht, hyt⟩ := hC.1.2 y
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hρy⟩)
      have hts : t ≠ s := by
        intro h
        subst t
        exact hys hyt
      have hscale : ((2 : ℝ) ^ j) ^ chargeCoverExponent =
          (2 : ℝ) ^ (chargeCoverExponent * (j : ℝ)) := by
        calc
          ((2 : ℝ) ^ j) ^ chargeCoverExponent =
              (2 : ℝ) ^ ((j : ℝ) * chargeCoverExponent) := by
                rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
          _ = (2 : ℝ) ^ (chargeCoverExponent * (j : ℝ)) :=
            congrArg (fun z : ℝ => (2 : ℝ) ^ z) (by ring)
      calc
        2 * (chargeCoverScale : ℝ) * ((2 : ℝ) ^ j) ^ chargeCoverExponent =
            2 * (chargeCoverScale : ℝ) *
              (2 : ℝ) ^ (chargeCoverExponent * (j : ℝ)) := by rw [hscale]
        _ ≤ euclideanSetDistance s t := hsep t ht hts
        _ ≤ euclideanSiteDistance x y := SelectionG.setDist_le_siteDist hxs hyt
    have hdist : 2 * (chargeCoverScale : ℝ) * ((2 : ℝ) ^ j) ^ chargeCoverExponent ≤
        euclideanSetDistance (chargeSupport child) (chargeSupport residual) :=
      SelectionG.le_setDist (chargeSupport_nonempty_of_ne_zero child hchildne)
        (chargeSupport_nonempty_of_ne_zero residual hresne) (fun x hx y hy => hpairEvery hx hy)
    have hdiamPow : chargeEuclideanDiameter child ^ chargeCoverExponent ≤
        ((2 : ℝ) ^ j) ^ chargeCoverExponent :=
      Real.rpow_le_rpow (SelectionG.diam_nonneg _) hdiam (by norm_num [chargeCoverExponent])
    have htrigger : 2 * (chargeCoverScale : ℝ) *
        chargeEuclideanDiameter child ^ chargeCoverExponent ≤
        euclideanSetDistance (chargeSupport child) (chargeSupport residual) := by
      calc
        2 * (chargeCoverScale : ℝ) * chargeEuclideanDiameter child ^ chargeCoverExponent ≤
            2 * (chargeCoverScale : ℝ) * ((2 : ℝ) ^ j) ^ chargeCoverExponent :=
          mul_le_mul_of_nonneg_left hdiamPow (by positivity)
        _ ≤ euclideanSetDistance (chargeSupport child) (chargeSupport residual) := hdist
    exact (hN ρ hρ child hchildconst (by simpa [residual] using htrigger)).1

/-- Bad selected squares are exactly the neutral restrictions in the selected family. -/
noncomputable def badSelectedSquares (ϱ : RotatorDualFace L → ℤ) (j : ℕ) :
    Finset (Finset (Site L)) :=
  (selectedSquares ϱ j).filter fun s =>
    ¬ totalCharge (chargeRestriction (siteRestrict ϱ) s) ≠ 0

/-- A selected occurrence is recorded with both its scale and its square. -/
abbrev BadSelectedIndex (ϱ : RotatorDualFace L → ℤ) :=
  Σ j : {j // j ∈ Finset.Icc 1 (layerCutoff ϱ)},
    {s // s ∈ badSelectedSquares ϱ j.1}

/-- The support cluster carried by a bad selected occurrence. -/
def badSelectedCluster (ϱ : RotatorDualFace L → ℤ) (i : BadSelectedIndex ϱ) :
    Finset (Site L) :=
  chargeSupport (chargeRestriction (siteRestrict ϱ) i.2.1)

/-- The finite family obtained by forgetting the scale and square labels. -/
noncomputable def badSelectedClusterFamily (ϱ : RotatorDualFace L → ℤ) :
    Finset (Finset (Site L)) := by
  classical
  exact Finset.univ.image (badSelectedCluster ϱ)

/-- The bad selected count is exactly the cardinality of its occurrence index type. -/
theorem badSelectedSum_eq_index_card (ϱ : RotatorDualFace L → ℤ) :
    badSelectedSum ϱ = (Fintype.card (BadSelectedIndex ϱ) : ℝ) := by
  classical
  have hcount : Fintype.card (BadSelectedIndex ϱ) =
      ∑ j ∈ Finset.Icc 1 (layerCutoff ϱ), (badSelectedSquares ϱ j).card := by
    rw [Fintype.card_sigma]
    simp only [Fintype.card_coe]
    simpa only [Finset.univ_eq_attach] using
      (Finset.sum_attach (Finset.Icc 1 (layerCutoff ϱ))
        (fun j : ℕ => (badSelectedSquares ϱ j).card))
  unfold badSelectedSum
  rw [hcount]
  simp [badSelectedSquares, selectedSquares, Nat.cast_sum]

/-- Geometric facts about one neutral selected cluster, before using terminal isolation. -/
theorem badSelectedCluster_data (ϱ : RotatorDualFace L → ℤ) (j : ℕ)
    {s : Finset (Site L)} (hs : s ∈ badSelectedSquares ϱ j) :
    chargeRestriction (siteRestrict ϱ) s ≠ 0 ∧
      totalCharge (chargeRestriction (siteRestrict ϱ) s) = 0 ∧
      chargeSupport (chargeRestriction (siteRestrict ϱ) s) ⊆ chargeSupport (siteRestrict ϱ) ∧
      2 ≤ (chargeSupport (chargeRestriction (siteRestrict ϱ) s)).card ∧
      chargeEuclideanDiameter (chargeRestriction (siteRestrict ϱ) s) ≤
        Real.sqrt 2 * (2 : ℝ) ^ j ∧
      (boundaryEntropyMinimumCover (siteRestrict ϱ) j).card ≠ 1 := by
  classical
  have hsParts := Finset.mem_filter.mp hs
  have hsSelected := hsParts.1
  have hneutral : totalCharge (chargeRestriction (siteRestrict ϱ) s) = 0 := by
    by_contra hne
    exact hsParts.2 hne
  have hsPrime : s ∈ pinnedPPrime (chargeCoverScale : ℝ) chargeCoverExponent j
      (siteRestrict ϱ) (boundaryEntropyMinimumCover (siteRestrict ϱ) j) := hsSelected
  have hC : IsMinimumSquareCover .free L j (siteRestrict ϱ)
      (boundaryEntropyMinimumCover (siteRestrict ϱ) j) :=
    boundaryEntropyMinimumCover_isMinimum _ _
  have hsCover := pinnedPPrime_mem_of_minimumCover chargeCoverScale
    chargeCoverExponent j (siteRestrict ϱ) (boundaryEntropyMinimumCover (siteRestrict ϱ) j)
    hC hsPrime
  have hconst : IsConstituent (siteRestrict ϱ)
      (chargeRestriction (siteRestrict ϱ) s) := by
    exact boundaryEnergy_squareRestriction_isConstituent j (siteRestrict ϱ)
      (boundaryEntropyMinimumCover (siteRestrict ϱ) j) hC hsCover.1
  refine ⟨hconst.1, hneutral, hconst.2.1, ?_, ?_, ?_⟩
  · have hnotone : (chargeSupport (chargeRestriction (siteRestrict ϱ) s)).card ≠ 1 := by
      intro hone
      obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hone
      exact (FroehlichSpencer.BKT.Generic.PinnedCharges.SelectionG.SelectionState.totalCharge_ne_zero_of_support_singleton hx)
        hneutral
    have hpos : 0 < (chargeSupport (chargeRestriction (siteRestrict ϱ) s)).card :=
      Finset.card_pos.mpr (chargeSupport_nonempty_of_ne_zero _ hconst.1)
    omega
  · have hchildsupp :
        (chargeSupport (chargeRestriction (siteRestrict ϱ) s)).Nonempty :=
      chargeSupport_nonempty_of_ne_zero _ hconst.1
    have hsnonempty : s.Nonempty := hchildsupp.mono (by
      intro x hx
      exact (mem_chargeSupport_restriction_iff (siteRestrict ϱ) s x).mp hx |>.1)
    have hdiam := euclideanSetDiameter_subset_le
      (chargeSupport (chargeRestriction (siteRestrict ϱ) s)) s hchildsupp hsnonempty
      (by intro x hx; exact (mem_chargeSupport_restriction_iff
        (siteRestrict ϱ) s x).mp hx |>.1)
    calc
      chargeEuclideanDiameter (chargeRestriction (siteRestrict ϱ) s) =
          euclideanSetDiameter (chargeSupport (chargeRestriction (siteRestrict ϱ) s)) := rfl
      _ ≤ euclideanSetDiameter s := hdiam
      _ ≤ Real.sqrt 2 * (2 : ℝ) ^ j :=
        freeSquare_euclideanDiameter_le hsCover.2
  · by_contra hsingle
    have hkeep : totalCharge (siteRestrict ϱ) ≠ 0 ∧
        singletonBoundaryMargin j ≤ chargeBoundaryDistance (siteRestrict ϱ) := by
      by_contra hfail
      have hempty := pinnedPPrime_eq_empty_of_singleton_exception_fails
        (chargeCoverScale : ℝ) chargeCoverExponent j (siteRestrict ϱ)
        (boundaryEntropyMinimumCover (siteRestrict ϱ) j) hsingle hfail
      rw [hempty] at hsPrime
      exact Finset.notMem_empty _ hsPrime
    obtain ⟨u, hu⟩ := Finset.card_eq_one.mp hsingle
    have hsu : s = u := by simpa [hu] using hsCover.1
    have hparentSupport : chargeSupport (siteRestrict ϱ) ⊆ s := by
      intro x hx
      obtain ⟨t, ht, hxt⟩ := hC.1.2 x hx
      have htu : t = u := by simpa [hu] using ht
      simpa [hsu, htu] using hxt
    have hsame : chargeRestriction (siteRestrict ϱ) s = siteRestrict ϱ := by
      funext x
      by_cases hxs : x ∈ s
      · simp [chargeRestriction, hxs]
      · have hxzero : siteRestrict ϱ x = 0 := by
          by_contra hxne
          exact hxs (hparentSupport (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxne⟩))
        simp [chargeRestriction, hxs, hxzero]
    have hparentZero : totalCharge (siteRestrict ϱ) = 0 := by
      rw [← hsame]
      exact hneutral
    exact hkeep.1 hparentZero

/-- If a fine bad cluster meets a coarser bad cluster, it is contained in the coarser one. -/
theorem badSelectedCluster_overlap_nested (N : ℕ) (T : SelConfig L)
    (hT : IsCombTerminal N T) (ϱ : RotatorDualFace L → ℤ)
    (hϱ : ϱ ∈ T.F.image neutralizeAtWiredRoot)
    (j k : ℕ) (hjk : j ≤ k)
    (s t : Finset (Site L)) (hs : s ∈ badSelectedSquares ϱ j)
    (ht : t ∈ badSelectedSquares ϱ k)
    (hoverlap : (chargeSupport (chargeRestriction (siteRestrict ϱ) s) ∩
      chargeSupport (chargeRestriction (siteRestrict ϱ) t)).Nonempty) :
    chargeSupport (chargeRestriction (siteRestrict ϱ) s) ⊆
      chargeSupport (chargeRestriction (siteRestrict ϱ) t) := by
  classical
  let ρ := siteRestrict ϱ
  obtain ⟨ρ₀, hρ₀, hρeq⟩ := Finset.mem_image.mp hϱ
  have hρT : ρ ∈ T.F := by
    change siteRestrict ϱ ∈ T.F
    rw [← hρeq]
    simpa using hρ₀
  have hiso := hT.geometry.isolated ρ hρT
  let C := boundaryEntropyMinimumCover ρ k
  have hC : IsMinimumSquareCover .free L k ρ C :=
    boundaryEntropyMinimumCover_isMinimum ρ k
  have htSelected : t ∈ pinnedPPrime (chargeCoverScale : ℝ) chargeCoverExponent k ρ C := by
    simpa [C, selectedSquares] using (Finset.mem_filter.mp ht).1
  rcases badSelectedCluster_data ϱ k ht with
    ⟨hchildne, _hneutral, _hsub, _hcard, _hdiam, hCne⟩
  have htData := (mem_pinnedPPrime_of_cover_card_ne_one
    (chargeCoverScale : ℝ) chargeCoverExponent k ρ C hCne t).1 htSelected
  rcases htData with ⟨htC, hsep, _hboundary⟩
  obtain ⟨y, hy⟩ := hoverlap
  have hyS : y ∈ chargeSupport (chargeRestriction ρ s) :=
    (Finset.mem_inter.mp hy).1
  have hyT : y ∈ chargeSupport (chargeRestriction ρ t) :=
    (Finset.mem_inter.mp hy).2
  have hdiamS := (badSelectedCluster_data ϱ j hs).2.2.2.2.1
  have hsChildSub : chargeSupport (chargeRestriction ρ s) ⊆ chargeSupport ρ :=
    (badSelectedCluster_data ϱ j hs).2.2.1
  have htChildSub : chargeSupport (chargeRestriction ρ t) ⊆ chargeSupport ρ :=
    (badSelectedCluster_data ϱ k ht).2.2.1
  intro x hx
  by_contra hxT
  have hxρ : x ∈ chargeSupport ρ := hsChildSub hx
  have hxNotSquare : x ∉ t := by
    intro hxt
    exact hxT ((mem_chargeSupport_restriction_iff ρ t x).2 ⟨hxt, hxρ⟩)
  obtain ⟨u, hu, hxu⟩ := hC.1.2 x hxρ
  have hne : u ≠ t := by
    intro hut
    subst u
    exact hxNotSquare hxu
  have hySquare : y ∈ t :=
    (mem_chargeSupport_restriction_iff ρ t y).mp hyT |>.1
  have hyFine : y ∈ chargeSupport (chargeRestriction ρ s) := hyS
  have hsep' := hsep u hu hne
  have hscale : ((2 : ℝ) ^ k) ^ chargeCoverExponent =
      (2 : ℝ) ^ (chargeCoverExponent * (k : ℝ)) := by
    calc
      ((2 : ℝ) ^ k) ^ chargeCoverExponent =
          (2 : ℝ) ^ ((k : ℝ) * chargeCoverExponent) := by
            rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
      _ = (2 : ℝ) ^ (chargeCoverExponent * (k : ℝ)) :=
        congrArg (fun z : ℝ => (2 : ℝ) ^ z) (by ring)
  rw [← hscale] at hsep'
  have hset := SelectionG.setDist_le_siteDist hySquare hxu
  have hsite := SelectionG.siteDist_le_diam hyFine hx
  have hjkPow : (2 : ℝ) ^ j ≤ (2 : ℝ) ^ k :=
    pow_le_pow_right₀ (by norm_num) hjk
  have hbase : 1 ≤ (2 : ℝ) ^ k :=
    one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  have hpow : (2 : ℝ) ^ k ≤ ((2 : ℝ) ^ k) ^ chargeCoverExponent := by
    calc
      (2 : ℝ) ^ k = ((2 : ℝ) ^ k) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ ((2 : ℝ) ^ k) ^ chargeCoverExponent :=
        Real.rpow_le_rpow_of_exponent_le hbase (by norm_num [chargeCoverExponent])
  have hsqrt : Real.sqrt 2 < 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  have hradius : Real.sqrt 2 * (2 : ℝ) ^ j <
      2 * (chargeCoverScale : ℝ) * ((2 : ℝ) ^ k) ^ chargeCoverExponent := by
    calc
      Real.sqrt 2 * (2 : ℝ) ^ j ≤ Real.sqrt 2 * (2 : ℝ) ^ k :=
        mul_le_mul_of_nonneg_left hjkPow (Real.sqrt_nonneg _)
      _ < 2 * (2 : ℝ) ^ k := mul_lt_mul_of_pos_right hsqrt (by positivity)
      _ ≤ 2 * (chargeCoverScale : ℝ) * ((2 : ℝ) ^ k) ^ chargeCoverExponent := by
        have hM : (1 : ℝ) ≤ (chargeCoverScale : ℝ) := by
          norm_num [chargeCoverScale]
        calc
          2 * (2 : ℝ) ^ k ≤
              2 * (chargeCoverScale : ℝ) * (2 : ℝ) ^ k := by
            have hmul : (2 : ℝ) ^ k ≤
                (chargeCoverScale : ℝ) * (2 : ℝ) ^ k :=
              by
                simpa using mul_le_mul_of_nonneg_right hM
                  (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) k)
            nlinarith
          _ ≤ 2 * (chargeCoverScale : ℝ) * ((2 : ℝ) ^ k) ^ chargeCoverExponent :=
            mul_le_mul_of_nonneg_left hpow (by positivity)
  have hdiam' := hdiamS
  have hchain :
      2 * (chargeCoverScale : ℝ) * ((2 : ℝ) ^ k) ^ chargeCoverExponent ≤
        Real.sqrt 2 * (2 : ℝ) ^ j := by
    calc
      2 * (chargeCoverScale : ℝ) * ((2 : ℝ) ^ k) ^ chargeCoverExponent ≤
          euclideanSetDistance t u := hsep'
      _ ≤ euclideanSiteDistance y x := hset
      _ ≤ chargeEuclideanDiameter (chargeRestriction ρ s) := hsite
      _ ≤ Real.sqrt 2 * (2 : ℝ) ^ j := hdiam'
  exact (not_lt_of_ge hchain) hradius

/-- At a fixed scale, a bad selected cluster determines its selected square. -/
theorem badSelectedSquare_eq_of_same_cluster (ϱ : RotatorDualFace L → ℤ)
    (j : ℕ) {s t : Finset (Site L)} (hs : s ∈ badSelectedSquares ϱ j)
    (ht : t ∈ badSelectedSquares ϱ j)
    (heq : chargeSupport (chargeRestriction (siteRestrict ϱ) s) =
      chargeSupport (chargeRestriction (siteRestrict ϱ) t)) : s = t := by
  classical
  let ρ := siteRestrict ϱ
  have hsData := badSelectedCluster_data ϱ j hs
  have htData := badSelectedCluster_data ϱ j ht
  let C := boundaryEntropyMinimumCover ρ j
  have hC : IsMinimumSquareCover .free L j ρ C := boundaryEntropyMinimumCover_isMinimum ρ j
  have hsSelected : s ∈ pinnedPPrime (chargeCoverScale : ℝ) chargeCoverExponent j ρ C := by
    simpa [ρ, C, selectedSquares] using (Finset.mem_filter.mp hs).1
  have htSelected : t ∈ pinnedPPrime (chargeCoverScale : ℝ) chargeCoverExponent j ρ C := by
    simpa [ρ, C, selectedSquares] using (Finset.mem_filter.mp ht).1
  have hCne := hsData.2.2.2.2.2
  have hsSep := (mem_pinnedPPrime_of_cover_card_ne_one (chargeCoverScale : ℝ)
    chargeCoverExponent j ρ C hCne s).1 hsSelected |>.2.1
  have htC := (mem_pinnedPPrime_of_cover_card_ne_one (chargeCoverScale : ℝ)
    chargeCoverExponent j ρ C hCne t).1 htSelected |>.1
  by_contra hst
  obtain ⟨x, hx⟩ := chargeSupport_nonempty_of_ne_zero _ hsData.1
  have hxS : x ∈ s := (mem_chargeSupport_restriction_iff ρ s x).mp hx |>.1
  have hxTCluster : x ∈ chargeSupport (chargeRestriction ρ t) := by
    rw [← heq]
    exact hx
  have hxT : x ∈ t := (mem_chargeSupport_restriction_iff ρ t x).mp hxTCluster |>.1
  have hsep := hsSep t htC (Ne.symm hst)
  have hself : euclideanSiteDistance x x = 0 := by simp [euclideanSiteDistance]
  have hdist := (SelectionG.setDist_le_siteDist hxS hxT).trans_eq hself
  have hpos : 0 < 2 * (chargeCoverScale : ℝ) *
      (2 : ℝ) ^ (chargeCoverExponent * (j : ℝ)) := by
    have hM : 0 < (chargeCoverScale : ℝ) := by norm_num [chargeCoverScale]
    have hp : 0 < (2 : ℝ) ^ (chargeCoverExponent * (j : ℝ)) :=
      Real.rpow_pos_of_pos (by norm_num) _
    exact mul_pos (mul_pos (by norm_num) hM) hp
  linarith

/-- A neutral selected cluster cannot be the same at two different scales. -/
theorem badSelectedCluster_eq_forces_scale_eq (N : ℕ) (T : SelConfig L)
    (hT : IsCombTerminal N T) (ϱ : RotatorDualFace L → ℤ)
    (hϱ : ϱ ∈ T.F.image neutralizeAtWiredRoot)
    (j k : ℕ)
    (s t : Finset (Site L)) (hs : s ∈ badSelectedSquares ϱ j)
    (ht : t ∈ badSelectedSquares ϱ k)
    (heq : chargeSupport (chargeRestriction (siteRestrict ϱ) s) =
      chargeSupport (chargeRestriction (siteRestrict ϱ) t)) : j = k := by
  classical
  by_contra hjk
  rcases lt_or_gt_of_ne hjk with hjk | hjk
  · let ρ := siteRestrict ϱ
    obtain ⟨ρ₀, hρ₀, hρeq⟩ := Finset.mem_image.mp hϱ
    have hρT : ρ ∈ T.F := by
      change siteRestrict ϱ ∈ T.F
      rw [← hρeq]
      simpa using hρ₀
    have hiso : HasBoundaryIsolation (chargeCoverScale : ℝ) chargeCoverExponent T.F :=
      (hasBoundaryIsolation_iff).2 (fun q hq => hT.geometry.isolated q hq)
    let C := boundaryEntropyMinimumCover ρ k
    have hC : IsMinimumSquareCover .free L k ρ C := boundaryEntropyMinimumCover_isMinimum ρ k
    have htSelected : t ∈ pinnedPPrime (chargeCoverScale : ℝ) chargeCoverExponent k ρ C := by
      simpa [ρ, C, selectedSquares] using (Finset.mem_filter.mp ht).1
    have htData := badSelectedCluster_data ϱ k ht
    have hCne := htData.2.2.2.2.2
    have hdiamT : chargeEuclideanDiameter (chargeRestriction ρ t) ≤
        Real.sqrt 2 * (2 : ℝ) ^ j := by
      have hdiamS := (badSelectedCluster_data ϱ j hs).2.2.2.2.1
      unfold chargeEuclideanDiameter at hdiamS ⊢
      rw [heq] at hdiamS
      exact hdiamS
    have hsqrt : Real.sqrt 2 < 2 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    have hpow : (2 : ℝ) ^ j * 2 ≤ (2 : ℝ) ^ k := by
      calc
        (2 : ℝ) ^ j * 2 = (2 : ℝ) ^ (j + 1) := by rw [pow_succ]
        _ ≤ (2 : ℝ) ^ k := pow_le_pow_right₀ (by norm_num) (Nat.succ_le_of_lt hjk)
    have hdiamStrict : chargeEuclideanDiameter (chargeRestriction ρ t) < (2 : ℝ) ^ k := by
      calc
        chargeEuclideanDiameter (chargeRestriction ρ t) ≤ Real.sqrt 2 * (2 : ℝ) ^ j := hdiamT
        _ < 2 * (2 : ℝ) ^ j := mul_lt_mul_of_pos_right hsqrt (by positivity)
        _ ≤ (2 : ℝ) ^ k := by simpa [mul_comm] using hpow
    have hdiam : chargeEuclideanDiameter (chargeRestriction ρ t) ≤ (2 : ℝ) ^ k :=
      hdiamStrict.le
    have hcharged := selectedRestriction_charged_of_diameter_le_scale k ρ T.F hiso
      hρT C hC t htSelected hdiam
    exact hcharged htData.2.1
  · let ρ := siteRestrict ϱ
    obtain ⟨ρ₀, hρ₀, hρeq⟩ := Finset.mem_image.mp hϱ
    have hρT : ρ ∈ T.F := by
      change siteRestrict ϱ ∈ T.F
      rw [← hρeq]
      simpa using hρ₀
    have hiso : HasBoundaryIsolation (chargeCoverScale : ℝ) chargeCoverExponent T.F :=
      (hasBoundaryIsolation_iff).2 (fun q hq => hT.geometry.isolated q hq)
    let C := boundaryEntropyMinimumCover ρ j
    have hC : IsMinimumSquareCover .free L j ρ C := boundaryEntropyMinimumCover_isMinimum ρ j
    have hsSelected : s ∈ pinnedPPrime (chargeCoverScale : ℝ) chargeCoverExponent j ρ C := by
      simpa [ρ, C, selectedSquares] using (Finset.mem_filter.mp hs).1
    have hsData := badSelectedCluster_data ϱ j hs
    have hCne := hsData.2.2.2.2.2
    have hdiamS : chargeEuclideanDiameter (chargeRestriction ρ s) ≤
        Real.sqrt 2 * (2 : ℝ) ^ k := by
      have hdiamT := (badSelectedCluster_data ϱ k ht).2.2.2.2.1
      unfold chargeEuclideanDiameter at hdiamT ⊢
      rw [heq]
      exact hdiamT
    have hsqrt : Real.sqrt 2 < 2 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    have hpow : (2 : ℝ) ^ k * 2 ≤ (2 : ℝ) ^ j := by
      calc
        (2 : ℝ) ^ k * 2 = (2 : ℝ) ^ (k + 1) := by rw [pow_succ]
        _ ≤ (2 : ℝ) ^ j := pow_le_pow_right₀ (by norm_num) (Nat.succ_le_of_lt hjk)
    have hdiamStrict : chargeEuclideanDiameter (chargeRestriction ρ s) < (2 : ℝ) ^ j := by
      calc
        chargeEuclideanDiameter (chargeRestriction ρ s) ≤ Real.sqrt 2 * (2 : ℝ) ^ k := hdiamS
        _ < 2 * (2 : ℝ) ^ k := mul_lt_mul_of_pos_right hsqrt (by positivity)
        _ ≤ (2 : ℝ) ^ j := by simpa [mul_comm] using hpow
    have hdiam : chargeEuclideanDiameter (chargeRestriction ρ s) ≤ (2 : ℝ) ^ j :=
      hdiamStrict.le
    have hcharged := selectedRestriction_charged_of_diameter_le_scale j ρ T.F hiso
      hρT C hC s hsSelected hdiam
    exact hcharged hsData.2.1

/-- Two bad occurrences with the same cluster have the same scale and square. -/
theorem badSelectedCluster_injective_on_univ (N : ℕ) (T : SelConfig L)
    (hT : IsCombTerminal N T) (ϱ : RotatorDualFace L → ℤ)
    (hϱ : ϱ ∈ T.F.image neutralizeAtWiredRoot) :
    Set.InjOn (badSelectedCluster ϱ) Set.univ := by
  classical
  intro i _ i' _ heq
  rcases i with ⟨⟨j, hj⟩, ⟨s, hs⟩⟩
  rcases i' with ⟨⟨k, hk⟩, ⟨t, ht⟩⟩
  change chargeSupport (chargeRestriction (siteRestrict ϱ) s) =
    chargeSupport (chargeRestriction (siteRestrict ϱ) t) at heq
  have hscale := badSelectedCluster_eq_forces_scale_eq N T hT ϱ hϱ j k s t hs ht heq
  subst k
  have hsquare := badSelectedSquare_eq_of_same_cluster ϱ j hs ht heq
  subst t
  rfl

/-- Neutral selected clusters form a laminar family. -/
theorem badSelectedClusterFamily_laminar (N : ℕ) (T : SelConfig L)
    (hT : IsCombTerminal N T) (ϱ : RotatorDualFace L → ℤ)
    (hϱ : ϱ ∈ T.F.image neutralizeAtWiredRoot) :
    IsLaminarFamily (badSelectedClusterFamily ϱ) := by
  classical
  intro A hA B hB hAB
  obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hA
  obtain ⟨i', _hi', rfl⟩ := Finset.mem_image.mp hB
  by_cases hdisj : Disjoint (badSelectedCluster ϱ i) (badSelectedCluster ϱ i')
  · exact Or.inl hdisj
  · have hoverlap : (badSelectedCluster ϱ i ∩ badSelectedCluster ϱ i').Nonempty := by
      rw [Finset.not_disjoint_iff] at hdisj
      rcases hdisj with ⟨x, hx, hx'⟩
      exact ⟨x, Finset.mem_inter.mpr ⟨hx, hx'⟩⟩
    obtain ⟨x, hx⟩ := hoverlap
    have hs : i.2.1 ∈ badSelectedSquares ϱ i.1.1 := i.2.2
    have ht : i'.2.1 ∈ badSelectedSquares ϱ i'.1.1 := i'.2.2
    rcases le_total i.1.1 i'.1.1 with hik | hki
    · apply Or.inr (Or.inl ?_)
      exact badSelectedCluster_overlap_nested N T hT ϱ hϱ i.1.1 i'.1.1 hik
        i.2.1 i'.2.1 hs ht ⟨x, hx⟩
    · apply Or.inr (Or.inr ?_)
      exact badSelectedCluster_overlap_nested N T hT ϱ hϱ i'.1.1 i.1.1 hki
        i'.2.1 i.2.1 ht hs ⟨x, Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hx).2,
          (Finset.mem_inter.mp hx).1⟩⟩

/-- The bad clusters sit in the parent support and each contains at least two sites. -/
theorem badSelectedClusterFamily_data (ϱ : RotatorDualFace L → ℤ) :
    (∀ A ∈ badSelectedClusterFamily ϱ, A ⊆ chargeSupport (siteRestrict ϱ)) ∧
    (∀ A ∈ badSelectedClusterFamily ϱ, 2 ≤ A.card) := by
  classical
  constructor
  · intro A hA
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hA
    rcases i with ⟨⟨j, _hj⟩, ⟨s, hs⟩⟩
    exact (badSelectedCluster_data ϱ j hs).2.2.1
  · intro A hA
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hA
    rcases i with ⟨⟨j, _hj⟩, ⟨s, hs⟩⟩
    exact (badSelectedCluster_data ϱ j hs).2.2.2.1

/-- The number of bad selected squares is bounded by the `ℓ¹` charge norm.

The count is the size of the occurrence index.  Injectivity identifies occurrences with their
clusters; the clusters are a laminar family of at-least-two-point subsets of the support.  Its
cardinality is therefore at most the support size, which is bounded by the integer `ℓ¹` norm. -/
theorem badSelectedBound_proof : BadSelectedBound := by
  classical
  intro L N T hT ϱ hϱ
  let ρ := siteRestrict ϱ
  let F := badSelectedClusterFamily ϱ
  have hInject := badSelectedCluster_injective_on_univ N T hT ϱ hϱ
  have hCard : F.card = Fintype.card (BadSelectedIndex ϱ) := by
    dsimp [F, badSelectedClusterFamily]
    rw [Finset.card_image_iff.mpr (by simpa using hInject)]
    simp
  have hData := badSelectedClusterFamily_data ϱ
  have hLaminar := badSelectedClusterFamily_laminar N T hT ϱ hϱ
  have hFamilyCard : F.card ≤ (chargeSupport ρ).card :=
    laminarFamily_card_le_universe (chargeSupport ρ) F
      (by simpa [ρ] using hData.1) (by simpa [ρ] using hData.2) hLaminar
  obtain ⟨ρ₀, hρ₀, hρeq⟩ := Finset.mem_image.mp hϱ
  have hNorm : ∑ x, |(ρ x : ℝ)| ≤ ∑ j, |(ϱ j : ℝ)| := by
    dsimp [ρ]
    rw [← hρeq]
    simp [siteRestrict_neutralize]
  have hIndexCount := badSelectedSum_eq_index_card ϱ
  rw [hIndexCount]
  calc
    (Fintype.card (BadSelectedIndex ϱ) : ℝ) = (F.card : ℝ) := by
      exact_mod_cast hCard.symm
    _ ≤ ((chargeSupport ρ).card : ℝ) := by exact_mod_cast hFamilyCard
    _ ≤ ∑ x, |(ρ x : ℝ)| := card_support_le_norm ρ
    _ ≤ ∑ j, |(ϱ j : ℝ)| := hNorm


end FroehlichSpencer.BKT.Generic.PinnedCharges.Layer
