/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Wilson.AreaLawCancellationSplit
public import FroehlichSpencer.FS82.Wilson.AreaLawClusterBound
public import FroehlichSpencer.FS82.Wilson.AreaLawWeight
public import FroehlichSpencer.FS82.Wilson.AreaLawTail
public import FroehlichSpencer.FS82.Wilson.DualityFinite

/-!
# Finite-volume small-β Wilson area law

The source-component cancellation is an inequality: after selecting the
component carrying the loop boundary, the remaining divergence-free field
contributes at most the unrestricted vacuum partition sum. The selected
component is then bounded by its area-extracted Gaussian weight and by the
degree-20 connected-animal tail.
-/

public section

namespace FroehlichSpencer.FS82.Wilson

open FroehlichSpencer.FS82.Cubical

private theorem rectangleSourceCluster_residual_le_tail {B : Box 4}
    {L T : ℕ} (hL : L ≤ B 0) (hT : T ≤ B 1)
    (hLpos : 0 < L) (hTpos : 0 < T)
    (β : ℝ) (hβ : 0 < β) (hsmall : β ≤ 1 / 80) :
    (∑' c : {m : PrimalPlaquettes B → ℤ //
      plaquetteModeDivergence m =
        primalSheetLoopFrequency (wilsonRectangleSheet L T hL hT) ∧
      ∃ p ∈ rectangleSourceRootPlaquettes L T hL hT,
        plaquetteFieldSupport m ∈
          FroehlichSpencer.Infra.animals (plaquetteLinkGraph (B := B)) p
            (plaquetteFieldSupport m).card},
      dualGaussianProduct β c.1) ≤
      Real.exp (-10 * (L * T : ℝ)) *
        (24 * ((L * T : ℕ) : ℝ) *
          areaActivityTail (400 * nonzeroGaussianActivity (4 * β / 3)) (L * T)) := by
  classical
  let Source : Type := {m : PrimalPlaquettes B → ℤ //
    plaquetteModeDivergence m =
      primalSheetLoopFrequency (wilsonRectangleSheet L T hL hT) ∧
    ∃ p ∈ rectangleSourceRootPlaquettes L T hL hT,
      plaquetteFieldSupport m ∈
        FroehlichSpencer.Infra.animals (plaquetteLinkGraph (B := B)) p
          (plaquetteFieldSupport m).card}
  let Allowed : Type := {m : PrimalPlaquettes B → ℤ //
    (∃ p ∈ rectangleSourceRootPlaquettes L T hL hT,
      plaquetteFieldSupport m ∈
        FroehlichSpencer.Infra.animals (plaquetteLinkGraph (B := B)) p
          (plaquetteFieldSupport m).card) ∧
    L * T ≤ (plaquetteFieldSupport m).card}
  let residualβ : ℝ := 4 * β / 3
  let r : ℝ := 400 * nonzeroGaussianActivity residualβ
  let extract : ℝ := Real.exp (-10 * (L * T : ℝ))
  have hβr : 0 < residualβ := by dsimp [residualβ]; positivity
  have hr0 : 0 ≤ r := by
    dsimp [r]
    unfold nonzeroGaussianActivity
    apply mul_nonneg (by norm_num)
    exact tsum_nonneg fun z => by split_ifs <;> positivity
  have hrsmall : r ≤ Real.exp (-7) := by
    dsimp [r, residualβ]
    exact smallBeta_residualActivity_bound β hβ hsmall
  have hfull := dualGaussianProduct_summable (B := B) residualβ hβr
  let forgetSource : Source → (PrimalPlaquettes B → ℤ) := fun m => m.1
  have hforgetSource : Function.Injective forgetSource := by
    intro m n h
    exact Subtype.ext h
  have hsourceResidualSummable : Summable (fun m : Source =>
      dualGaussianProduct residualβ m.1) := by
    change Summable (dualGaussianProduct residualβ ∘ forgetSource)
    exact hfull.comp_injective hforgetSource
  have hsourceOriginalSummable : Summable (fun m : Source =>
      dualGaussianProduct β m.1) := by
    have h := dualGaussianProduct_summable (B := B) β hβ
    change Summable (dualGaussianProduct β ∘ forgetSource)
    exact h.comp_injective hforgetSource
  have hsourcePoint (m : Source) :
      dualGaussianProduct β m.1 ≤ extract * dualGaussianProduct residualβ m.1 := by
    dsimp [extract, residualβ]
    exact dualGaussianProduct_source_small_beta_bound hL hT β hβ hsmall
      m.1 m.2.1
  have hsourceSum :
      (∑' m : Source, dualGaussianProduct β m.1) ≤
        extract * (∑' m : Source, dualGaussianProduct residualβ m.1) := by
    calc
      _ ≤ ∑' m : Source, extract * dualGaussianProduct residualβ m.1 :=
        hsourceOriginalSummable.tsum_le_tsum hsourcePoint
          (hsourceResidualSummable.mul_left extract)
      _ = extract * (∑' m : Source, dualGaussianProduct residualβ m.1) :=
        tsum_mul_left
  have harea (m : Source) : L * T ≤ (plaquetteFieldSupport m.1).card :=
    plaquetteFieldSupport_card_lower_bound hL hT m.1 m.2.1
  let incl : Source → Allowed := fun m =>
    ⟨m.1, ⟨m.2.2, harea m⟩⟩
  have hinj : Function.Injective incl := by
    intro m n h
    apply Subtype.ext
    exact congrArg (fun x : Allowed => x.1) h
  have hfullAllowed : Summable (fun m : Allowed =>
      dualGaussianProduct residualβ m.1) := by
    let forgetAllowed : Allowed → (PrimalPlaquettes B → ℤ) := fun m => m.1
    have hforgetAllowed : Function.Injective forgetAllowed := by
      intro m n h
      exact Subtype.ext h
    change Summable (dualGaussianProduct residualβ ∘ forgetAllowed)
    exact hfull.comp_injective hforgetAllowed
  have hsourceResidualLeAllowed :
    (∑' m : Source, dualGaussianProduct residualβ m.1) ≤
        ∑' m : Allowed, dualGaussianProduct residualβ m.1 := by
    have hfun : (fun m : Source => dualGaussianProduct residualβ m.1) =
        (fun m : Allowed => dualGaussianProduct residualβ m.1) ∘ incl := by
      funext m
      rfl
    rw [hfun]
    exact tsum_comp_le_tsum_of_inj hfullAllowed
      (fun m : Allowed => dualGaussianProduct_nonneg residualβ m.1) hinj
  have hA : 1 ≤ L * T := by
    have hpos : 0 < L * T := Nat.mul_pos hLpos hTpos
    omega
  have hrEq : r = 400 * nonzeroGaussianActivity residualβ := by rfl
  have hcluster := rectangleConnectedSourceActivity_le_tail
    hL hT hA residualβ hβr r hr0 hrsmall hrEq
  have hAcast : ((L * T : ℕ) : ℝ) = (L : ℝ) * (T : ℝ) := by norm_cast
  calc
    (∑' m : Source, dualGaussianProduct β m.1) ≤
        extract * (∑' m : Source, dualGaussianProduct residualβ m.1) :=
          hsourceSum
    _ ≤ extract * (∑' m : Allowed, dualGaussianProduct residualβ m.1) :=
          mul_le_mul_of_nonneg_left hsourceResidualLeAllowed (Real.exp_pos _).le
    _ ≤ extract *
          (24 * ((L * T : ℕ) : ℝ) * areaActivityTail r (L * T)) := by
            apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
            exact hcluster
    _ = extract *
          (24 * (L * T : ℝ) * areaActivityTail r (L * T)) := by rw [hAcast]
    _ ≤ Real.exp (-10 * (L * T : ℝ)) *
          (24 * ((L * T : ℕ) : ℝ) *
            areaActivityTail (400 * nonzeroGaussianActivity (4 * β / 3)) (L * T)) := by
          simp [extract, r, residualβ, hAcast]

/-- Uniform finite-volume area decay for the fundamental Villain Wilson loop.
The constants are explicit: `β₀ = 1/80` and `c = 1/2`. -/
theorem primalWilsonExpectation_rectangle_smallBeta_areaLaw
    {B : Box 4} {L T : ℕ}
    (hL : L ≤ B 0) (hT : T ≤ B 1) (hLpos : 0 < L) (hTpos : 0 < T)
    (β : ℝ) (hβ : 0 < β) (hsmall : β ≤ 1 / 80) :
    0 ≤ (primalWilsonExpectation β (wilsonRectangleSheet L T hL hT)).re ∧
      (primalWilsonExpectation β (wilsonRectangleSheet L T hL hT)).re ≤
        Real.exp (-(L * T : ℝ) / 2) := by
  classical
  let A : ℕ := L * T
  let residualβ : ℝ := 4 * β / 3
  let r : ℝ := 400 * nonzeroGaussianActivity residualβ
  let extract : ℝ := Real.exp (-10 * (A : ℝ))
  have hA : 1 ≤ A := by
    dsimp [A]
    have hpos : 0 < L * T := Nat.mul_pos hLpos hTpos
    omega
  have hβr : 0 < residualβ := by dsimp [residualβ]; positivity
  have hr0 : 0 ≤ r := by
    dsimp [r]
    unfold nonzeroGaussianActivity
    apply mul_nonneg (by norm_num)
    exact tsum_nonneg fun z => by split_ifs <;> positivity
  have hrsmall : r ≤ Real.exp (-7) := by
    dsimp [r, residualβ]
    exact smallBeta_residualActivity_bound β hβ hsmall
  have hpartition := dualWilsonPartition_le_rectangleSourceClusters_mul_vacuum
    hL hT hLpos hTpos β hβ
  have hvac : 0 < dualWilsonPartition (B := B) β (0 : Chain 4 B) :=
    dualWilsonPartition_zero_pos β hβ
  have hratio :
      dualWilsonPartition (B := B) β (wilsonRectangleSheet L T hL hT) /
          dualWilsonPartition (B := B) β (0 : Chain 4 B) ≤
        ∑' c : {m : PrimalPlaquettes B → ℤ //
          plaquetteModeDivergence m =
            primalSheetLoopFrequency (wilsonRectangleSheet L T hL hT) ∧
          ∃ p ∈ rectangleSourceRootPlaquettes L T hL hT,
            plaquetteFieldSupport m ∈
              FroehlichSpencer.Infra.animals (plaquetteLinkGraph (B := B)) p
                (plaquetteFieldSupport m).card},
          dualGaussianProduct β c.1 := by
    apply (div_le_iff₀ hvac).2
    exact hpartition
  have hclusterTail := rectangleSourceCluster_residual_le_tail
    hL hT hLpos hTpos β hβ hsmall
  have hactivityTail := areaActivityTail_bound A hA r hr0 hrsmall
  have hclusterBound :
      (∑' c : {m : PrimalPlaquettes B → ℤ //
        plaquetteModeDivergence m =
          primalSheetLoopFrequency (wilsonRectangleSheet L T hL hT) ∧
        ∃ p ∈ rectangleSourceRootPlaquettes L T hL hT,
          plaquetteFieldSupport m ∈
            FroehlichSpencer.Infra.animals (plaquetteLinkGraph (B := B)) p
              (plaquetteFieldSupport m).card},
        dualGaussianProduct β c.1) ≤ Real.exp (-(A : ℝ) / 2) := by
    have htailCast : areaActivityTail r (L * T) = areaActivityTail r A := by
      rfl
    have hcoefCast : ((L * T : ℕ) : ℝ) = (A : ℝ) := by rfl
    have hcluster := hclusterTail
    rw [htailCast, hcoefCast] at hcluster
    have hextract : Real.exp (-10 * (L * T : ℝ)) = extract := by
      dsimp [extract, A]
      congr 1
      push_cast
      ring
    have hExtractLe : extract ≤ 1 := by
      dsimp [extract]
      rw [← Real.exp_zero]
      apply Real.exp_le_exp.mpr
      have hApos : 0 ≤ (A : ℝ) := by positivity
      linarith
    calc
      _ ≤ extract * (24 * (A : ℝ) * areaActivityTail r A) := by
        calc
          _ ≤ Real.exp (-10 * (L * T : ℝ)) *
                (24 * (A : ℝ) * areaActivityTail r A) := by
                  simpa [htailCast, hcoefCast] using hcluster
          _ = extract * (24 * (A : ℝ) * areaActivityTail r A) := by rw [hextract]
      _ ≤ extract * Real.exp (-(A : ℝ) / 2) :=
        mul_le_mul_of_nonneg_left hactivityTail (Real.exp_pos _).le
      _ ≤ Real.exp (-(A : ℝ) / 2) := by
        calc
          extract * Real.exp (-(A : ℝ) / 2) ≤
              1 * Real.exp (-(A : ℝ) / 2) :=
            mul_le_mul_of_nonneg_right hExtractLe (Real.exp_pos _).le
          _ = Real.exp (-(A : ℝ) / 2) := by ring
  have hreal :
      (primalWilsonExpectation β (wilsonRectangleSheet L T hL hT)).re =
        dualWilsonPartition (B := B) β (wilsonRectangleSheet L T hL hT) /
          dualWilsonPartition (B := B) β (0 : Chain 4 B) := by
    rw [primalWilsonExpectation_eq_dualPartition_ratio β hβ]
    rw [← Complex.ofReal_div]
    simp only [Complex.ofReal_re]
  refine ⟨primalWilsonExpectation_re_nonneg β hβ _, ?_⟩
  rw [hreal]
  have hratioBound := hratio.trans hclusterBound
  simpa [A] using hratioBound

/-- An existential small-coupling formulation of the finite-volume area law. -/
theorem exists_smallBeta_primalWilsonExpectation_rectangle_areaLaw :
    ∃ β₀ c : ℝ, 0 < β₀ ∧ 0 < c ∧
      ∀ {B : Box 4} {L T : ℕ} (hL : L ≤ B 0) (hT : T ≤ B 1),
        0 < L → 0 < T →
        ∀ β : ℝ, 0 < β → β ≤ β₀ →
          0 ≤ (primalWilsonExpectation β (wilsonRectangleSheet L T hL hT)).re ∧
          (primalWilsonExpectation β (wilsonRectangleSheet L T hL hT)).re ≤
            Real.exp (-c * (L * T : ℝ)) := by
  refine ⟨1 / 80, 1 / 2, by norm_num, by norm_num, ?_⟩
  intro B L T hL hT hLpos hTpos β hβ hsmall
  have hmain := primalWilsonExpectation_rectangle_smallBeta_areaLaw
    hL hT hLpos hTpos β hβ hsmall
  refine ⟨hmain.1, ?_⟩
  have hexp : -(1 / 2 : ℝ) * (L * T : ℝ) = -(L * T : ℝ) / 2 := by ring
  rw [hexp]
  exact hmain.2

end FroehlichSpencer.FS82.Wilson

end
