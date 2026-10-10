/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Root.NormalizedActivity
public import FroehlichSpencer.FS82.Root.FamilyJensen
public import FroehlichSpencer.FS82.Root.BranchPositiveType
public import FroehlichSpencer.FS82.Currents.PlaquetteDistance
public import FroehlichSpencer.FS82.Root.SourcePackingEstimate

/-!
# the lineages of a terminal state as a separated family

For a separated, valid terminal state of the fixed-frequency expansion, the physical currents of
its lineages have pairwise disjoint, plaquette-separated and vertex-separated supports.

With the
root activity `z(n) = 2^(n+1)` every lineage coefficient is at most `exp(β₁ ‖ϱ‖²)` with the
explicit box-independent `β₁ = 2 log 2 + 4·7⁴ log 3`, and the one-link attenuation on the
selected colour class gives the renormalized envelope `exp(−a(β)(‖ϱ‖² + |supp ϱ|))`,
`a(β) = (β/216 − β₁)/2`.
-/

open MeasureTheory
open scoped BigOperators InnerProductSpace
open FroehlichSpencer.FS82.Gaussian
open FroehlichSpencer.FS82.Gaussian.GaugeAveraged
open FroehlichSpencer.FS82.Currents
open FroehlichSpencer.FS82.Currents.SelectedLinkSelection
open FroehlichSpencer.FS82.Currents.SelectedCurrentLinks
open FroehlichSpencer.FS82.Currents.SourceLinkColoring
open FroehlichSpencer.FS82.Currents.PlaquetteDistance
open FroehlichSpencer.FS82.Currents.PackingFamily
open FroehlichSpencer.FS82.Moment
open FroehlichSpencer.FS82.Moment.ExpansionIntegral
open FroehlichSpencer.FS82.Moment.PhysicalGaugeCurrent
open FroehlichSpencer.FS82.Moment.SourceConstructor
open FroehlichSpencer.FS82.Poisson

@[expose] public section

namespace FroehlichSpencer.FS82.Root.MomentComparisonAssembly

variable {B : Cubical.Box 4}

/-! ## The activity envelope for the root activity -/

/-- The box-independent rate of the lineage activity envelope for the root activity. -/
noncomputable def rootRate : ℝ := 2 * Real.log 2 + (4 * 7 ^ 4 : ℕ) * Real.log 3

theorem rootRate_nonneg : 0 ≤ rootRate := by
  unfold rootRate
  have h2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have h3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  positivity

theorem natPow_eq_exp_log (a : ℝ) (ha : 0 < a) (n : ℕ) :
    a ^ n = Real.exp (Real.log a * (n : ℝ)) := by
  rw [mul_comm, Real.exp_nat_mul, Real.exp_log ha]

theorem rootIntegerActivity_nonneg (n : ℤ) :
    0 ≤ sourceAssignmentIntegerActivity rootActivity n :=
  (rootActivity_pos _).le

/-- On nonzero integer frequencies the root activity is at most `exp(2 log 2 · n²)`. -/
theorem rootIntegerActivity_le (n : ℤ) (hn : n ≠ 0) :
    sourceAssignmentIntegerActivity rootActivity |n| ≤
      Real.exp (2 * Real.log 2 * (n : ℝ) ^ 2) := by
  have hk : 1 ≤ n.natAbs := Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hn)
  have hsq : (n : ℝ) ^ 2 = ((n.natAbs : ℕ) : ℝ) ^ 2 := by
    have h : ((n.natAbs : ℤ) : ℝ) ^ 2 = (n : ℝ) ^ 2 := by
      rw [Int.natCast_natAbs, Int.cast_abs, sq_abs]
    rw [← h]
    norm_cast
  unfold sourceAssignmentIntegerActivity rootActivity
  rw [Int.natAbs_abs, natPow_eq_exp_log 2 (by norm_num), hsq]
  apply Real.exp_le_exp.mpr
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hkR : (1 : ℝ) ≤ (n.natAbs : ℝ) := by exact_mod_cast hk
  push_cast
  nlinarith [mul_nonneg hlog (sub_nonneg.mpr hkR)]

/-- **Lineage activity envelope for the root activity.** -/
theorem lineageCoefficient_rootActivity_le (q : Link B → ℤ) (h : ExpansionLineage B)
    (hg : ActivityLineage.Good currentNear h) (hq : ∀ e ∈ h.all, q e ≠ 0) :
    lineageCoefficient q (sourceAssignmentIntegerActivity rootActivity) h ≤
      Real.exp (rootRate * integerCurrentNormSq (lineageCurrent q h)) := by
  let j := ActivityLineage.value q h
  let S := currentSupport j
  have hactivity := cubical_currentActivity_bound hg q hq
    (sourceAssignmentIntegerActivity rootActivity) rootIntegerActivity_nonneg
  have hcard := oneNeighborSet_card_le_localConstant S
  have hsupport : (S.card : ℝ) ≤ integerCurrentNormSq j :=
    currentSupport_card_le_integerCurrentNormSq j
  have hneighborR : ((oneNeighborSet S).card : ℝ) ≤
      ((4 * 7 ^ 4 : ℕ) : ℝ) * integerCurrentNormSq j := by
    have hcardR' : ((oneNeighborSet S).card : ℝ) ≤
        ((4 * 7 ^ 4 : ℕ) : ℝ) * (S.card : ℝ) := by exact_mod_cast hcard
    exact le_trans hcardR' (mul_le_mul_of_nonneg_left hsupport (by positivity))
  have hsumSupport : (∑ e ∈ S, (j e : ℝ) ^ 2) = integerCurrentNormSq j := by
    unfold integerCurrentNormSq
    apply Finset.sum_subset (Finset.subset_univ S)
    intro e _ hnot
    have hzero : j e = 0 := by
      by_contra hne
      exact hnot (by simp [S, currentSupport, hne])
    simp [hzero]
  have hprod : (∏ e ∈ S, sourceAssignmentIntegerActivity rootActivity (abs (j e))) ≤
      Real.exp (2 * Real.log 2 * integerCurrentNormSq j) := by
    calc
      _ ≤ ∏ e ∈ S, Real.exp (2 * Real.log 2 * (j e : ℝ) ^ 2) := by
        apply Finset.prod_le_prod₀
        · intro e _
          exact rootIntegerActivity_nonneg _
        · intro e he
          have hne : j e ≠ 0 := by simpa [S, currentSupport] using he
          exact rootIntegerActivity_le (j e) hne
      _ = Real.exp (2 * Real.log 2 * (∑ e ∈ S, (j e : ℝ) ^ 2)) := by
        rw [← Real.exp_sum, Finset.mul_sum]
      _ = _ := by rw [hsumSupport]
  have hpow : (3 : ℝ) ^ (oneNeighborSet S).card =
      Real.exp (Real.log 3 * ((oneNeighborSet S).card : ℝ)) :=
    natPow_eq_exp_log 3 (by norm_num) _
  change ActivityLineage.coefficient
      (fun e => sourceAssignmentIntegerActivity rootActivity (abs (q e))) h ≤
    Real.exp (rootRate * integerCurrentNormSq j)
  calc
    _ ≤ (3 : ℝ) ^ (oneNeighborSet S).card *
        ∏ e ∈ S, sourceAssignmentIntegerActivity rootActivity (abs (j e)) := hactivity
    _ ≤ Real.exp (Real.log 3 * ((oneNeighborSet S).card : ℝ)) *
        Real.exp (2 * Real.log 2 * integerCurrentNormSq j) := by
      rw [hpow]
      exact mul_le_mul_of_nonneg_left hprod (Real.exp_pos _).le
    _ = Real.exp (Real.log 3 * ((oneNeighborSet S).card : ℝ) +
        2 * Real.log 2 * integerCurrentNormSq j) := by rw [← Real.exp_add]
    _ ≤ Real.exp (rootRate * integerCurrentNormSq j) := by
      apply Real.exp_le_exp.mpr
      unfold rootRate
      have hlog : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
      have hlogBound := mul_le_mul_of_nonneg_left hneighborR hlog
      nlinarith [hlogBound]

/-! ## The physical current of a lineage -/

theorem sourceBranchModeCurrent_apply (k : Link B → ℤ) (e : Link B) :
    sourceBranchModeCurrent k e = sourceDualT e * k e := by
  simp [sourceBranchModeCurrent, physicalGaugeCurrent]

theorem sourceBranchModeCurrent_support (k : Link B → ℤ) :
    (sourceBranchModeCurrent k).support = currentSupport k := by
  ext e
  rw [Finsupp.mem_support_iff, sourceBranchModeCurrent_apply]
  simp only [currentSupport, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases sourceDualT_is_pm_one e with he | he <;> simp [he]


theorem sourceBranchModeCurrent_normSq (k : Link B → ℤ) :
    integerCurrentNormSq (fun e : Link B => sourceBranchModeCurrent k e) =
      integerCurrentNormSq k := by
  unfold integerCurrentNormSq
  refine Finset.sum_congr rfl fun e _ => ?_
  simp only [sourceBranchModeCurrent_apply]
  rcases sourceDualT_is_pm_one e with he | he <;> simp [he]

/-- The lattice phase of the physical current is the integer-frequency phase. -/
theorem sourceBranchModeCurrent_inner (k : Link B → ℤ)
    (α : EuclideanSpace ℝ (SourceDualOneCells B)) :
    inner ℝ ((2 * Real.pi) • latticeIntegerModeVector (B := B) (sourceBranchModeCurrent k)) α =
      Currents.currentPhase (fun e => 2 * Real.pi * α e) k := by
  have hmode : ∀ e : SourceDualOneCells B,
      latticePhysicalMode (B := B) (sourceBranchModeCurrent k) e = k e := by
    intro e
    rw [latticePhysicalMode, sourceBranchModeCurrent_apply]
    rcases sourceDualT_is_pm_one e with he | he <;> rw [he] <;> ring
  rw [PiLp.inner_apply]
  simp only [Real.inner_apply, PiLp.smul_apply, smul_eq_mul, latticeIntegerModeVector_apply,
    hmode]
  unfold Currents.currentPhase
  refine Finset.sum_congr rfl fun e _ => ?_
  ring

/-! ## The lineages of a state as a family -/

section State

variable (q : Link B → ℤ) (z : ℤ → ℝ) (s : CurrentState B)

/-- The activity of a lineage of the state. -/
noncomputable def stateActivity (i : {h : ExpansionLineage B // h ∈ s}) : ℝ :=
  lineageCoefficient q z i.1

/-- The physical integer current of a lineage of the state. -/
noncomputable def stateCurrent (i : {h : ExpansionLineage B // h ∈ s}) : IntegerCurrent B :=
  sourceBranchModeCurrent (lineageCurrent q i.1)

theorem stateCurrent_support (i : {h : ExpansionLineage B // h ∈ s}) :
    (stateCurrent q s i).support = currentSupport (lineageCurrent q i.1) :=
  sourceBranchModeCurrent_support _

variable {q s}

theorem state_linkDistance (hs : IsSeparatedCurrentState q s)
    (i j : {h : ExpansionLineage B // h ∈ s}) (hij : i ≠ j) :
    ∀ e ∈ (stateCurrent q s i).support, ∀ f ∈ (stateCurrent q s j).support,
      Real.sqrt 2 ≤ linkDistance e f := by
  intro e he f hf
  rw [stateCurrent_support] at he hf
  exact hs i.1 i.2 j.1 j.2 (fun h => hij (Subtype.ext h)) e he f hf

theorem state_hdisjoint (hs : IsSeparatedCurrentState q s) :
    ∀ i j : {h : ExpansionLineage B // h ∈ s}, i ≠ j →
      Disjoint (stateCurrent q s i).support (stateCurrent q s j).support := by
  intro i j hij
  refine Finset.disjoint_left.mpr fun e he hf => ?_
  have hsep := state_linkDistance hs i j hij e he e hf
  rw [linkDistance_self] at hsep
  exact (not_le_of_gt (Real.sqrt_pos.2 (by norm_num))) hsep

theorem state_hplaq (hs : IsSeparatedCurrentState q s) :
    ∀ i j : {h : ExpansionLineage B // h ∈ s}, i ≠ j →
      ∀ e ∈ (stateCurrent q s i).support, ∀ f ∈ (stateCurrent q s j).support,
        ¬ ∃ p : SourceDualTwoCells B,
          linkIncidentPlaquette e p ∧ linkIncidentPlaquette f p := by
  intro i j hij e he f hf hshare
  have hsep := state_linkDistance hs i j hij e he f hf
  have hef : e ≠ f := by
    rintro rfl
    exact Finset.disjoint_left.mp (state_hdisjoint hs i j hij) he hf
  exact (not_le_of_gt (linkDistance_lt_sqrt_two_of_sharedPlaquette hef hshare)) hsep

theorem state_hvert (hs : IsSeparatedCurrentState q s) :
    ∀ i j : {h : ExpansionLineage B // h ∈ s}, i ≠ j →
      ∀ e ∈ (stateCurrent q s i).support, ∀ f ∈ (stateCurrent q s j).support,
        ¬ linksShareFiniteVertex e f := by
  intro i j hij e he f hf hshare
  have hsep := state_linkDistance hs i j hij e he f hf
  obtain ⟨v, hve, hvf⟩ := linksShareFiniteVertex_sourceEndpoint hshare
  have hzero : linkDistance e f = 0 := linkDistance_zero_of_shared_vertex e f v hve hvf
  rw [hzero] at hsep
  exact (not_le_of_gt (Real.sqrt_pos.2 (by norm_num))) hsep

theorem stateCurrent_support_nonempty (hv : IsValidCurrentState q s)
    (i : {h : ExpansionLineage B // h ∈ s}) : (stateCurrent q s i).support.Nonempty := by
  obtain ⟨hg, hq⟩ := hv.1 i.1 i.2
  rw [stateCurrent_support]
  change (currentSupport (ActivityLineage.value q i.1)).Nonempty
  rw [ActivityLineage.currentSupport_value_eq_active hg q hq]
  apply Finset.card_pos.mp
  rw [hg.active_card_eq_mergeCount_add_one]
  omega

theorem stateCurrent_ne_zero (hv : IsValidCurrentState q s)
    (i : {h : ExpansionLineage B // h ∈ s}) : stateCurrent q s i ≠ 0 := by
  intro h
  have hne := stateCurrent_support_nonempty hv i
  rw [h] at hne
  simp at hne

theorem stateCurrent_injective (hs : IsSeparatedCurrentState q s)
    (hv : IsValidCurrentState q s) : Function.Injective (stateCurrent q s) := by
  intro i j hij
  by_contra hne
  obtain ⟨e, he⟩ := stateCurrent_support_nonempty hv i
  have hf : e ∈ (stateCurrent q s j).support := hij ▸ he
  exact Finset.disjoint_left.mp (state_hdisjoint hs i j hne) he hf

end State

/-! ## The selected colour and the renormalized envelope -/

/--
The colour class selected for a current: one carrying the selected-link attenuation of the selected-link estimate.
-/
noncomputable def stateColor (β K : ℝ) (J : IntegerCurrent B) : Fin 8 := by
  classical
  exact if h : 0 ≤ β ∧ 0 ≤ K then
    Classical.choose (selectedCurrentActivity_le_one216 J β K h.1 h.2) else 0

theorem stateColor_spec (β K : ℝ) (hβ : 0 ≤ β) (hK : 0 ≤ K) (J : IntegerCurrent B) :
    K * Real.exp (-((β / 2) *
      ∑ e ∈ colorClass J.support linkColor (stateColor β K J),
        physicalLinkCoefficient J e ^ 2 / (incidentPlaquetteCount e : ℝ))) ≤
      K * Real.exp (-((β / 216) * ∑ e ∈ J.support, physicalLinkCoefficient J e ^ 2)) := by
  have h : 0 ≤ β ∧ 0 ≤ K := ⟨hβ, hK⟩
  simp only [stateColor, h, and_self, dite_true]
  exact Classical.choose_spec (selectedCurrentActivity_le_one216 J β K hβ hK)

theorem physicalCoefficient_sum_ge_integerNormSq (J : IntegerCurrent B) :
    integerCurrentNormSq (fun e : Link B => J e) ≤
      ∑ e ∈ J.support, physicalLinkCoefficient J e ^ 2 := by
  have hsum : (∑ e ∈ J.support, (J e : ℝ) ^ 2) =
      integerCurrentNormSq (fun e : Link B => J e) := by
    unfold integerCurrentNormSq
    apply Finset.sum_subset (Finset.subset_univ J.support)
    intro e _ hnot
    have hzero : J e = 0 := by
      by_contra hne
      exact hnot (Finsupp.mem_support_iff.mpr hne)
    simp [hzero]
  have hfactor : (1 : ℝ) ≤ (2 * Real.pi) ^ 2 := by
    have hpi := Real.pi_gt_three
    nlinarith
  rw [← hsum]
  apply Finset.sum_le_sum
  intro e _
  have h := mul_le_mul_of_nonneg_right hfactor (sq_nonneg (J e : ℝ))
  simpa [physicalLinkCoefficient, mul_pow] using h

/-- **The renormalized envelope.** If the raw activity is at most `exp(β₁ ‖J‖²)` and
`β₁ ≤ β/216`, the one-link renormalized amplitude on the selected colour class is at most
`exp(−a(‖J‖² + |supp J|))`, `a = (β/216 − β₁)/2`. -/
theorem branchAmplitude_le_envelope (β β₁ K : ℝ) (hβ : 0 ≤ β) (hK : 0 ≤ K)
    (J : IntegerCurrent B)
    (hKJ : K ≤ Real.exp (β₁ * integerCurrentNormSq (fun e : Link B => J e)))
    (hRate : β₁ ≤ β / 216) :
    branchAmplitude β K J (stateColor β K J) ≤
      Real.exp (-(sourceRenormalizedRate β β₁ *
        (integerCurrentNormSq (fun e : Link B => J e) +
          ((currentSupport (fun e : Link B => J e)).card : ℝ)))) := by
  classical
  let n := integerCurrentNormSq (fun e : Link B => J e)
  have hnorm : 0 ≤ n := by
    dsimp [n]
    unfold integerCurrentNormSq
    exact Finset.sum_nonneg fun e _ => by positivity
  have hcard : ((currentSupport (fun e : Link B => J e)).card : ℝ) ≤ n :=
    currentSupport_card_le_integerCurrentNormSq _
  have hphys := physicalCoefficient_sum_ge_integerNormSq J
  have hclosed : closedActivity K J ≤ K := by
    unfold closedActivity
    split_ifs
    · exact le_rfl
    · exact hK
  calc
    branchAmplitude β K J (stateColor β K J) ≤
        K * Real.exp (-((β / 2) *
          ∑ e ∈ colorClass J.support linkColor (stateColor β K J),
            physicalLinkCoefficient J e ^ 2 / (incidentPlaquetteCount e : ℝ))) :=
      mul_le_mul_of_nonneg_right hclosed (Real.exp_pos _).le
    _ ≤ K * Real.exp (-((β / 216) * ∑ e ∈ J.support, physicalLinkCoefficient J e ^ 2)) :=
      stateColor_spec β K hβ hK J
    _ ≤ K * Real.exp (-((β / 216) * n)) := by
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hK
      have : (β / 216) * n ≤ (β / 216) * ∑ e ∈ J.support, physicalLinkCoefficient J e ^ 2 :=
        mul_le_mul_of_nonneg_left hphys (by positivity)
      linarith
    _ ≤ Real.exp (β₁ * n) * Real.exp (-((β / 216) * n)) :=
      mul_le_mul_of_nonneg_right hKJ (Real.exp_pos _).le
    _ = Real.exp ((β₁ - β / 216) * n) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      unfold sourceRenormalizedRate
      have ha : 0 ≤ β / 216 - β₁ := by linarith
      nlinarith [mul_nonneg ha (sub_nonneg.mpr hcard), mul_nonneg ha hnorm]

/-! ## the branch mixture's branch integral as a family integral -/

/-- the branch mixture's Expansion branch integral is the raw family integral of the lineages of the state. -/
theorem sourceExpansionBranchIntegral_eq_gaugeBranchIntegral (β t : ℝ) (hβ : 0 ≤ β)
    (μ : SourceW B) (q : SourcePoissonEdge B → ℕ) (z : ℕ → ℝ)
    (b : CurrentExpansionTerm B) :
    sourceExpansionBranchIntegral β t hβ μ q z b =
      gaugeBranchIntegral β hβ t μ
        (stateActivity (sourceAssignmentIntegerFrequency q)
          (sourceAssignmentIntegerActivity z) b.state)
        (stateCurrent (sourceAssignmentIntegerFrequency q) b.state) := by
  unfold sourceExpansionBranchIntegral gaugeBranchIntegral
  refine integral_congr_ae (ae_of_all _ fun α => ?_)
  beta_reduce
  congr 2
  unfold currentStateProduct currentFactor
  rw [← Finset.prod_coe_sort]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [stateCurrent, sourceBranchModeCurrent_inner]
  rfl

end FroehlichSpencer.FS82.Root.MomentComparisonAssembly

end
