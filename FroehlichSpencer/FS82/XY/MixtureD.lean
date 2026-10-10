/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.XY.StateD
public import FroehlichSpencer.FS82.XY.Activity3
import all FroehlichSpencer.FS82.XY.CurrentExpansionD

/-!
# the sum over co-closed integer currents as a positive branch mixture, `d ≥ 3`

The dimension-generic form of `XY/Terms3.lean` and `XY/Mixture3.lean`.

For the dual complex of a
box of dimension `d ≥ 3`, a real translation `shift` of the field and `β > 0`:

`Re ∑_{j co-closed} e^{i⟨shift, j⟩} e^{−2π²β⟨j,(d₁†d₁)⁻¹j⟩} = ∑_ω w_ω · N_ω(shift)`,

a countable sum over branches `ω = (q, t)`: a mode assignment `q` and a terminal state `t` of the
expansion of its cosine product with the base-near relation.

`w_ω ≥ 0` and `N_ω(shift)` is the
gauge-averaged integral of the cosine product of the state, which is a Gaussian integral
(`XY/StateD.lean`).

On each branch Jensen's inequality gives
`N_ω(shift) ≥ exp(−∑ γ(amp_l) θ'_l²) N_ω(0)` for phase representatives `θ'`.

* `termsD`, `BranchD`, `branchCurrentD`, `branchAmpD`, `branchWeightD`, `branchIntegralD`.
* `branchD_jensen`.
* `closedGaussian_summable`: the Gaussian weights are summable over the co-closed currents.
* `closedCharacterSum`, `branchD_hasSum`.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

@[expose] public section

namespace FroehlichSpencer.FS82.XY.DualD

open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Gaussian
open FroehlichSpencer.FS82.Poisson
open FroehlichSpencer.FS82.Root
open FroehlichSpencer.FS82.Currents
open FroehlichSpencer.FS82.Moment
open FroehlichSpencer.FS82.XY.GaugeAverage
open FroehlichSpencer.FS82.XY.ExpansionD.Generic

variable {d : ℕ} {B : Box d}

/-! ## Frequencies and the expansion -/

/-- The integer frequency of a mode assignment. -/
def assignmentFrequencyD (q : DualDForm B (d - 2) → ℕ) : DualDForm B (d - 2) → ℤ :=
  fun e => ((q e + 1 : ℕ) : ℤ)

theorem integerActivity_assignmentFrequencyD (z : ℕ → ℝ) (q : DualDForm B (d - 2) → ℕ)
    (e : DualDForm B (d - 2)) :
    integerActivity z (abs (assignmentFrequencyD q e)) = z (positiveMode (q e)) := by
  have hpos : (0 : ℤ) < ((q e + 1 : ℕ) : ℤ) := by exact_mod_cast Nat.succ_pos _
  unfold assignmentFrequencyD
  rw [abs_of_pos hpos]
  simp only [integerActivity, hpos, ↓reduceIte, Int.toNat_natCast, positiveMode]

theorem sourceCurrentProduct_assignmentD (z : ℕ → ℝ) (q : DualDForm B (d - 2) → ℕ)
    (φ : DualDForm B (d - 2) → ℝ) :
    ExpansionD.Generic.sourceCurrentProduct (assignmentFrequencyD q) (integerActivity z) φ =
      ∏ e, (1 + z (positiveMode (q e)) * Real.cos (φ e * ((q e + 1 : ℕ) : ℝ))) := by
  unfold ExpansionD.Generic.sourceCurrentProduct
  refine Finset.prod_congr rfl fun e _ => ?_
  rw [integerActivity_assignmentFrequencyD]
  simp [assignmentFrequencyD]

/-- The terminal states of the expansion of a mode assignment at the root activity, for the
base-near relation. -/
noncomputable def termsD (q : DualDForm B (d - 2) → ℕ) :
    List (CurrentExpansionTerm (DualDForm B (d - 2))) :=
  Classical.choose (exists_baseNearCurrentExpansion (d - 2) (assignmentFrequencyD q)
    (integerActivity rootActivity) (integerActivity_zero _)
    (integerActivity_nonneg fun n => (rootActivity_pos n).le)
    (integerActivity_pos rootActivity_pos))

theorem termsD_spec (q : DualDForm B (d - 2) → ℕ) :
    IsFixedFrequencyCurrentExpansion (baseNearRelation B (d - 2)) (assignmentFrequencyD q)
      (integerActivity rootActivity) (termsD q) :=
  (Classical.choose_spec (exists_baseNearCurrentExpansion (d - 2) (assignmentFrequencyD q)
    (integerActivity rootActivity) (integerActivity_zero _)
    (integerActivity_nonneg fun n => (rootActivity_pos n).le)
    (integerActivity_pos rootActivity_pos))).1

/-- The outer index: a mode assignment and a terminal state of its expansion. -/
abbrev BranchD (B : Box d) := Σ q : DualDForm B (d - 2) → ℕ, Fin (termsD q).length

/-- The expansion term of a branch. -/
noncomputable def branchTermD (ω : BranchD B) : CurrentExpansionTerm (DualDForm B (d - 2)) :=
  (termsD ω.1).get ω.2

/-- The terminal state of a branch. -/
noncomputable abbrev branchStateD (ω : BranchD B) :
    Finset (ActivityLineage (DualDForm B (d - 2))) := (branchTermD ω).state

/-- The integer frequency of a branch. -/
abbrev branchFrequencyD (ω : BranchD B) : DualDForm B (d - 2) → ℤ := assignmentFrequencyD ω.1

theorem branchTermD_mem (ω : BranchD B) : branchTermD ω ∈ termsD ω.1 := List.get_mem _ _

theorem branchStateD_separated (ω : BranchD B) :
    IsSeparatedCurrentState (baseNearRelation B (d - 2)) (branchFrequencyD ω) (branchStateD ω) :=
  (termsD_spec ω.1).2.1 _ (branchTermD_mem ω)

theorem branchTermD_weight_pos (ω : BranchD B) : 0 < (branchTermD ω).weight :=
  (termsD_spec ω.1).2.2.2.1 _ (branchTermD_mem ω)

theorem branchD_lineageCoefficient_pos (ω : BranchD B)
    {l : ActivityLineage (DualDForm B (d - 2))} (hl : l ∈ branchStateD ω) :
    0 < lineageCoefficient (branchFrequencyD ω) (integerActivity rootActivity) l :=
  (termsD_spec ω.1).2.2.2.2.2.2.1 _ (branchTermD_mem ω) l hl

/-- The lineages of a branch. -/
abbrev BranchIndexD (ω : BranchD B) := StateIndexD (branchStateD ω)

/-- The current of a lineage of a branch, zero if it is not co-closed. -/
noncomputable def branchCurrentD (ω : BranchD B) (i : BranchIndexD ω) : DualDForm B (d - 2) → ℤ :=
  stateCurrentD (branchFrequencyD ω) (branchStateD ω) i

/-- The renormalized amplitude of a lineage of a branch. -/
noncomputable def branchAmpD (β : ℝ) (ω : BranchD B) (i : BranchIndexD ω) : ℝ :=
  stateAmpD β (branchFrequencyD ω) (integerActivity rootActivity) (branchStateD ω) i

/-- The weight of a branch. -/
noncomputable def branchWeightD (ω : BranchD B) : ℝ :=
  assignmentCoefficient rootActivity ω.1 * (branchTermD ω).weight

/-- The state integral of a branch, with the field translated by `shift`. -/
noncomputable def branchIntegralD (hd : 3 ≤ d) (β : ℝ) (shift : DualDForm B (d - 2) → ℝ)
    (ω : BranchD B) : ℝ :=
  stateIntegralD hd β (branchFrequencyD ω) (integerActivity rootActivity) (branchStateD ω) shift

theorem branchAmpD_nonneg (β : ℝ) (ω : BranchD B) (i : BranchIndexD ω) :
    0 ≤ branchAmpD β ω i := by
  unfold branchAmpD stateAmpD stateActivityD
  refine mul_nonneg ?_ (Real.exp_pos _).le
  by_cases hcl : ClosedD stencilInt (lineageCurrent (branchFrequencyD ω) i.1)
  · rw [closedActivityD_of_closed _ hcl]
    exact (branchD_lineageCoefficient_pos ω i.2).le
  · rw [closedActivityD_of_not_closed _ hcl]

theorem branchWeightD_nonneg (ω : BranchD B) : 0 ≤ branchWeightD ω :=
  mul_nonneg (assignmentCoefficient_pos rootActivity ω.1 fun _ => rootActivity_pos _).le
    (branchTermD_weight_pos ω).le

theorem branchIntegralD_eq_gaussian (hd : 3 ≤ d) {β : ℝ} (hβ : 0 ≤ β)
    (shift : DualDForm B (d - 2) → ℝ) (ω : BranchD B) :
    branchIntegralD hd β shift ω =
      ∫ y : EuclideanSpace ℝ (BranchIndexD ω),
        ∏ i, (1 + branchAmpD β ω i * Real.cos (y i + linkPairing shift (branchCurrentD ω i)))
        ∂multivariateGaussian 0
          (stateCovarianceD hd β (branchFrequencyD ω) (branchStateD ω)) :=
  stateIntegralD_eq_gaussian hd hβ _ _ _ (branchStateD_separated ω) shift

theorem branchIntegralD_nonneg (hd : 3 ≤ d) {β : ℝ} (hβ : 0 ≤ β)
    (shift : DualDForm B (d - 2) → ℝ) (ω : BranchD B) (hamp : ∀ i, branchAmpD β ω i ≤ 1) :
    0 ≤ branchIntegralD hd β shift ω := by
  rw [branchIntegralD_eq_gaussian hd hβ]
  exact integral_cosineProduct_gaussian_nonneg _ _ _ (branchAmpD_nonneg β ω) hamp

theorem branchIntegralD_zero_pos (hd : 3 ≤ d) {β : ℝ} (hβ : 0 ≤ β) (ω : BranchD B)
    (hamp : ∀ i, branchAmpD β ω i < 1) : 0 < branchIntegralD hd β 0 ω := by
  rw [branchIntegralD_eq_gaussian hd hβ]
  exact integral_cosineProduct_gaussian_pos _ _ _ (branchAmpD_nonneg β ω) hamp

theorem linkPairing_zero_leftD {E : Type*} [Fintype E] (j : E → ℤ) :
    linkPairing (0 : E → ℝ) j = 0 := by
  simp [linkPairing]

/-- **Jensen on one branch, with phase representatives.** -/
theorem branchD_jensen (hd : 3 ≤ d) {β : ℝ} (hβ : 0 ≤ β) (shift : DualDForm B (d - 2) → ℝ)
    (ω : BranchD B) (hamp : ∀ i, branchAmpD β ω i < 1) (θ' : BranchIndexD ω → ℝ)
    (hθ : ∀ i, ∃ n : ℤ, linkPairing shift (branchCurrentD ω i) + θ' i = 2 * Real.pi * (n : ℝ)) :
    Real.exp (-∑ i, SourceJensen.sourceJensenGamma (branchAmpD β ω i) * θ' i ^ 2) *
        branchIntegralD hd β 0 ω ≤ branchIntegralD hd β shift ω := by
  rw [branchIntegralD_eq_gaussian hd hβ, branchIntegralD_eq_gaussian hd hβ]
  have hJ := gaussian_cosineProduct_jensen
    (stateCovarianceD_posSemidef hd hβ (branchStateD_separated ω))
    (branchAmpD β ω) θ' (branchAmpD_nonneg β ω) hamp
  have hzero : (fun y : EuclideanSpace ℝ (BranchIndexD ω) =>
      ∏ i, (1 + branchAmpD β ω i *
        Real.cos (y i + linkPairing (0 : DualDForm B (d - 2) → ℝ) (branchCurrentD ω i)))) =
      fun y => ∏ i, (1 + branchAmpD β ω i * Real.cos (y i)) := by
    funext y
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [linkPairing_zero_leftD, add_zero]
  have hshift : (fun y : EuclideanSpace ℝ (BranchIndexD ω) =>
      ∏ i, (1 + branchAmpD β ω i *
        Real.cos (y i + linkPairing shift (branchCurrentD ω i)))) =
      fun y => ∏ i, (1 + branchAmpD β ω i * Real.cos (y i - θ' i)) := by
    funext y
    refine Finset.prod_congr rfl fun i _ => ?_
    obtain ⟨n, hn⟩ := hθ i
    have harg : y i + linkPairing shift (branchCurrentD ω i) =
        (y i - θ' i) + (n : ℝ) * (2 * Real.pi) := by linarith
    rw [harg, Real.cos_add_int_mul_two_pi]
  rw [hzero, hshift]
  exact hJ

/-! ## The integral of a mode assignment as a sum over its branches -/

theorem integrable_currentStateProductD (S : Matrix (DualDForm B (d - 2)) (DualDForm B (d - 2)) ℝ)
    (q : DualDForm B (d - 2) → ℤ) (z : ℤ → ℝ)
    (s : Finset (ActivityLineage (DualDForm B (d - 2)))) (shift : DualDForm B (d - 2) → ℝ) :
    Integrable (fun ω => ExpansionD.Generic.currentStateProduct q z
      (fun e => gaugeFieldD stencilInt ω e + shift e) s)
      (gaugeMeasureD (DualDForm B (d - 3)) S) := by
  refine Integrable.of_bound ?_ (∏ t ∈ s, (1 + |lineageCoefficient q z t|))
    (ae_of_all _ fun ω => ?_)
  · have hm : Measurable fun ω : EuclideanSpace ℝ (DualDForm B (d - 2)) ×
        (DualDForm B (d - 3) → ℝ) => ExpansionD.Generic.currentStateProduct q z
          (fun e => gaugeFieldD stencilInt ω e + shift e) s := by
      unfold ExpansionD.Generic.currentStateProduct ExpansionD.Generic.currentFactor
        ExpansionD.Generic.currentPhase
      refine Finset.measurable_prod _ fun t _ => ?_
      refine measurable_const.add (measurable_const.mul (Real.measurable_cos.comp ?_))
      exact Finset.measurable_sum _ fun e _ =>
        ((measurable_gaugeFieldD_apply stencilInt e).add measurable_const).mul_const _
    exact hm.aestronglyMeasurable
  · unfold ExpansionD.Generic.currentStateProduct ExpansionD.Generic.currentFactor
    rw [Real.norm_eq_abs, Finset.abs_prod]
    refine Finset.prod_le_prod₀ (fun t _ => abs_nonneg _) fun t _ => ?_
    refine (abs_add_le _ _).trans ?_
    rw [abs_one, abs_mul]
    have hc := Real.abs_cos_le_one (ExpansionD.Generic.currentPhase
      (fun e => gaugeFieldD stencilInt ω e + shift e) (lineageCurrent q t))
    nlinarith [abs_nonneg (lineageCoefficient q z t)]

/-- The weighted sum of the state integrals of one mode assignment. -/
noncomputable def assignmentInnerD (hd : 3 ≤ d) (β : ℝ) (shift : DualDForm B (d - 2) → ℝ)
    (q : DualDForm B (d - 2) → ℕ) : ℝ :=
  ∑ i : Fin (termsD q).length, ((termsD q).get i).weight *
    stateIntegralD hd β (assignmentFrequencyD q) (integerActivity rootActivity)
      ((termsD q).get i).state shift

/-- **The integral of the cosine product of a mode assignment as the weighted sum of its terminal
state integrals.** -/
theorem assignmentIntegral_eq_innerD (hd : 3 ≤ d) (β : ℝ) (shift : DualDForm B (d - 2) → ℝ)
    (q : DualDForm B (d - 2) → ℕ) :
    ∫ ω, ∏ e, (1 + rootActivity (positiveMode (q e)) *
        Real.cos ((gaugeFieldD stencilInt ω e + shift e) * ((q e + 1 : ℕ) : ℝ)))
          ∂gaugeMeasureD (DualDForm B (d - 3)) (dualCovariance hd B β) =
      assignmentInnerD hd β shift q := by
  have hpt : ∀ ω : EuclideanSpace ℝ (DualDForm B (d - 2)) × (DualDForm B (d - 3) → ℝ),
      (∏ e, (1 + rootActivity (positiveMode (q e)) *
        Real.cos ((gaugeFieldD stencilInt ω e + shift e) * ((q e + 1 : ℕ) : ℝ)))) =
      ∑ i : Fin (termsD q).length, ((termsD q).get i).weight *
        ExpansionD.Generic.currentStateProduct (assignmentFrequencyD q)
          (integerActivity rootActivity)
          (fun e => gaugeFieldD stencilInt ω e + shift e) ((termsD q).get i).state := by
    intro ω
    rw [← sourceCurrentProduct_assignmentD rootActivity q
      (fun e => gaugeFieldD stencilInt ω e + shift e),
      (termsD_spec q).2.2.2.2.2.1, ExpansionD.Generic.currentExpansionSum,
      list_map_sum_eq_fin_sum]
  simp_rw [hpt]
  rw [integral_finsetSum _ fun i _ =>
    (integrable_currentStateProductD (dualCovariance hd B β) _ _ _ shift).const_mul _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_const_mul]
  rfl

/-! ## Summability of the Gaussian weights -/

theorem summable_int_gaussian {c : ℝ} (hc : 0 < c) :
    Summable fun n : ℤ => Real.exp (-(c * (n : ℝ) ^ 2)) := by
  have hr0 : 0 ≤ Real.exp (-c) := (Real.exp_pos _).le
  have hr1 : Real.exp (-c) < 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  have hnat : Summable fun n : ℕ => Real.exp (-(c * (n : ℝ) ^ 2)) := by
    refine Summable.of_nonneg_of_le (fun n => (Real.exp_pos _).le) (fun n => ?_)
      (summable_geometric_of_lt_one hr0 hr1)
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have hn : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · simp [h0]
      · have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hpos
        nlinarith
    nlinarith
  rw [summable_int_iff_summable_nat_and_neg]
  refine ⟨by simpa using hnat, ?_⟩
  simpa using hnat

/-- **The Gaussian weights are summable over the co-closed integer currents.** -/
theorem closedGaussian_summable (hd : 3 ≤ d) {β : ℝ} (hβ : 0 < β) :
    Summable fun j : {j : DualDForm B (d - 2) → ℤ // ClosedD stencilInt j} =>
      Real.exp (-(quadraticD (dualCovariance hd B β) j.1 / 2)) := by
  have hd0 : (0 : ℝ) < (d : ℝ) := by
    have : 0 < d := by omega
    exact_mod_cast this
  set c : ℝ := Real.pi ^ 2 * β / (2 * (d : ℝ) ^ 2) with hc
  have hc0 : 0 < c := by positivity
  have hall : Summable fun j : DualDForm B (d - 2) → ℤ =>
      ∏ e, Real.exp (-(c * ((j e : ℤ) : ℝ) ^ 2)) :=
    summable_pi_prod_of_summable (fun n : ℤ => Real.exp (-(c * (n : ℝ) ^ 2)))
      (summable_int_gaussian hc0)
  refine Summable.of_nonneg_of_le (fun j => (Real.exp_pos _).le) (fun j => ?_)
    (hall.subtype _)
  have hco := (closedD_stencilInt_iff hd j.1).mp j.2
  rw [Function.comp_apply, ← Real.exp_sum, quadraticD_dualCovariance hd β j.1 hco]
  apply Real.exp_le_exp.mpr
  have hcoer := dualD_normSq_le_quotientCovarianceQuadratic hd
    (⟨currentVector j.1, hco⟩ : coClosed (dualDExactOneComplex hd B))
  have hnorm : inner ℝ (currentVector j.1) (currentVector j.1) =
      ∑ e, ((j.1 e : ℤ) : ℝ) ^ 2 := by
    rw [currentVector_inner_self]
    rfl
  rw [hnorm] at hcoer
  have hsum : ∑ e, -(c * ((j.1 e : ℤ) : ℝ) ^ 2) = -(c * ∑ e, ((j.1 e : ℤ) : ℝ) ^ 2) := by
    rw [Finset.sum_neg_distrib, Finset.mul_sum]
  rw [hsum]
  have hQ0 := quotientCovarianceQuadratic_nonneg (dualDExactOneComplex hd B)
    (⟨currentVector j.1, hco⟩ : coClosed (dualDExactOneComplex hd B))
  have hkey : c * ∑ e, ((j.1 e : ℤ) : ℝ) ^ 2 ≤
      4 * Real.pi ^ 2 * β * quotientCovarianceQuadratic (dualDExactOneComplex hd B)
        ⟨currentVector j.1, hco⟩ / 2 := by
    have h1 := mul_le_mul_of_nonneg_left hcoer hc0.le
    refine h1.trans (le_of_eq ?_)
    rw [hc]
    field_simp
  linarith

/-! ## The branch mixture -/

/-- The character sum over the co-closed integer currents. -/
noncomputable def closedCharacterSum (hd : 3 ≤ d) (β : ℝ) (shift : DualDForm B (d - 2) → ℝ) : ℂ :=
  ∑' j : {j : DualDForm B (d - 2) → ℤ // ClosedD stencilInt j},
    Complex.exp (Complex.I * (linkPairing shift j.1 : ℝ)) *
      Complex.exp (-(quadraticD (dualCovariance hd B β) j.1 / 2 : ℝ))

/-- The character sum as a sum over mode assignments of real terms. -/
theorem assignmentD_hasSum (hd : 3 ≤ d) {β : ℝ} (hβ : 0 < β)
    (shift : DualDForm B (d - 2) → ℝ) :
    HasSum (fun q : DualDForm B (d - 2) → ℕ =>
        ((assignmentCoefficient rootActivity q * assignmentInnerD hd β shift q : ℝ) : ℂ))
      (closedCharacterSum hd β shift) := by
  have hC := closedCharacterSum_hasSum_assignment (V := DualDForm B (d - 3)) stencilInt
    (dualCovariance_posSemidef hd B hβ.le) shift rootActivity
    hasSum_inactiveWeight_rootActivity inactiveWeight_rootActivity_nonneg
    (fun q => rootActivity_pos _) (closedGaussian_summable hd hβ)
  have hterm : ∀ q : DualDForm B (d - 2) → ℕ,
      (assignmentCoefficient rootActivity q : ℂ) *
        ((∫ ω, ∏ e, (1 + rootActivity (positiveMode (q e)) *
            Real.cos ((gaugeFieldD stencilInt ω e + shift e) * ((q e + 1 : ℕ) : ℝ)))
              ∂gaugeMeasureD (DualDForm B (d - 3)) (dualCovariance hd B β) : ℝ) : ℂ) =
      ((assignmentCoefficient rootActivity q * assignmentInnerD hd β shift q : ℝ) : ℂ) := by
    intro q
    rw [assignmentIntegral_eq_innerD hd β shift q, Complex.ofReal_mul]
  simp_rw [hterm] at hC
  exact hC

/-- **The character sum as a positive branch mixture.** -/
theorem branchD_hasSum (hd : 3 ≤ d) {β : ℝ} (hβ : 0 < β) (shift : DualDForm B (d - 2) → ℝ)
    (hamp : ∀ (ω : BranchD B) (i : BranchIndexD ω), branchAmpD β ω i ≤ 1) :
    HasSum (fun ω : BranchD B => branchWeightD ω * branchIntegralD hd β shift ω)
      (closedCharacterSum hd β shift).re := by
  have hC := assignmentD_hasSum hd hβ shift
  have hg : HasSum (fun q : DualDForm B (d - 2) → ℕ =>
      assignmentCoefficient rootActivity q * assignmentInnerD hd β shift q)
      (closedCharacterSum hd β shift).re := by
    have h := Complex.hasSum_re hC
    simpa only [Complex.ofReal_re] using h
  have hf : ∀ q : DualDForm B (d - 2) → ℕ, HasSum (fun i : Fin (termsD q).length =>
      branchWeightD (⟨q, i⟩ : BranchD B) * branchIntegralD hd β shift ⟨q, i⟩)
      (assignmentCoefficient rootActivity q * assignmentInnerD hd β shift q) := by
    intro q
    have h := hasSum_fintype (fun i : Fin (termsD q).length =>
      branchWeightD (⟨q, i⟩ : BranchD B) * branchIntegralD hd β shift ⟨q, i⟩)
    convert h using 1
    simp only [assignmentInnerD, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => (mul_assoc _ _ _).symm
  have hnonneg : ∀ ω : BranchD B, 0 ≤ branchWeightD ω * branchIntegralD hd β shift ω :=
    fun ω => mul_nonneg (branchWeightD_nonneg ω)
      (branchIntegralD_nonneg hd hβ.le shift ω (hamp ω))
  have hsummable : Summable fun ω : BranchD B =>
      branchWeightD ω * branchIntegralD hd β shift ω := by
    rw [summable_sigma_of_nonneg hnonneg]
    refine ⟨fun q => (hf q).summable, ?_⟩
    have hEq : (fun q : DualDForm B (d - 2) → ℕ => ∑' i : Fin (termsD q).length,
        branchWeightD (⟨q, i⟩ : BranchD B) * branchIntegralD hd β shift ⟨q, i⟩) =
        fun q => assignmentCoefficient rootActivity q * assignmentInnerD hd β shift q := by
      funext q
      exact (hf q).tsum_eq
    rw [hEq]
    exact hg.summable
  exact HasSum.sigma_of_hasSum hg hf hsummable

end FroehlichSpencer.FS82.XY.DualD

end
