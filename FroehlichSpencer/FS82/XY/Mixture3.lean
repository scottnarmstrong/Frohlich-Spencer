/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.XY.Terms3

/-!
# the positive branch mixture in three dimensions

The tilted chord Poisson sum is a countable mixture of the terminal state integrals with positive
weights, FS82 (4.32) and (4.35):

`∑_k dualQuadraticExp A w k = e^{π⟨w, A⁻¹w⟩} ∑_ω d_ω ∫ ∏ (1 + K cos(⟨ϱ, φ + s_w⟩))`.

After renormalization every state integral is a Gaussian integral of a cosine product with
amplitudes in `[0, 1)`, so it is nonnegative, and Jensen's inequality compares the translated
integral with the untranslated one branch by branch.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

@[expose] public section

namespace FroehlichSpencer.FS82.XY

open FroehlichSpencer.FS82.Poisson
open FroehlichSpencer.FS82.Root
open FroehlichSpencer.FS82.Moment
open FroehlichSpencer.FS82.XY.Expansion3
open FroehlichSpencer.FS82.XY.GaugeAverage

variable {B : Dual3Box}

/-! ## The data of a branch -/

/-- The lineages of a branch: the Jensen index. -/
abbrev XY3BranchIndex (ω : XY3Branch B) := StateIndex (xy3BranchState ω)

/-- The co-closed current of a lineage of a branch. -/
noncomputable def xy3BranchCurrent (ω : XY3Branch B) (i : XY3BranchIndex ω) :
    Dual3Links B → ℤ :=
  stateCurrent (xy3BranchFrequency ω) (xy3BranchState ω) i

/-- The renormalized amplitude of a lineage of a branch. -/
noncomputable def xy3BranchAmp (β : ℝ) (ω : XY3Branch B) (i : XY3BranchIndex ω) : ℝ :=
  stateAmp β (xy3BranchFrequency ω) (integerActivity rootActivity) (xy3BranchState ω) i

/-- The outer weight of a branch. -/
noncomputable def xy3BranchWeight (ω : XY3Branch B) : ℝ :=
  assignmentCoefficient rootActivity ω.1 * (xy3BranchTerm ω).weight

/-- The state integral of a branch with the link field translated by `shift`. -/
noncomputable def xy3BranchIntegral (β : ℝ) (shift : Dual3Links B → ℝ) (ω : XY3Branch B) : ℝ :=
  stateIntegral β (xy3BranchFrequency ω) (integerActivity rootActivity) (xy3BranchState ω) shift

theorem xy3BranchAmp_nonneg (β : ℝ) (ω : XY3Branch B) (i : XY3BranchIndex ω) :
    0 ≤ xy3BranchAmp β ω i := by
  unfold xy3BranchAmp stateAmp familyAmp stateActivity
  refine mul_nonneg ?_ (Real.exp_pos _).le
  by_cases hcl : RootedTreeGauge.CoClosed (xyDual3RootedTree B)
      (lineageCurrent (xy3BranchFrequency ω) i.1)
  · rw [closedActivity_of_coClosed _ hcl]
    exact (xy3Branch_lineageCoefficient_pos ω i.2).le
  · rw [closedActivity_of_not_coClosed _ hcl]

theorem xy3BranchWeight_nonneg (ω : XY3Branch B) : 0 ≤ xy3BranchWeight ω :=
  mul_nonneg (assignmentCoefficient_pos rootActivity ω.1 fun _ => rootActivity_pos _).le
    (xy3BranchWeight_pos ω).le

theorem xy3BranchIntegral_eq_gaussian {β : ℝ} (hβ : 0 < β) (shift : Dual3Links B → ℝ)
    (ω : XY3Branch B) :
    xy3BranchIntegral β shift ω =
      ∫ y : EuclideanSpace ℝ (XY3BranchIndex ω),
        ∏ i, (1 + xy3BranchAmp β ω i *
          Real.cos (y i + linkPairing shift (xy3BranchCurrent ω i)))
        ∂multivariateGaussian 0 (stateCovariance β (xy3BranchFrequency ω) (xy3BranchState ω)) :=
  stateIntegral_eq_gaussian hβ _ _ _ (xy3BranchState_separated ω) shift

theorem xy3BranchIntegral_nonneg {β : ℝ} (hβ : 0 < β) (shift : Dual3Links B → ℝ)
    (ω : XY3Branch B) (hamp : ∀ i, xy3BranchAmp β ω i ≤ 1) :
    0 ≤ xy3BranchIntegral β shift ω := by
  rw [xy3BranchIntegral_eq_gaussian hβ]
  exact integral_cosineProduct_gaussian_nonneg _ _ _ (xy3BranchAmp_nonneg β ω) hamp

theorem linkPairing_zero_left (j : Dual3Links B → ℤ) :
    linkPairing (0 : Dual3Links B → ℝ) j = 0 := by
  simp [linkPairing]

theorem xy3BranchIntegral_zero_pos {β : ℝ} (hβ : 0 < β) (ω : XY3Branch B)
    (hamp : ∀ i, xy3BranchAmp β ω i < 1) :
    0 < xy3BranchIntegral β 0 ω := by
  rw [xy3BranchIntegral_eq_gaussian hβ]
  exact integral_cosineProduct_gaussian_pos _ _ _ (xy3BranchAmp_nonneg β ω) hamp

/-- **Jensen on one branch, with phase representatives.** If every lineage with a nonzero
amplitude has a representative `θ' i` with `⟨shift, J_i⟩ + θ' i ∈ 2πℤ`, then the translated state
integral is at least `exp(−∑ γ(amp_i) θ'_i²)` times the untranslated one. -/
theorem xy3Branch_jensen {β : ℝ} (hβ : 0 < β) (shift : Dual3Links B → ℝ) (ω : XY3Branch B)
    (hamp : ∀ i, xy3BranchAmp β ω i < 1) (θ' : XY3BranchIndex ω → ℝ)
    (hθ : ∀ i, xy3BranchAmp β ω i ≠ 0 → ∃ n : ℤ,
      linkPairing shift (xy3BranchCurrent ω i) + θ' i = 2 * Real.pi * (n : ℝ)) :
    Real.exp (-∑ i, SourceJensen.sourceJensenGamma (xy3BranchAmp β ω i) * θ' i ^ 2) *
        xy3BranchIntegral β 0 ω ≤ xy3BranchIntegral β shift ω := by
  rw [xy3BranchIntegral_eq_gaussian hβ, xy3BranchIntegral_eq_gaussian hβ]
  have hJ := gaussian_cosineProduct_jensen
    (stateCovariance_posSemidef hβ (xy3BranchState_separated ω))
    (xy3BranchAmp β ω) θ' (xy3BranchAmp_nonneg β ω) hamp
  have hzero : (fun y : EuclideanSpace ℝ (XY3BranchIndex ω) =>
      ∏ i, (1 + xy3BranchAmp β ω i *
        Real.cos (y i + linkPairing (0 : Dual3Links B → ℝ) (xy3BranchCurrent ω i)))) =
      fun y => ∏ i, (1 + xy3BranchAmp β ω i * Real.cos (y i)) := by
    funext y
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [linkPairing_zero_left, add_zero]
  have hshift : (fun y : EuclideanSpace ℝ (XY3BranchIndex ω) =>
      ∏ i, (1 + xy3BranchAmp β ω i *
        Real.cos (y i + linkPairing shift (xy3BranchCurrent ω i)))) =
      fun y => ∏ i, (1 + xy3BranchAmp β ω i * Real.cos (y i - θ' i)) := by
    funext y
    refine Finset.prod_congr rfl fun i _ => ?_
    by_cases h0 : xy3BranchAmp β ω i = 0
    · simp [h0]
    · obtain ⟨n, hn⟩ := hθ i h0
      have harg : y i + linkPairing shift (xy3BranchCurrent ω i) =
          (y i - θ' i) + (n : ℝ) * (2 * Real.pi) := by linarith
      rw [harg, Real.cos_add_int_mul_two_pi]
  rw [hzero, hshift]
  exact hJ

/-! ## The outer mixture -/

/-- The weighted sum of the state integrals of one mode assignment. -/
noncomputable def xy3AssignmentInner (β : ℝ) (shift : Dual3Links B → ℝ)
    (q : Dual3Links B → ℕ) : ℝ :=
  ∑ i : Fin (xy3Terms q).length, ((xy3Terms q).get i).weight *
    stateIntegral β (assignmentFrequency q) (integerActivity rootActivity)
      ((xy3Terms q).get i).state shift

/-- The tilted chord Poisson sum as a sum over mode assignments of real terms. -/
theorem xy3_assignment_hasSum {β : ℝ} (hβ : 0 < β) (τ : (xyDual3RootedTree B).Chord → ℝ)
    (t : ℝ) :
    HasSum (fun q : Dual3Links B → ℕ =>
        ((assignmentCoefficient rootActivity q *
          (tiltConstant (xyDual3RootedTree B) (xyDual3ChordMatrix (B := B) β)
              (tiltVector (xyDual3RootedTree B) τ t) *
            xy3AssignmentInner β (tiltShift (xyDual3RootedTree B)
              (xyDual3ChordMatrix (B := B) β) (tiltVector (xyDual3RootedTree B) τ t)) q) : ℝ) : ℂ))
      (∑' k : (xyDual3RootedTree B).Chord → ℤ,
        dualQuadraticExp (xyDual3ChordMatrix (B := B) β) (realTiltParameter τ t) k) := by
  have hC := xy3_chordSum_hasSum_assignment (B := B) hβ τ t rootActivity
    hasSum_inactiveWeight_rootActivity inactiveWeight_rootActivity_nonneg
    (fun q => rootActivity_pos _)
  have hterm : ∀ q : Dual3Links B → ℕ,
      (assignmentCoefficient rootActivity q : ℂ) *
        gaugeAssignmentMoment (xyDual3RootedTree B) (xyDual3ChordMatrix (B := B) β) τ t
          rootActivity q =
      ((assignmentCoefficient rootActivity q *
          (tiltConstant (xyDual3RootedTree B) (xyDual3ChordMatrix (B := B) β)
              (tiltVector (xyDual3RootedTree B) τ t) *
            xy3AssignmentInner β (tiltShift (xyDual3RootedTree B)
              (xyDual3ChordMatrix (B := B) β) (tiltVector (xyDual3RootedTree B) τ t)) q) : ℝ) :
        ℂ) := by
    intro q
    rw [gaugeAssignmentMoment_eq_branchSum hβ τ t q, Complex.ofReal_mul, Complex.ofReal_mul]
    rfl
  simp_rw [hterm] at hC
  exact hC

/-- The tilted chord Poisson sum is real. -/
theorem xy3_chordSum_ofReal_re {β : ℝ} (hβ : 0 < β) (τ : (xyDual3RootedTree B).Chord → ℝ)
    (t : ℝ) :
    (((∑' k : (xyDual3RootedTree B).Chord → ℤ,
        dualQuadraticExp (xyDual3ChordMatrix (B := B) β) (realTiltParameter τ t) k).re : ℝ) : ℂ) =
      ∑' k : (xyDual3RootedTree B).Chord → ℤ,
        dualQuadraticExp (xyDual3ChordMatrix (B := B) β) (realTiltParameter τ t) k := by
  have hC := xy3_assignment_hasSum (B := B) hβ τ t
  have hRe := Complex.hasSum_re hC
  simp only [Complex.ofReal_re] at hRe
  exact (Complex.hasSum_ofReal.mpr hRe).unique hC

/-- **The tilted chord Poisson sum as a positive branch mixture.** -/
theorem xy3_branch_hasSum {β : ℝ} (hβ : 0 < β) (τ : (xyDual3RootedTree B).Chord → ℝ) (t : ℝ)
    (hamp : ∀ (ω : XY3Branch B) (i : XY3BranchIndex ω), xy3BranchAmp β ω i ≤ 1) :
    HasSum (fun ω : XY3Branch B => xy3BranchWeight ω *
        xy3BranchIntegral β (tiltShift (xyDual3RootedTree B) (xyDual3ChordMatrix (B := B) β)
          (tiltVector (xyDual3RootedTree B) τ t)) ω)
      ((∑' k : (xyDual3RootedTree B).Chord → ℤ,
          dualQuadraticExp (xyDual3ChordMatrix (B := B) β) (realTiltParameter τ t) k).re /
        tiltConstant (xyDual3RootedTree B) (xyDual3ChordMatrix (B := B) β)
          (tiltVector (xyDual3RootedTree B) τ t)) := by
  have hC := xy3_assignment_hasSum (B := B) hβ τ t
  set shift := tiltShift (xyDual3RootedTree B) (xyDual3ChordMatrix (B := B) β)
    (tiltVector (xyDual3RootedTree B) τ t) with hshift
  set c := tiltConstant (xyDual3RootedTree B) (xyDual3ChordMatrix (B := B) β)
    (tiltVector (xyDual3RootedTree B) τ t) with hc
  have hcpos : 0 < c := tiltConstant_pos _ _ _
  set S : ℂ := ∑' k : (xyDual3RootedTree B).Chord → ℤ,
    dualQuadraticExp (xyDual3ChordMatrix (B := B) β) (realTiltParameter τ t) k with hS
  have hRe : HasSum (fun q : Dual3Links B → ℕ =>
      assignmentCoefficient rootActivity q * (c * xy3AssignmentInner β shift q)) S.re := by
    have h := Complex.hasSum_re hC
    simpa only [Complex.ofReal_re] using h
  have hg : HasSum (fun q : Dual3Links B → ℕ =>
      assignmentCoefficient rootActivity q * xy3AssignmentInner β shift q) (S.re / c) := by
    have h := hRe.mul_right c⁻¹
    have hfun : (fun q : Dual3Links B → ℕ =>
        assignmentCoefficient rootActivity q * (c * xy3AssignmentInner β shift q) * c⁻¹) =
        fun q => assignmentCoefficient rootActivity q * xy3AssignmentInner β shift q := by
      funext q
      field_simp
    rw [hfun] at h
    rwa [div_eq_mul_inv]
  have hf : ∀ q : Dual3Links B → ℕ, HasSum (fun i : Fin (xy3Terms q).length =>
      xy3BranchWeight (⟨q, i⟩ : XY3Branch B) * xy3BranchIntegral β shift ⟨q, i⟩)
      (assignmentCoefficient rootActivity q * xy3AssignmentInner β shift q) := by
    intro q
    have h := hasSum_fintype (fun i : Fin (xy3Terms q).length =>
      xy3BranchWeight (⟨q, i⟩ : XY3Branch B) * xy3BranchIntegral β shift ⟨q, i⟩)
    convert h using 1
    simp only [xy3AssignmentInner, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => (mul_assoc _ _ _).symm
  have hnonneg : ∀ ω : XY3Branch B, 0 ≤ xy3BranchWeight ω * xy3BranchIntegral β shift ω :=
    fun ω => mul_nonneg (xy3BranchWeight_nonneg ω)
      (xy3BranchIntegral_nonneg hβ shift ω (hamp ω))
  have hsummable : Summable fun ω : XY3Branch B =>
      xy3BranchWeight ω * xy3BranchIntegral β shift ω := by
    rw [summable_sigma_of_nonneg hnonneg]
    refine ⟨fun q => (hf q).summable, ?_⟩
    have hEq : (fun q : Dual3Links B → ℕ => ∑' i : Fin (xy3Terms q).length,
        xy3BranchWeight (⟨q, i⟩ : XY3Branch B) * xy3BranchIntegral β shift ⟨q, i⟩) =
        fun q => assignmentCoefficient rootActivity q * xy3AssignmentInner β shift q := by
      funext q
      exact (hf q).tsum_eq
    rw [hEq]
    exact hg.summable
  exact HasSum.sigma_of_hasSum hg hf hsummable

end FroehlichSpencer.FS82.XY

end
