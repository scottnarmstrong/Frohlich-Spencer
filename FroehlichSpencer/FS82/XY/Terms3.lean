/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.XY.Branch3
public import FroehlichSpencer.FS82.XY.OuterAssignment3
public import FroehlichSpencer.FS82.Root.NormalizedActivity

/-!
# the terminal branches of the three-dimensional expansion

This file fixes
that list for the root activity `z_n = 2^(n+1)` and writes the per-assignment moment as the finite
sum of the weighted state integrals, FS82 (4.31)–(4.32):

`gaugeAssignmentMoment T A τ t z q = e^{π⟨w, A⁻¹w⟩} ∑_γ d_γ ∫ ∏_{ϱ ∈ γ} (1 + K(ϱ) cos(⟨ϱ, φ + s_w⟩))`.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

@[expose] public section

namespace FroehlichSpencer.FS82.XY

open FroehlichSpencer.FS82.Poisson
open FroehlichSpencer.FS82.Root
open FroehlichSpencer.FS82.XY.Expansion3
open FroehlichSpencer.FS82.XY.GaugeAverage

variable {B : Dual3Box}

/-! ## Integer frequencies and activities -/

/-- The integer frequency of a mode assignment. -/
def assignmentFrequency (q : Dual3Links B → ℕ) : Dual3Links B → ℤ :=
  fun e => ((q e + 1 : ℕ) : ℤ)

/-- An activity sequence indexed by the integers; it vanishes at nonpositive frequencies. -/
noncomputable def integerActivity (z : ℕ → ℝ) : ℤ → ℝ :=
  fun n => if 0 < n then z n.toNat else 0

theorem integerActivity_zero (z : ℕ → ℝ) : integerActivity z 0 = 0 := by
  simp [integerActivity]

theorem integerActivity_nonneg {z : ℕ → ℝ} (hz : ∀ n, 0 ≤ z n) (n : ℤ) :
    0 ≤ integerActivity z n := by
  unfold integerActivity
  split_ifs
  · exact hz _
  · exact le_rfl

theorem integerActivity_pos {z : ℕ → ℝ} (hz : ∀ n, 0 < z n) (n : ℤ) (hn : 0 < n) :
    0 < integerActivity z n := by
  simp only [integerActivity, hn, ↓reduceIte]
  exact hz _

theorem integerActivity_assignmentFrequency (z : ℕ → ℝ) (q : Dual3Links B → ℕ)
    (e : Dual3Links B) :
    integerActivity z (abs (assignmentFrequency q e)) = z (positiveMode (q e)) := by
  have hpos : (0 : ℤ) < ((q e + 1 : ℕ) : ℤ) := by exact_mod_cast Nat.succ_pos _
  unfold assignmentFrequency
  rw [abs_of_pos hpos]
  simp only [integerActivity, hpos, ↓reduceIte, Int.toNat_natCast, positiveMode]

theorem sourceCurrentProduct_assignment (z : ℕ → ℝ) (q : Dual3Links B → ℕ)
    (φ : Dual3Links B → ℝ) :
    Expansion3.sourceCurrentProduct (assignmentFrequency q) (integerActivity z) φ =
      ∏ e, (1 + z (positiveMode (q e)) * Real.cos (φ e * ((q e + 1 : ℕ) : ℝ))) := by
  unfold Expansion3.sourceCurrentProduct
  refine Finset.prod_congr rfl fun e _ => ?_
  rw [integerActivity_assignmentFrequency]
  simp [assignmentFrequency]

/-! ## The terminal branches -/

/-- The terminal states of the expansion of a mode assignment at the root activity. -/
noncomputable def xy3Terms (q : Dual3Links B → ℕ) : List (CurrentExpansionTerm B) :=
  Classical.choose (exists_fixedFrequencySeparatedCurrentExpansion_withLineageActivity
    (assignmentFrequency q) (integerActivity rootActivity) (integerActivity_zero _)
    (integerActivity_nonneg fun n => (rootActivity_pos n).le)
    (integerActivity_pos rootActivity_pos))

theorem xy3Terms_spec (q : Dual3Links B → ℕ) :
    IsFixedFrequencyCurrentExpansion (assignmentFrequency q) (integerActivity rootActivity)
      (xy3Terms q) :=
  (Classical.choose_spec (exists_fixedFrequencySeparatedCurrentExpansion_withLineageActivity
    (assignmentFrequency q) (integerActivity rootActivity) (integerActivity_zero _)
    (integerActivity_nonneg fun n => (rootActivity_pos n).le)
    (integerActivity_pos rootActivity_pos))).1

/-- The outer index: a mode assignment and a terminal state of its expansion. -/
abbrev XY3Branch (B : Dual3Box) := Σ q : Dual3Links B → ℕ, Fin (xy3Terms q).length

/-- The expansion term of a branch. -/
noncomputable def xy3BranchTerm (ω : XY3Branch B) : CurrentExpansionTerm B :=
  (xy3Terms ω.1).get ω.2

/-- The terminal state of a branch. -/
noncomputable abbrev xy3BranchState (ω : XY3Branch B) : CurrentState B := (xy3BranchTerm ω).state

/-- The integer frequency of a branch. -/
abbrev xy3BranchFrequency (ω : XY3Branch B) : Dual3Links B → ℤ := assignmentFrequency ω.1

theorem xy3BranchTerm_mem (ω : XY3Branch B) : xy3BranchTerm ω ∈ xy3Terms ω.1 :=
  List.get_mem _ _

theorem xy3BranchState_separated (ω : XY3Branch B) :
    IsSeparatedCurrentState (xy3BranchFrequency ω) (xy3BranchState ω) :=
  (xy3Terms_spec ω.1).2.1 _ (xy3BranchTerm_mem ω)

theorem xy3BranchWeight_pos (ω : XY3Branch B) : 0 < (xy3BranchTerm ω).weight :=
  (xy3Terms_spec ω.1).2.2.2.1 _ (xy3BranchTerm_mem ω)

theorem xy3Branch_lineageCoefficient_pos (ω : XY3Branch B) {l : ExpansionLineage B}
    (hl : l ∈ xy3BranchState ω) :
    0 < lineageCoefficient (xy3BranchFrequency ω) (integerActivity rootActivity) l :=
  (xy3Terms_spec ω.1).2.2.2.2.2.2.1 _ (xy3BranchTerm_mem ω) l hl

/-! ## The per-assignment moment as a finite sum of state integrals -/

theorem list_map_sum_eq_fin_sum {α γ : Type*} [AddCommMonoid γ] (l : List α) (f : α → γ) :
    (l.map f).sum = ∑ i : Fin l.length, f (l.get i) := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      rw [Fin.sum_univ_succ]
      simp only [List.get_cons_zero, List.get_cons_succ']
      rw [ih]

theorem integrable_currentStateProduct
    (A : Matrix (xyDual3RootedTree B).Chord (xyDual3RootedTree B).Chord ℝ)
    (q : Dual3Links B → ℤ) (z : ℤ → ℝ) (s : CurrentState B) (shift : Dual3Links B → ℝ) :
    Integrable (fun ω => Expansion3.currentStateProduct q z
      (fun e => gaugeField (xyDual3RootedTree B) ω e + shift e) s)
      (gaugeMeasure (xyDual3RootedTree B) A) := by
  refine Integrable.of_bound ?_ (∏ t ∈ s, (1 + |lineageCoefficient q z t|))
    (ae_of_all _ fun ω => ?_)
  · have hm : Measurable fun ω : EuclideanSpace ℝ (xyDual3RootedTree B).Chord ×
        (XYDual3GraphVertex B → ℝ) => Expansion3.currentStateProduct q z
          (fun e => gaugeField (xyDual3RootedTree B) ω e + shift e) s := by
      unfold Expansion3.currentStateProduct Expansion3.currentFactor Expansion3.currentPhase3
      refine Finset.measurable_prod _ fun t _ => ?_
      refine measurable_const.add (measurable_const.mul (Real.measurable_cos.comp ?_))
      exact Finset.measurable_sum _ fun e _ =>
        ((measurable_gaugeField_apply (xyDual3RootedTree B) e).add measurable_const).mul_const _
    exact hm.aestronglyMeasurable
  · unfold Expansion3.currentStateProduct Expansion3.currentFactor
    rw [Real.norm_eq_abs, Finset.abs_prod]
    refine Finset.prod_le_prod₀ (fun t _ => abs_nonneg _) fun t _ => ?_
    refine (abs_add_le _ _).trans ?_
    rw [abs_one, abs_mul]
    have hc := Real.abs_cos_le_one (Expansion3.currentPhase3
      (fun e => gaugeField (xyDual3RootedTree B) ω e + shift e) (lineageCurrent q t))
    nlinarith [abs_nonneg (lineageCoefficient q z t)]

/-- **The per-assignment moment as the weighted sum of the terminal state integrals.** -/
theorem gaugeAssignmentMoment_eq_branchSum {β : ℝ} (hβ : 0 < β)
    (τ : (xyDual3RootedTree B).Chord → ℝ) (t : ℝ) (q : Dual3Links B → ℕ) :
    gaugeAssignmentMoment (xyDual3RootedTree B) (xyDual3ChordMatrix (B := B) β) τ t
        rootActivity q =
      (tiltConstant (xyDual3RootedTree B) (xyDual3ChordMatrix (B := B) β)
          (tiltVector (xyDual3RootedTree B) τ t) : ℂ) *
        ((∑ i : Fin (xy3Terms q).length, ((xy3Terms q).get i).weight *
          stateIntegral β (assignmentFrequency q) (integerActivity rootActivity)
            ((xy3Terms q).get i).state
            (tiltShift (xyDual3RootedTree B) (xyDual3ChordMatrix (B := B) β)
              (tiltVector (xyDual3RootedTree B) τ t)) : ℝ) : ℂ) := by
  rw [gaugeAssignmentMoment_eq_integral (xyDual3RootedTree B) (xyDual3ChordMatrix_posDef hβ) τ t
    rootActivity q fun n => rootActivity_pos _]
  set A := xyDual3ChordMatrix (B := B) β with hAdef
  set shift := tiltShift (xyDual3RootedTree B) A (tiltVector (xyDual3RootedTree B) τ t)
    with hshift
  congr 2
  have hpt : ∀ ω : EuclideanSpace ℝ (xyDual3RootedTree B).Chord × (XYDual3GraphVertex B → ℝ),
      (∏ e, (1 + rootActivity (positiveMode (q e)) *
        Real.cos ((gaugeField (xyDual3RootedTree B) ω e + shift e) * ((q e + 1 : ℕ) : ℝ)))) =
      ∑ i : Fin (xy3Terms q).length, ((xy3Terms q).get i).weight *
        Expansion3.currentStateProduct (assignmentFrequency q) (integerActivity rootActivity)
          (fun e => gaugeField (xyDual3RootedTree B) ω e + shift e)
          ((xy3Terms q).get i).state := by
    intro ω
    rw [← sourceCurrentProduct_assignment rootActivity q
      (fun e => gaugeField (xyDual3RootedTree B) ω e + shift e),
      (xy3Terms_spec q).2.2.2.2.2.1, Expansion3.currentExpansionSum, list_map_sum_eq_fin_sum]
  simp_rw [hpt]
  rw [integral_finsetSum _ fun i _ =>
    (integrable_currentStateProduct A _ _ _ shift).const_mul _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_const_mul]
  rfl

end FroehlichSpencer.FS82.XY

end
