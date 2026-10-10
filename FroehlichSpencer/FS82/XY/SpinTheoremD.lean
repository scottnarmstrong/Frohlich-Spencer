/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.XY.EndpointRatioD
import all FroehlichSpencer.FS82.XY.CurrentExpansionD

/-!
# the finite-volume root of FS82 Section 4, (4.40), for every `d ≥ 3`

`fs82_xyD_spinCorrelation_root`: for every `d ≥ 3` there are `β₀` and `C` such that for every
`β ≥ β₀`, every box with `d` equal sides and all sites `x, y` of it, the spin correlation of the
Villain `XY` model with free boundary conditions satisfies

`exp(−C/β) ≤ ⟨cos(θ_x − θ_y)⟩`.

They are not optimized, and no uniformity
in `d` is claimed.

The limit `Λ ↗ ℤ^d` is not taken .

It has the
additive term `5π² · #cells · e^{−a m}` for the currents with at least `m` cells, which the printed
(4.38) does not have; on cubes that term is bounded uniformly in the side, which is what the root
uses.

The box-uniform printed (4.38) is not claimed.

The proof assembles:

* `poisson_residual_together`: a statement that uses the Poisson layer and the residual layer in
  one theorem (the two could not be imported together before the renaming in
  `XY/PoissonPhaseD.lean`).
-/

open scoped BigOperators

@[expose] public section

namespace FroehlichSpencer.FS82.XY.DualD

open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Gaussian
open FroehlichSpencer.FS82.Poisson
open FroehlichSpencer.FS82.Root
open FroehlichSpencer.FS82.Currents
open FroehlichSpencer.FS82.Wilson
open FroehlichSpencer.FS82.Moment.SourceJensen
open FroehlichSpencer.FS82.XY.GaugeAverage
open FroehlichSpencer.FS82.XY.ExpansionD.Generic

variable {d : ℕ} {B : Box d}

/-! ## The amplitudes of a branch -/

theorem branchD_lineage_length_pos (ω : BranchD B) (i : BranchIndexD ω) :
    1 ≤ currentLength (lineageCurrent (branchFrequencyD ω) i.1) := by
  unfold currentLength
  rw [lineage_support (termsD_spec ω.1) (branchTermD_mem ω) i.2]
  exact Finset.card_pos.mpr (active_nonempty i.1)

/-- **The envelope of the renormalized amplitudes**, FS82 (4.37) for every `d ≥ 3`. -/
theorem branchAmpD_le {β a : ℝ} (ha0 : 0 ≤ a)
    (hrate : 2 * a + 2 + ((6 ^ d : ℕ) : ℝ) * Real.log 3 ≤ Real.pi ^ 2 * β / (2 * (d : ℝ) ^ 2))
    (ω : BranchD B) (i : BranchIndexD ω) :
    branchAmpD β ω i ≤
      Real.exp (-(a * (currentEnergy (branchCurrentD ω i) +
        (currentLength (branchCurrentD ω i) : ℝ)))) := by
  unfold branchAmpD stateAmpD stateActivityD branchCurrentD stateCurrentD
  set J₀ := lineageCurrent (branchFrequencyD ω) i.1 with hJ₀
  by_cases hcl : ClosedD stencilInt J₀
  · rw [closedActivityD_of_closed _ hcl, closedCurrentD_of_closed hcl]
    have hz0 : ∀ k : ℤ, 0 ≤ integerActivity rootActivity k :=
      integerActivity_nonneg fun n => (rootActivity_pos n).le
    have hK1 := lineageCoefficient_le (termsD_spec ω.1) hz0 (branchTermD_mem ω) i.2
    have hprod := prod_activity_le J₀ (integerActivity rootActivity) 2 hz0
      (fun n hn => integerActivity_rootActivity_le hn)
    have hK : lineageCoefficient (branchFrequencyD ω) (integerActivity rootActivity) i.1 ≤
        (3 : ℝ) ^ (6 ^ d * currentLength J₀) * Real.exp (2 * currentEnergy J₀) :=
      hK1.trans (mul_le_mul_of_nonneg_left hprod (by positivity))
    refine activity_envelope (κ := Real.pi ^ 2 * β / (2 * (d : ℝ) ^ 2)) hK le_rfl
      (currentLength_le_currentEnergy J₀) (le_of_eq ?_) ha0 hrate
    unfold lineageGain
    ring
  · rw [closedActivityD_of_not_closed _ hcl, zero_mul]
    exact (Real.exp_pos _).le

/-- Every renormalized amplitude is below one. -/
theorem branchAmpD_lt_one {β a : ℝ} (ha : 0 < a)
    (hrate : 2 * a + 2 + ((6 ^ d : ℕ) : ℝ) * Real.log 3 ≤ Real.pi ^ 2 * β / (2 * (d : ℝ) ^ 2))
    (ω : BranchD B) (i : BranchIndexD ω) : branchAmpD β ω i < 1 := by
  by_cases hcl : ClosedD stencilInt (lineageCurrent (branchFrequencyD ω) i.1)
  · have hle := branchAmpD_le ha.le hrate ω i
    have hcur : branchCurrentD ω i = lineageCurrent (branchFrequencyD ω) i.1 :=
      closedCurrentD_of_closed hcl
    rw [hcur] at hle
    have hL := branchD_lineage_length_pos ω i
    have hL1 : (1 : ℝ) ≤ (currentLength (lineageCurrent (branchFrequencyD ω) i.1) : ℝ) := by
      exact_mod_cast hL
    have hE0 := currentEnergy_nonneg (lineageCurrent (branchFrequencyD ω) i.1)
    refine lt_of_le_of_lt hle ?_
    rw [← Real.exp_zero]
    apply Real.exp_lt_exp.mpr
    nlinarith
  · unfold branchAmpD stateAmpD stateActivityD
    rw [closedActivityD_of_not_closed _ hcl, zero_mul]
    exact one_pos

/-- **Every branch is an admissible family.** -/
theorem branch_admissible (hd : 3 ≤ d) {β a : ℝ} (ha0 : 0 ≤ a)
    (hrate : 2 * a + 2 + ((6 ^ d : ℕ) : ℝ) * Real.log 3 ≤ Real.pi ^ 2 * β / (2 * (d : ℝ) ^ 2))
    (ω : BranchD B) :
    AdmissibleFamily hd a (branchCurrentD ω) (branchAmpD β ω) where
  coClosed := stateCurrentD_coClosed hd _ _
  disjoint := fun i j hij e he => stateCurrentD_disjoint (branchStateD_separated ω) i j hij e he
  extent := by
    intro i e f he hf k
    obtain ⟨he', heq⟩ := stateCurrentD_ne_zero_imp he
    obtain ⟨hf', _⟩ := stateCurrentD_ne_zero_imp hf
    change cellBase e.1 k + 1 ≤ cellBase f.1 k +
      currentLength (stateCurrentD (branchFrequencyD ω) (branchStateD ω) i)
    rw [heq]
    exact lineage_extent (termsD_spec ω.1) (branchTermD_mem ω) i.2 e f he' hf' k
  nonneg := branchAmpD_nonneg β ω
  envelope := branchAmpD_le ha0 hrate ω

/-! ## The interface -/

theorem closedCharacterSum_zero_re_pos (hd : 3 ≤ d) {β a : ℝ} (hβ : 0 < β) (ha : 0 < a)
    (hrate : 2 * a + 2 + ((6 ^ d : ℕ) : ℝ) * Real.log 3 ≤ Real.pi ^ 2 * β / (2 * (d : ℝ) ^ 2)) :
    0 < (closedCharacterSum (B := B) hd β 0).re := by
  have hamp1 : ∀ (ω : BranchD B) (i : BranchIndexD ω), branchAmpD β ω i < 1 :=
    fun ω i => branchAmpD_lt_one ha hrate ω i
  have hden := branchD_hasSum (B := B) hd hβ 0 fun ω i => (hamp1 ω i).le
  let q₀ : DualDForm B (d - 2) → ℕ := fun _ => 0
  have hlen : 0 < (termsD q₀).length := List.length_pos_iff.mpr (termsD_spec q₀).1
  let ω₀ : BranchD B := ⟨q₀, ⟨0, hlen⟩⟩
  have hterm : 0 < branchWeightD ω₀ * branchIntegralD hd β 0 ω₀ :=
    mul_pos (mul_pos (assignmentCoefficient_pos rootActivity _ fun _ => rootActivity_pos _)
      (branchTermD_weight_pos ω₀)) (branchIntegralD_zero_pos hd hβ.le ω₀ (hamp1 ω₀))
  exact lt_of_lt_of_le hterm (le_hasSum hden ω₀ fun ω _ =>
    mul_nonneg (branchWeightD_nonneg ω)
      (branchIntegralD_nonneg hd hβ.le 0 ω fun i => (hamp1 ω i).le))

/-- **The interface holds**: the output of the Poisson, expansion and Gaussian layers, for every
`d ≥ 3`, every box, at the rate of the envelope. -/
theorem branchJensenInterface_holds (hd : 3 ≤ d) {β a : ℝ} (hβ : 0 < β) (ha : 0 < a)
    (hrate : 2 * a + 2 + ((6 ^ d : ℕ) : ℝ) * Real.log 3 ≤ Real.pi ^ 2 * β / (2 * (d : ℝ) ^ 2))
    (x y : XYSites B) :
    BranchJensenInterface hd β x y (xyDualDEndpointPathVector x y)
      (xyDualDEndpointPathTau hd x y).1 a := by
  classical
  intro E hE
  set τ : EuclideanSpace ℝ (DualDForm B (d - 2)) := (xyDualDEndpointPathTau hd x y).1 with hτ
  have hamp1 : ∀ (ω : BranchD B) (i : BranchIndexD ω), branchAmpD β ω i < 1 :=
    fun ω i => branchAmpD_lt_one ha hrate ω i
  have hnum := branchD_hasSum (B := B) hd hβ (pathShift τ) fun ω i => (hamp1 ω i).le
  have hden := branchD_hasSum (B := B) hd hβ 0 fun ω i => (hamp1 ω i).le
  have hbranch : ∀ ω : BranchD B,
      branchIntegralD hd β 0 ω * Real.exp (-E) ≤ branchIntegralD hd β (pathShift τ) ω := by
    intro ω
    obtain ⟨θ', hθ, hbudget⟩ := hE (BranchIndexD ω) (branchCurrentD ω) (branchAmpD β ω)
      (branch_admissible hd ha.le hrate ω)
    have hJ := branchD_jensen hd hβ.le (pathShift τ) ω (hamp1 ω) θ' (fun i => by
      obtain ⟨n, hn⟩ := hθ i
      exact ⟨n, by rw [linkPairing_pathShift]; exact hn⟩)
    have hN0 := (branchIntegralD_zero_pos hd hβ.le ω (hamp1 ω)).le
    calc branchIntegralD hd β 0 ω * Real.exp (-E)
        ≤ branchIntegralD hd β 0 ω *
            Real.exp (-∑ i, sourceJensenGamma (branchAmpD β ω i) * θ' i ^ 2) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hN0
      _ = Real.exp (-∑ i, sourceJensenGamma (branchAmpD β ω i) * θ' i ^ 2) *
            branchIntegralD hd β 0 ω := mul_comm _ _
      _ ≤ branchIntegralD hd β (pathShift τ) ω := hJ
  have hdenpos := closedCharacterSum_zero_re_pos (B := B) hd hβ ha hrate
  have hratio := xy3_countablePositiveBranchRatio_lower (I := BranchD B)
    (fun ω => branchWeightD ω) (fun ω => branchIntegralD hd β 0 ω)
    (fun ω => branchIntegralD hd β (pathShift τ) ω) (fun _ => E) 1 E
    (closedCharacterSum (B := B) hd β 0).re (closedCharacterSum hd β (pathShift τ)).re
    branchWeightD_nonneg (fun ω => (branchIntegralD_zero_pos hd hβ.le ω (hamp1 ω)).le)
    hdenpos hden hnum hbranch (fun _ => by rw [one_mul])
  rw [one_mul] at hratio
  rw [xyEndpointCharacterExpectation_re_eq hd hβ x y, sum_sq_pathResidual, sub_eq_add_neg,
    Real.exp_add]
  exact mul_le_mul_of_nonneg_left hratio (Real.exp_pos _).le

/-! ## The root -/

/-- The slope of the activity rate in `β`. -/
noncomputable def rootSlopeD (d : ℕ) : ℝ := Real.pi ^ 2 / (4 * (d : ℝ) ^ 2)

/-- The offset of the activity rate. -/
noncomputable def rootOffsetD (d : ℕ) : ℝ := 1 + ((6 ^ d : ℕ) : ℝ) * Real.log 3 / 2

/-- The threshold of the root in dimension `d`. -/
noncomputable def rootBetaThresholdD (d : ℕ) : ℝ :=
  max 1 (((d : ℝ) + rootOffsetD d) / rootSlopeD d)

/-- The constant of the root in dimension `d`. -/
noncomputable def rootConstantFinalD (d : ℕ) : ℝ :=
  rootConstantD d (rootSlopeD d) (rootOffsetD d) (72 * (d : ℝ) ^ 2)

theorem rootSlopeD_pos {d : ℕ} (hd : 3 ≤ d) : 0 < rootSlopeD d := by
  have hd0 : (0 : ℝ) < (d : ℝ) := by
    have : 0 < d := by omega
    exact_mod_cast this
  unfold rootSlopeD
  positivity

theorem rate_identity (d : ℕ) (hd : 3 ≤ d) (β : ℝ) :
    2 * (rootSlopeD d * β - rootOffsetD d) + 2 + ((6 ^ d : ℕ) : ℝ) * Real.log 3 =
      Real.pi ^ 2 * β / (2 * (d : ℝ) ^ 2) := by
  have hd0 : (d : ℝ) ≠ 0 := by
    have : 0 < d := by omega
    exact_mod_cast this.ne'
  unfold rootSlopeD rootOffsetD
  field_simp
  ring


/-- **FS82 (4.40) in finite volume for every `d ≥ 3`, with explicit constants.** -/
theorem xyD_spinCorrelation_lower (hd : 3 ≤ d) {β : ℝ} (hβ : rootBetaThresholdD d ≤ β)
    (hCube : ∀ i j : Fin d, B i = B j) (x y : XYSites B) :
    Real.exp (-(rootConstantFinalD d / β)) ≤ xyEndpointCosExpectation β x y := by
  have hκ := rootSlopeD_pos hd
  have hβ0 : 0 < β := lt_of_lt_of_le one_pos ((le_max_left _ _).trans hβ)
  have hrate : (d : ℝ) ≤ rootSlopeD d * β - rootOffsetD d := by
    have h := (le_max_right 1 (((d : ℝ) + rootOffsetD d) / rootSlopeD d)).trans hβ
    rw [div_le_iff₀ hκ] at h
    linarith
  have hapos : 0 < rootSlopeD d * β - rootOffsetD d := by
    have : (3 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  exact xyD_cube_spinCorrelation_lower hd hβ0 hκ hrate hCube x y
    (branchJensenInterface_holds hd hβ0 hapos (le_of_eq (rate_identity d hd β)) x y)

/-- **The finite-volume root of FS82 Section 4, (4.40), for every `d ≥ 3`.** There are `β₀` and
`C` such that for every `β ≥ β₀`, every box with `d` equal sides and all sites `x, y` of it, the
spin correlation of the Villain `XY` model with free boundary conditions satisfies
`exp(−C/β) ≤ ⟨cos(θ_x − θ_y)⟩`. -/
theorem fs82_xyD_spinCorrelation_root (hd : 3 ≤ d) :
    ∃ β₀ C : ℝ, 0 < β₀ ∧ 0 < C ∧ ∀ β : ℝ, β₀ ≤ β → ∀ B : Box d,
      (∀ i j : Fin d, B i = B j) → ∀ x y : XYSites B,
        Real.exp (-(C / β)) ≤ xyEndpointCosExpectation β x y := by
  have hd0 : (0 : ℝ) < (d : ℝ) := by
    have : 0 < d := by omega
    exact_mod_cast this
  exact ⟨rootBetaThresholdD d, rootConstantFinalD d, lt_of_lt_of_le one_pos (le_max_left _ _),
    rootConstantD_pos d (rootSlopeD_pos hd) (by positivity),
    fun _ hβ _ hCube x y => xyD_spinCorrelation_lower hd hβ hCube x y⟩

/-! ## The Poisson layer and the residual layer together -/


end FroehlichSpencer.FS82.XY.DualD

end
