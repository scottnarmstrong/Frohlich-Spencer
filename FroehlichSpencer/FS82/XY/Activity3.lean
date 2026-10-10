/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.XY.Mixture3
public import FroehlichSpencer.FS82.XY.Neighbour3
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# the renormalized activities in three dimensions

The six-colour block carries at
least one sixth of `‖ϱ‖²` and every link has at most four plaquettes, so the renormalization
gains `e^{−(π²β/12) ‖ϱ‖²}`.

Therefore, for `β ≥ 400/3`,

`amp(ϱ) ≤ exp(−(3β/8 − 50)(‖ϱ‖² + L(ϱ)))`,

which is FS82 (4.37).

In particular every renormalized amplitude is below one.
-/

open scoped BigOperators

@[expose] public section

namespace FroehlichSpencer.FS82.XY

open FroehlichSpencer.FS82.Gaussian.ConditionalGaussian
open FroehlichSpencer.FS82.Poisson
open FroehlichSpencer.FS82.Root
open FroehlichSpencer.FS82.Currents
open FroehlichSpencer.FS82.XY.Renormalization3
open FroehlichSpencer.FS82.XY.GaugeAverage

variable {B : Dual3Box}

/-- The squared `ℓ²` norm of an integer dual-link current. -/
noncomputable def currentEnergy3 (j : Dual3Links B → ℤ) : ℝ :=
  ∑ e ∈ currentSupport j, ((j e : ℤ) : ℝ) ^ 2

/-- The number of links of an integer dual-link current. -/
noncomputable def currentLength3 (j : Dual3Links B → ℤ) : ℕ := (currentSupport j).card

theorem currentEnergy3_nonneg (j : Dual3Links B → ℤ) : 0 ≤ currentEnergy3 j :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem one_le_sq_of_mem_currentSupport {j : Dual3Links B → ℤ} {e : Dual3Links B}
    (he : e ∈ currentSupport j) : (1 : ℝ) ≤ ((j e : ℤ) : ℝ) ^ 2 := by
  have hne : j e ≠ 0 := (Finset.mem_filter.mp he).2
  have h1 : (1 : ℤ) ≤ (j e) ^ 2 := by
    have := sq_nonneg (j e)
    have hpos : 0 < (j e) ^ 2 := by positivity
    omega
  exact_mod_cast h1

theorem currentLength3_le_energy (j : Dual3Links B → ℤ) :
    (currentLength3 j : ℝ) ≤ currentEnergy3 j := by
  unfold currentLength3 currentEnergy3
  calc ((currentSupport j).card : ℝ) = ∑ _e ∈ currentSupport j, (1 : ℝ) := by simp
    _ ≤ ∑ e ∈ currentSupport j, ((j e : ℤ) : ℝ) ^ 2 :=
      Finset.sum_le_sum fun e he => one_le_sq_of_mem_currentSupport he

/-- The activity rate of FS82 (4.37) in three dimensions. -/
noncomputable def xy3ActivityRate (β : ℝ) : ℝ := 3 * β / 8 - 50

/-! ## The renormalization gain -/

theorem exp_neg_familyGain_le {ι : Type*} [Fintype ι] [DecidableEq ι] {β : ℝ} (hβ : 0 ≤ β)
    (J : ι → Dual3Links B → ℤ) (i : ι) :
    Real.exp (-(familyGain β J i / 2)) ≤ Real.exp (-(3 * β / 4 * currentEnergy3 (J i))) := by
  classical
  set ρ : ι → Dual3Links B → ℝ := fun i e => (J i e : ℝ) with hρ
  have hsupp : familyCurrentSupport ρ i = currentSupport (J i) := familyCurrentSupport_intCast J i
  have h48 := selectedLinkEnergy_at_least_one48 (familyCurrentSupport ρ i)
    (selectedFamilyBlock ρ i) ((2 * Real.pi) ^ 2 * β) (ρ i) incidentPlaquetteCount
    (by positivity) (fun b _ => incidentPlaquetteCount_pos b)
    (fun b _ => incidentPlaquetteCount_le_four b) (selectedFamilyBlock_mass_captures ρ i)
  have hgain : familyGain β J i / 2 = (2 * Real.pi) ^ 2 * β / 2 *
      ∑ b ∈ selectedFamilyBlock ρ i, ρ i b ^ 2 / (incidentPlaquetteCount b : ℝ) := by
    unfold familyGain
    simp_rw [linkMass_dual3ChartIncidence_eq_incidentPlaquetteCount]
    ring
  rw [hgain]
  refine h48.trans (Real.exp_le_exp.mpr ?_)
  rw [hsupp]
  have hE : ∑ b ∈ currentSupport (J i), ρ i b ^ 2 = currentEnergy3 (J i) := rfl
  rw [hE]
  have hE0 := currentEnergy3_nonneg (J i)
  have hpi : (9 : ℝ) ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
  have hcoef : 3 * β / 4 ≤ (2 * Real.pi) ^ 2 * β / 48 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right hcoef hE0]

/-! ## The lineage coefficient -/

theorem three_le_exp : (3 : ℝ) ≤ Real.exp (6 / 5) := by
  have h1 : (2.7 : ℝ) ≤ Real.exp 1 := by
    have := Real.exp_one_gt_d9
    linarith
  have h2 : (6 / 5 : ℝ) ≤ Real.exp (1 / 5) := by
    have := Real.add_one_le_exp (1 / 5 : ℝ)
    linarith
  have h3 : Real.exp (6 / 5) = Real.exp 1 * Real.exp (1 / 5) := by
    rw [← Real.exp_add]
    norm_num
  rw [h3]
  nlinarith [Real.exp_pos (1 : ℝ), Real.exp_pos (1 / 5 : ℝ)]

theorem two_le_exp : (2 : ℝ) ≤ Real.exp 1 := by
  have := Real.add_one_le_exp (1 : ℝ)
  linarith

theorem integerActivity_rootActivity_le {n : ℤ} (hn : n ≠ 0) :
    integerActivity rootActivity |n| ≤ Real.exp (2 * ((n : ℤ) : ℝ) ^ 2) := by
  have hpos : 0 < |n| := abs_pos.mpr hn
  simp only [integerActivity, hpos, ↓reduceIte, rootActivity]
  have h2 := two_le_exp
  have hm : (|n|.toNat : ℝ) + 1 ≤ 2 * ((n : ℤ) : ℝ) ^ 2 := by
    have hcast : ((|n|.toNat : ℕ) : ℝ) = |(n : ℝ)| := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (abs_nonneg n), Int.cast_abs]
    rw [hcast]
    have h1 : (1 : ℝ) ≤ |(n : ℝ)| := by
      have : (1 : ℤ) ≤ |n| := hpos
      exact_mod_cast this
    have hsq : |(n : ℝ)| ^ 2 = (n : ℝ) ^ 2 := sq_abs _
    nlinarith
  calc (2 : ℝ) ^ (|n|.toNat + 1) ≤ Real.exp 1 ^ (|n|.toNat + 1) :=
        pow_le_pow_left₀ (by norm_num) h2 _
    _ = Real.exp ((|n|.toNat : ℝ) + 1) := by
        rw [← Real.exp_nat_mul]
        congr 1
        push_cast
        ring
    _ ≤ Real.exp (2 * ((n : ℤ) : ℝ) ^ 2) := Real.exp_le_exp.mpr hm

/-- The coefficient of a lineage of a branch is at most `exp(100 ‖ϱ‖²)`. -/
theorem xy3Branch_lineageCoefficient_le (ω : XY3Branch B) {l : Expansion3.ExpansionLineage B}
    (hl : l ∈ xy3BranchState ω) :
    Expansion3.lineageCoefficient (xy3BranchFrequency ω) (integerActivity rootActivity) l ≤
      Real.exp (100 * currentEnergy3 (Expansion3.lineageCurrent (xy3BranchFrequency ω) l)) := by
  set J := Expansion3.lineageCurrent (xy3BranchFrequency ω) l with hJ
  have hspec := (xy3Terms_spec ω.1).2.2.2.2.2.2.2 _ (xy3BranchTerm_mem ω) l hl
  have hN := card_activityNeighborhood_le (B := B) (currentSupport J)
  have hLE := currentLength3_le_energy J
  have hE0 := currentEnergy3_nonneg J
  have h3 : (3 : ℝ) ^ (ActivityLineage.activityNeighborhood Finset.univ
      (currentSupport J) Expansion3.currentNear).card ≤
      Real.exp (486 / 5 * currentEnergy3 J) := by
    calc (3 : ℝ) ^ (ActivityLineage.activityNeighborhood Finset.univ
          (currentSupport J) Expansion3.currentNear).card
        ≤ (3 : ℝ) ^ (81 * (currentSupport J).card) :=
          pow_le_pow_right₀ (by norm_num) hN
      _ ≤ Real.exp (6 / 5) ^ (81 * (currentSupport J).card) :=
          pow_le_pow_left₀ (by norm_num) three_le_exp _
      _ = Real.exp (486 / 5 * (currentLength3 J : ℝ)) := by
          rw [← Real.exp_nat_mul]
          congr 1
          unfold currentLength3
          push_cast
          ring
      _ ≤ Real.exp (486 / 5 * currentEnergy3 J) :=
          Real.exp_le_exp.mpr (by nlinarith)
  have hz : ∏ e ∈ currentSupport J, integerActivity rootActivity |J e| ≤
      Real.exp (2 * currentEnergy3 J) := by
    calc ∏ e ∈ currentSupport J, integerActivity rootActivity |J e|
        ≤ ∏ e ∈ currentSupport J, Real.exp (2 * ((J e : ℤ) : ℝ) ^ 2) :=
          Finset.prod_le_prod₀
            (fun e _ => integerActivity_nonneg (fun n => (rootActivity_pos n).le) _)
            (fun e he => integerActivity_rootActivity_le (Finset.mem_filter.mp he).2)
      _ = Real.exp (2 * currentEnergy3 J) := by
          rw [← Real.exp_sum]
          congr 1
          unfold currentEnergy3
          rw [Finset.mul_sum]
  have h3pos : (0 : ℝ) ≤ (3 : ℝ) ^ (ActivityLineage.activityNeighborhood Finset.univ
      (currentSupport J) Expansion3.currentNear).card := by positivity
  have hzpos : 0 ≤ ∏ e ∈ currentSupport J, integerActivity rootActivity |J e| :=
    Finset.prod_nonneg fun e _ => integerActivity_nonneg (fun n => (rootActivity_pos n).le) _
  calc Expansion3.lineageCoefficient (xy3BranchFrequency ω) (integerActivity rootActivity) l
      ≤ (3 : ℝ) ^ (ActivityLineage.activityNeighborhood Finset.univ
          (currentSupport J) Expansion3.currentNear).card *
          ∏ e ∈ currentSupport J, integerActivity rootActivity |J e| := hspec
    _ ≤ Real.exp (486 / 5 * currentEnergy3 J) * Real.exp (2 * currentEnergy3 J) :=
        mul_le_mul h3 hz hzpos (Real.exp_pos _).le
    _ = Real.exp (486 / 5 * currentEnergy3 J + 2 * currentEnergy3 J) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (100 * currentEnergy3 J) := Real.exp_le_exp.mpr (by nlinarith)

/-! ## The envelope -/

/-- **The renormalized amplitude envelope, FS82 (4.37).** -/
theorem xy3BranchAmp_le {β : ℝ} (hβ : 400 / 3 ≤ β) (ω : XY3Branch B) (i : XY3BranchIndex ω) :
    xy3BranchAmp β ω i ≤
      Real.exp (-(xy3ActivityRate β * (currentEnergy3 (xy3BranchCurrent ω i) +
        (currentLength3 (xy3BranchCurrent ω i) : ℝ)))) := by
  have hβ0 : 0 ≤ β := by linarith
  unfold xy3BranchAmp stateAmp familyAmp stateActivity
  by_cases hcl : RootedTreeGauge.CoClosed (xyDual3RootedTree B)
      (Expansion3.lineageCurrent (xy3BranchFrequency ω) i.1)
  · have hcur : xy3BranchCurrent ω i =
        Expansion3.lineageCurrent (xy3BranchFrequency ω) i.1 := closedCurrent_of_coClosed hcl
    rw [closedActivity_of_coClosed _ hcl]
    have hK := xy3Branch_lineageCoefficient_le ω i.2
    have hG := exp_neg_familyGain_le hβ0
      (stateCurrent (xy3BranchFrequency ω) (xy3BranchState ω)) i
    change Real.exp (-(familyGain β (stateCurrent (xy3BranchFrequency ω) (xy3BranchState ω)) i
      / 2)) ≤ Real.exp (-(3 * β / 4 * currentEnergy3 (xy3BranchCurrent ω i))) at hG
    rw [← hcur] at hK
    set En := currentEnergy3 (xy3BranchCurrent ω i) with hEn
    have hLE : (currentLength3 (xy3BranchCurrent ω i) : ℝ) ≤ En := currentLength3_le_energy _
    have hE0 : 0 ≤ En := currentEnergy3_nonneg _
    calc Expansion3.lineageCoefficient (xy3BranchFrequency ω) (integerActivity rootActivity) i.1 *
          Real.exp (-(familyGain β (stateCurrent (xy3BranchFrequency ω) (xy3BranchState ω)) i
            / 2))
        ≤ Real.exp (100 * En) * Real.exp (-(3 * β / 4 * En)) :=
          mul_le_mul hK hG (Real.exp_pos _).le (Real.exp_pos _).le
      _ = Real.exp (100 * En + -(3 * β / 4 * En)) := (Real.exp_add _ _).symm
      _ ≤ Real.exp (-(xy3ActivityRate β *
            (En + (currentLength3 (xy3BranchCurrent ω i) : ℝ)))) := by
          apply Real.exp_le_exp.mpr
          unfold xy3ActivityRate
          nlinarith
  · rw [closedActivity_of_not_coClosed _ hcl, zero_mul]
    exact (Real.exp_pos _).le

theorem active_nonempty {Cell : Type*} [DecidableEq Cell] (h : ActivityLineage Cell) :
    h.active.Nonempty := by
  induction h with
  | leaf e => exact ⟨e, by simp [ActivityLineage.active]⟩
  | add l r ihl _ | sub l r ihl _ =>
      obtain ⟨x, hx⟩ := ihl
      exact ⟨x, by simp [ActivityLineage.active, hx]⟩
  | keepLeft l r ihl _ => simpa [ActivityLineage.active] using ihl
  | keepRight l r _ ihr => simpa [ActivityLineage.active] using ihr

/-- The current of a lineage of a branch is nonzero somewhere. -/
theorem xy3Branch_lineageCurrent_length_pos (ω : XY3Branch B) {l : Expansion3.ExpansionLineage B}
    (hl : l ∈ xy3BranchState ω) :
    0 < currentLength3 (Expansion3.lineageCurrent (xy3BranchFrequency ω) l) := by
  obtain ⟨hgood, hq⟩ := ((xy3Terms_spec ω.1).2.2.1 _ (xy3BranchTerm_mem ω)).1 l hl
  unfold currentLength3 Expansion3.lineageCurrent
  rw [ActivityLineage.currentSupport_value_eq_active hgood _ hq]
  exact Finset.card_pos.mpr (active_nonempty l)

/-- **Every renormalized amplitude is below one** for `β > 400/3`. -/
theorem xy3BranchAmp_lt_one {β : ℝ} (hβ : 400 / 3 < β) (ω : XY3Branch B)
    (i : XY3BranchIndex ω) : xy3BranchAmp β ω i < 1 := by
  by_cases hcl : RootedTreeGauge.CoClosed (xyDual3RootedTree B)
      (Expansion3.lineageCurrent (xy3BranchFrequency ω) i.1)
  · have hcur : xy3BranchCurrent ω i =
        Expansion3.lineageCurrent (xy3BranchFrequency ω) i.1 := closedCurrent_of_coClosed hcl
    refine lt_of_le_of_lt (xy3BranchAmp_le hβ.le ω i) ?_
    rw [← Real.exp_zero]
    apply Real.exp_lt_exp.mpr
    have hL : (1 : ℝ) ≤ (currentLength3 (xy3BranchCurrent ω i) : ℝ) := by
      rw [hcur]
      exact_mod_cast xy3Branch_lineageCurrent_length_pos ω i.2
    have hE0 := currentEnergy3_nonneg (xy3BranchCurrent ω i)
    have hrate : 0 < xy3ActivityRate β := by
      unfold xy3ActivityRate
      linarith
    nlinarith
  · unfold xy3BranchAmp stateAmp familyAmp stateActivity
    rw [closedActivity_of_not_coClosed _ hcl, zero_mul]
    exact zero_lt_one

end FroehlichSpencer.FS82.XY

end
