/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Villain.TheoremC.CurrentHeight
public import FroehlichSpencer.BKT.Villain.TheoremC.Frequency

/-! # Arbitrary Villain harmonics as Gaussian height ratios -/

@[expose] public section

open Complex
open FroehlichSpencer.BKT.Rotator
open FroehlichSpencer.BKT.Villain
open FroehlichSpencer.BKT.Villain.TheoremC

noncomputable section

namespace FroehlichSpencer.BKT.Villain.TheoremC

private theorem tsum_if_eq_subtype {α : Type*} (P : α → Prop) [DecidablePred P]
    (f : α → ℝ) :
    (∑' a, if P a then f a else 0) = ∑' a : {a // P a}, f a.1 := by
  classical
  calc
    (∑' a, if P a then f a else 0) =
        ∑' a, ({a | P a} : Set α).indicator f a := by
      apply tsum_congr
      intro a
      by_cases ha : P a <;> simp [Set.indicator, ha]
    _ = ∑' a : {a // P a}, f a.1 := (tsum_subtype {a | P a} f).symm

private theorem neutralAwayFrom_iff_all_divergences_zero
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : Multigraph V E) (root : V) (q : E → ℤ) :
    neutralAwayFrom G root q ↔ ∀ v, currentDivergence G q v = 0 := by
  constructor
  · intro h v
    by_cases hv : v = root
    · subst v
      have hsum := sum_currentDivergence_eq_zero G q
      rw [← Finset.add_sum_erase (s := Finset.univ)
        (f := currentDivergence G q) (Finset.mem_univ root)] at hsum
      have hrest : ∑ w ∈ Finset.univ.erase root, currentDivergence G q w = 0 := by
        apply Finset.sum_eq_zero
        intro w hw
        exact h w (Finset.ne_of_mem_erase hw)
      rw [hrest, add_zero] at hsum
      exact hsum
    · exact h v hv
  · intro h v hv
    exact h v

private theorem currentDivergence_eq_of_offRoot
    {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : Multigraph V E) (root : V) (q : E → ℤ) (χ : V → ℤ)
    (hχ : ∑ v, χ v = 0)
    (hoff : ∀ v, v ≠ root → currentDivergence G q v = χ v) :
    ∀ v, currentDivergence G q v = χ v := by
  intro v
  by_cases hv : v = root
  · subst v
    have hdiv := sum_currentDivergence_eq_zero G q
    rw [← Finset.add_sum_erase (s := Finset.univ)
      (f := currentDivergence G q) (Finset.mem_univ root)] at hdiv
    have hχsum := hχ
    rw [← Finset.add_sum_erase (s := Finset.univ) (f := χ) (Finset.mem_univ root)] at hχsum
    have hrest : ∑ w ∈ Finset.univ.erase root, currentDivergence G q w =
        ∑ w ∈ Finset.univ.erase root, χ w := by
      apply Finset.sum_congr rfl
      intro w hw
      exact hoff w (Finset.ne_of_mem_erase hw)
    rw [hrest] at hdiv
    omega
  · exact hoff v hv

private theorem villainFrequencyCurrent_iff_endpointCharge {L : ℕ}
    (root site : RotatorSpinSite L) (hne : site ≠ root) (ξ : ℤ)
    (q : RotatorInternalBond L → ℤ) :
    villainFrequencyCurrent (rotatorFreeGraph L) root ⟨site, hne⟩ ξ q ↔
      ∀ v, currentDivergence (rotatorFreeGraph L) q v =
        ξ * freeBoxEndpointCharge root site v := by
  classical
  have hχsum : ∑ v : RotatorSpinSite L, ξ * freeBoxEndpointCharge root site v = 0 := by
    rw [← Finset.mul_sum]
    have hpoint (v : RotatorSpinSite L) :
        freeBoxEndpointCharge root site v =
          (if v = site then 1 else 0) - (if v = root then 1 else 0) := by
      unfold freeBoxEndpointCharge
      by_cases hs : v = site
      · subst v
        simp [hne]
      · by_cases hr : v = root
        · subst v
          simp [hne.symm]
        · simp [hs, hr]
    simp_rw [hpoint, Finset.sum_sub_distrib]
    simp
  constructor
  · intro h
    apply currentDivergence_eq_of_offRoot (rotatorFreeGraph L) root q
      (fun v => ξ * freeBoxEndpointCharge root site v) hχsum
    intro v hv
    by_cases hs : v = site
    · subst v
      simpa [freeBoxEndpointCharge] using h site hv
    · simpa [freeBoxEndpointCharge, hv, hs] using h v hv
  · intro h v hv
    have hv' := h v
    by_cases hs : v = site
    · subst v
      simpa [freeBoxEndpointCharge, hne] using hv'
    · simpa [freeBoxEndpointCharge, hv, hs] using hv'

private def freeBoxNeutralCurrentEquiv {L : ℕ} (root : RotatorSpinSite L) :
    RotatorNeutralCurrents (rotatorFreeGraph L) ≃
      {q : RotatorInternalBond L → ℤ // neutralAwayFrom (rotatorFreeGraph L) root q} where
  toFun q := ⟨q.1, fun v hv => q.2 v⟩
  invFun q := ⟨q.1,
    (neutralAwayFrom_iff_all_divergences_zero (rotatorFreeGraph L) root q.1).mp q.2⟩
  left_inv q := by cases q; rfl
  right_inv q := by cases q; rfl

/-- The root-pinned neutral-current sum is the sum over all neutral free-box currents. -/
theorem neutralCurrentGaussianWeight_tsum_eq_rotatorNeutralCurrents {L : ℕ}
    (root : RotatorSpinSite L) (β : ℝ) :
    (∑' q : RotatorInternalBond L → ℤ,
      neutralCurrentGaussianWeight (rotatorFreeGraph L) root β q) =
      ∑' q : RotatorNeutralCurrents (rotatorFreeGraph L), currentGaussianWeight β q.1 := by
  classical
  unfold neutralCurrentGaussianWeight
  rw [tsum_if_eq_subtype]
  let e := freeBoxNeutralCurrentEquiv (L := L) root
  calc
    (∑' q : {q : RotatorInternalBond L → ℤ //
        neutralAwayFrom (rotatorFreeGraph L) root q}, currentGaussianWeight β q.1) =
      ∑' q : RotatorNeutralCurrents (rotatorFreeGraph L), currentGaussianWeight β (e q).1 :=
        (Equiv.tsum_eq e (fun q : {q : RotatorInternalBond L → ℤ //
          neutralAwayFrom (rotatorFreeGraph L) root q} => currentGaussianWeight β q.1)).symm
    _ = _ := by
      apply tsum_congr
      intro q
      rfl

/-- The unmarked pinned Gaussian height partition sum is strictly positive. -/
theorem gaussianVillainHeightPartitionSum_pos {L : ℕ} {β : ℝ} (hβ : 0 < β) :
    0 < ∑' h : RotatorFaceHeight L, gaussianVillainHeightWeight L β h := by
  classical
  let root : RotatorSpinSite L := ⟨⟨0, by omega⟩, ⟨0, by omega⟩⟩
  rw [← neutralFreeBoxVillainCurrent_tsum_eq_height L β]
  rw [← neutralCurrentGaussianWeight_tsum_eq_rotatorNeutralCurrents root β]
  exact neutralCurrentGaussianWeight_tsum_pos (rotatorFreeGraph L) root β hβ

private def freeBoxFrequencyCurrentEquiv {L : ℕ} (root site : RotatorSpinSite L)
    (hne : site ≠ root) (ξ : ℤ) :
    RotatorSourceCurrents (rotatorFreeGraph L)
        (fun v => ξ * freeBoxEndpointCharge root site v) ≃
      {q : RotatorInternalBond L → ℤ //
        villainFrequencyCurrent (rotatorFreeGraph L) root ⟨site, hne⟩ ξ q} where
  toFun q := ⟨q.1,
    (villainFrequencyCurrent_iff_endpointCharge root site hne ξ q.1).mpr q.2⟩
  invFun q := ⟨q.1,
    (villainFrequencyCurrent_iff_endpointCharge root site hne ξ q.1).mp q.2⟩
  left_inv q := by cases q; rfl
  right_inv q := by cases q; rfl

/-- The rooted Villain character expectation at every integer frequency is the ratio of the pinned
Gaussian height sum marked by `ξ` times an endpoint current and the unmarked height partition sum.
The mark `j` has unit endpoint divergence. -/
theorem villainFrequencyCharacterExpectation_eq_gaussianHeightRatio {L : ℕ}
    (β : ℝ) (hβ : 0 < β) (root site : RotatorSpinSite L) (hne : site ≠ root)
    (ξ : ℤ) (j : RotatorInternalBond L → ℤ)
    (hj : ∀ v, currentDivergence (rotatorFreeGraph L) j v =
      freeBoxEndpointCharge root site v) :
    villainFrequencyCharacterExpectation (rotatorFreeGraph L) root β ⟨site, hne⟩ ξ =
      (∑' h : RotatorFaceHeight L,
        gaussianVillainMarkedHeightWeight L β (fun e => ξ * j e) h) /
        (∑' h : RotatorFaceHeight L, gaussianVillainHeightWeight L β h) := by
  classical
  have hscaled (v : RotatorSpinSite L) :
      currentDivergence (rotatorFreeGraph L) (fun e => ξ * j e) v =
        ξ * freeBoxEndpointCharge root site v := by
    have hmul : currentDivergence (rotatorFreeGraph L) (fun e => ξ * j e) v =
        ξ * currentDivergence (rotatorFreeGraph L) j v := by
      unfold currentDivergence
      rw [mul_sub, Finset.mul_sum, Finset.mul_sum]
      congr 1 <;> refine Finset.sum_congr rfl fun e _ => ?_ <;> split_ifs <;> simp
    rw [hmul, hj v]
  have hden :
      (∑' q : RotatorInternalBond L → ℤ,
        neutralCurrentGaussianWeight (rotatorFreeGraph L) root β q) =
      ∑' q : RotatorNeutralCurrents (rotatorFreeGraph L), currentGaussianWeight β q.1 := by
    unfold neutralCurrentGaussianWeight
    rw [tsum_if_eq_subtype]
    let e := freeBoxNeutralCurrentEquiv (L := L) root
    calc
      (∑' q : {q : RotatorInternalBond L → ℤ //
          neutralAwayFrom (rotatorFreeGraph L) root q}, currentGaussianWeight β q.1) =
        ∑' q : RotatorNeutralCurrents (rotatorFreeGraph L),
          currentGaussianWeight β (e q).1 :=
          (Equiv.tsum_eq e (fun q : {q : RotatorInternalBond L → ℤ //
            neutralAwayFrom (rotatorFreeGraph L) root q} => currentGaussianWeight β q.1)).symm
      _ = _ := by
        apply tsum_congr
        intro q
        rfl
  have hnum :
      (∑' q : RotatorInternalBond L → ℤ,
        villainFrequencyCurrentGaussianWeight (rotatorFreeGraph L) root
          ⟨site, hne⟩ β ξ q) =
      ∑' q : RotatorSourceCurrents (rotatorFreeGraph L)
        (fun v => ξ * freeBoxEndpointCharge root site v), currentGaussianWeight β q.1 := by
    unfold villainFrequencyCurrentGaussianWeight
    rw [tsum_if_eq_subtype]
    let e := freeBoxFrequencyCurrentEquiv root site hne ξ
    calc
      (∑' q : {q : RotatorInternalBond L → ℤ //
          villainFrequencyCurrent (rotatorFreeGraph L) root ⟨site, hne⟩ ξ q},
          currentGaussianWeight β q.1) =
        ∑' q : RotatorSourceCurrents (rotatorFreeGraph L)
          (fun v => ξ * freeBoxEndpointCharge root site v), currentGaussianWeight β (e q).1 :=
          (Equiv.tsum_eq e (fun q : {q : RotatorInternalBond L → ℤ //
            villainFrequencyCurrent (rotatorFreeGraph L) root ⟨site, hne⟩ ξ q} =>
              currentGaussianWeight β q.1)).symm
      _ = _ := by
        apply tsum_congr
        intro q
        rfl
  calc
    villainFrequencyCharacterExpectation (rotatorFreeGraph L) root β ⟨site, hne⟩ ξ =
        ((∑' q : RotatorInternalBond L → ℤ,
          villainFrequencyCurrentGaussianWeight (rotatorFreeGraph L) root
            ⟨site, hne⟩ β ξ q) /
          (∑' q : RotatorInternalBond L → ℤ,
            neutralCurrentGaussianWeight (rotatorFreeGraph L) root β q) : ℂ) :=
      villainFrequencyCharacterExpectation_eq_realCurrentRatio
        (rotatorFreeGraph L) root β hβ ⟨site, hne⟩ ξ
    _ = _ := by
      rw [hnum, hden,
        sourceFreeBoxVillainCurrent_tsum_eq_markedHeight L β
          (fun v => ξ * freeBoxEndpointCharge root site v) (fun e => ξ * j e) hscaled,
        neutralFreeBoxVillainCurrent_tsum_eq_height]

end FroehlichSpencer.BKT.Villain.TheoremC

end
