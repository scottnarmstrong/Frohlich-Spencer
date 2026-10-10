/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Rotator.CurrentIntegration
public import FroehlichSpencer.BKT.Rotator.FreeBoxBijection
public import FroehlichSpencer.BKT.Villain.CurrentFormula
public import FroehlichSpencer.BKT.Villain.CosineExpectation

/-! # Free-box Villain currents as pinned Gaussian heights

The finite free-square Villain Fourier expansion is indexed by neutral currents and by currents
with a prescribed endpoint source. The existing planar current/height equivalence identifies these
sums with the zero-exterior pinned-height partition sum and its marked version.
-/

@[expose] public section

open Complex MeasureTheory
open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Rotator
open FroehlichSpencer.BKT.Villain

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
    _ = ∑' a : {a // P a}, f a.1 :=
      (tsum_subtype {a | P a} f).symm

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

/-- The two current constraints in the free-box Villain character formula: divergence `+1` at
the observed site and `−1` at the pinned root. -/
def freeBoxEndpointCharge {L : ℕ} (root site : RotatorSpinSite L)
    (v : RotatorSpinSite L) : ℤ :=
  if v = site then 1 else if v = root then -1 else 0

private theorem characterCurrent_iff_freeBoxEndpointCharge {L : ℕ}
    (root site : RotatorSpinSite L) (hne : site ≠ root)
    (q : RotatorInternalBond L → ℤ) :
    characterCurrent (rotatorFreeGraph L) root site q ↔
      ∀ v, currentDivergence (rotatorFreeGraph L) q v =
        freeBoxEndpointCharge root site v := by
  constructor
  · intro h v
    by_cases hv : v = root
    · subst v
      have hr := characterCurrent_root_divergence (rotatorFreeGraph L) root site q h hne
      simp [freeBoxEndpointCharge, hne.symm] at hr ⊢
      exact hr
    · have hv' := h v hv
      simp [freeBoxEndpointCharge, hv, hv']
  · intro h v hv
    have hv' := h v
    simpa [freeBoxEndpointCharge, hv, hne] using hv'

/-- Reindex the root-pinned neutral-current filter as the subtype of currents neutral at every
free-box vertex. -/
private def freeBoxNeutralCurrentEquiv {L : ℕ} (root : RotatorSpinSite L) :
    RotatorNeutralCurrents (rotatorFreeGraph L) ≃
      {q : RotatorInternalBond L → ℤ // neutralAwayFrom (rotatorFreeGraph L) root q} where
  toFun q := ⟨q.1, fun v hv => q.2 v⟩
  invFun q := ⟨q.1,
    (neutralAwayFrom_iff_all_divergences_zero (rotatorFreeGraph L) root q.1).mp q.2⟩
  left_inv q := by cases q; rfl
  right_inv q := by cases q; rfl

/-- Reindex the root-pinned source-current filter as the subtype with the endpoint divergence
specified by `freeBoxEndpointCharge`. -/
private def freeBoxSourceCurrentEquiv {L : ℕ} (root site : RotatorSpinSite L)
    (hne : site ≠ root) :
    RotatorSourceCurrents (rotatorFreeGraph L) (freeBoxEndpointCharge root site) ≃
      {q : RotatorInternalBond L → ℤ // characterCurrent (rotatorFreeGraph L) root site q} where
  toFun q := ⟨q.1,
    (characterCurrent_iff_freeBoxEndpointCharge root site hne q.1).mpr q.2⟩
  invFun q := ⟨q.1,
    (characterCurrent_iff_freeBoxEndpointCharge root site hne q.1).mp q.2⟩
  left_inv q := by cases q; rfl
  right_inv q := by cases q; rfl

/-- The Gaussian edge weight of a zero-exterior integer height in the free box. -/
def gaussianVillainHeightWeight (L : ℕ) (β : ℝ) (h : RotatorFaceHeight L) : ℝ :=
  currentGaussianWeight β (rotatorFaceHeightCurrent h)

/-- The Gaussian height weight with a fixed integer source current inserted. -/
def gaussianVillainMarkedHeightWeight (L : ℕ) (β : ℝ)
    (j : RotatorInternalBond L → ℤ) (h : RotatorFaceHeight L) : ℝ :=
  currentGaussianWeight β (fun e => rotatorFaceHeightCurrent h e + j e)

/-- The free-box Villain partition sum is exactly the sum over zero-exterior pinned integer
heights, with Gaussian edge weights. -/
theorem neutralFreeBoxVillainCurrent_tsum_eq_height (L : ℕ) (β : ℝ) :
    (∑' q : RotatorNeutralCurrents (rotatorFreeGraph L), currentGaussianWeight β q.1) =
      ∑' h : RotatorFaceHeight L, gaussianVillainHeightWeight L β h := by
  classical
  let e := rotatorNeutralCurrentHeightEquiv L
  calc
    (∑' q : RotatorNeutralCurrents (rotatorFreeGraph L),
      currentGaussianWeight β q.1) =
        ∑' h : RotatorFaceHeight L, currentGaussianWeight β (e.symm h).1 :=
      (Equiv.tsum_eq e.symm
        (fun q : RotatorNeutralCurrents (rotatorFreeGraph L) =>
          currentGaussianWeight β q.1)).symm
    _ = ∑' h : RotatorFaceHeight L, gaussianVillainHeightWeight L β h := by
      apply tsum_congr
      intro h
      rfl

/-- A prescribed source-current sum is the pinned-height sum with that current added to every
height gradient. This is the marked half of finite free-box Villain duality. -/
theorem sourceFreeBoxVillainCurrent_tsum_eq_markedHeight
    (L : ℕ) (β : ℝ) (χ : RotatorSpinSite L → ℤ)
    (j : RotatorInternalBond L → ℤ)
    (hj : ∀ v, currentDivergence (rotatorFreeGraph L) j v = χ v) :
    (∑' q : RotatorSourceCurrents (rotatorFreeGraph L) χ,
      currentGaussianWeight β q.1) =
      ∑' h : RotatorFaceHeight L, gaussianVillainMarkedHeightWeight L β j h := by
  classical
  let e : RotatorFaceHeight L ≃ RotatorSourceCurrents (rotatorFreeGraph L) χ :=
    (rotatorNeutralCurrentHeightEquiv L).symm.trans
      (rotatorCurrentShiftEquiv (rotatorFreeGraph L) χ j hj)
  calc
    (∑' q : RotatorSourceCurrents (rotatorFreeGraph L) χ,
        currentGaussianWeight β q.1) =
        ∑' h : RotatorFaceHeight L, currentGaussianWeight β (e h).1 :=
      (Equiv.tsum_eq e (fun q : RotatorSourceCurrents (rotatorFreeGraph L) χ =>
        currentGaussianWeight β q.1)).symm
    _ = ∑' h : RotatorFaceHeight L, gaussianVillainMarkedHeightWeight L β j h := by
      apply tsum_congr
      intro h
      change currentGaussianWeight β (rotatorFaceHeightCurrent h + j) = _
      rfl

/-- **Finite free-box Villain duality, normalized character form.** The root-pinned Villain
character expectation on the free square is the ratio of the pinned Gaussian height sum with the
source current inserted to its unmarked partition sum. -/
theorem villainCharacterExpectation_eq_gaussianHeightRatio {L : ℕ}
    (β : ℝ) (hβ : 0 < β) (root site : RotatorSpinSite L) (hne : site ≠ root)
    (j : RotatorInternalBond L → ℤ)
    (hj : ∀ v, currentDivergence (rotatorFreeGraph L) j v =
      freeBoxEndpointCharge root site v) :
    villainCharacterExpectation (rotatorFreeGraph L) root β ⟨site, hne⟩ =
      (∑' h : RotatorFaceHeight L, gaussianVillainMarkedHeightWeight L β j h) /
        (∑' h : RotatorFaceHeight L, gaussianVillainHeightWeight L β h) := by
  classical
  have hden :
      (∑' q : RotatorInternalBond L → ℤ,
        neutralCurrentGaussianWeight (rotatorFreeGraph L) root β q) =
      ∑' q : RotatorNeutralCurrents (rotatorFreeGraph L),
        currentGaussianWeight β q.1 := by
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
      _ = ∑' q : RotatorNeutralCurrents (rotatorFreeGraph L),
          currentGaussianWeight β q.1 := by
        apply tsum_congr
        intro q
        rfl
  have hnum :
      (∑' q : RotatorInternalBond L → ℤ,
        sourceCurrentGaussianWeight (rotatorFreeGraph L) root site β q) =
      ∑' q : RotatorSourceCurrents (rotatorFreeGraph L)
        (freeBoxEndpointCharge root site), currentGaussianWeight β q.1 := by
    unfold sourceCurrentGaussianWeight
    rw [tsum_if_eq_subtype]
    let e := freeBoxSourceCurrentEquiv (L := L) root site hne
    calc
      (∑' q : {q : RotatorInternalBond L → ℤ //
          characterCurrent (rotatorFreeGraph L) root site q}, currentGaussianWeight β q.1) =
        ∑' q : RotatorSourceCurrents (rotatorFreeGraph L)
          (freeBoxEndpointCharge root site), currentGaussianWeight β (e q).1 :=
          (Equiv.tsum_eq e (fun q : {q : RotatorInternalBond L → ℤ //
            characterCurrent (rotatorFreeGraph L) root site q} => currentGaussianWeight β q.1)).symm
      _ = ∑' q : RotatorSourceCurrents (rotatorFreeGraph L)
          (freeBoxEndpointCharge root site), currentGaussianWeight β q.1 := by
        apply tsum_congr
        intro q
        rfl
  calc
    villainCharacterExpectation (rotatorFreeGraph L) root β ⟨site, hne⟩ =
        (∑' q : RotatorInternalBond L → ℤ,
          sourceCurrentGaussianWeight (rotatorFreeGraph L) root site β q) /
        (∑' q : RotatorInternalBond L → ℤ,
          neutralCurrentGaussianWeight (rotatorFreeGraph L) root β q) :=
      villainCharacterExpectation_eq_real_current_ratio
        (rotatorFreeGraph L) root β hβ ⟨site, hne⟩
    _ = _ := by
      rw [hnum, hden,
        sourceFreeBoxVillainCurrent_tsum_eq_markedHeight L β
          (freeBoxEndpointCharge root site) j hj,
        neutralFreeBoxVillainCurrent_tsum_eq_height]

end FroehlichSpencer.BKT.Villain.TheoremC

end
