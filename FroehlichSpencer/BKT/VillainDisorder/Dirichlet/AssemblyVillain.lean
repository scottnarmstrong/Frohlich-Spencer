/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.VillainDisorder.Dirichlet.AssemblyFejer
public import FroehlichSpencer.BKT.VillainDisorder.ShiftedVillain
public import FroehlichSpencer.BKT.Villain.TheoremC.FrequencyHeight
import Mathlib.Tactic

/-! # Finite free-box disorder duality for the centered Dirichlet carrier

The root-pinned free-box Villain expectation is the expectation of the FS81 shifted-bond ratio
(1.32). The current expansion (1.38), the planar current/height bijection, and the carrier's
explicit Fourier normalization identify it with the (1.35) dipole cosine expectation.
-/

@[expose] public section

open MeasureTheory
open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Duality
open FroehlichSpencer.BKT.Generic.PinnedCharges
open FroehlichSpencer.BKT.Rotator
open FroehlichSpencer.BKT.Villain
open FroehlichSpencer.BKT.Villain.TheoremC
open FroehlichSpencer.BKT.VillainDisorder.Dirichlet

noncomputable section

namespace FroehlichSpencer.BKT.VillainDisorder.Dirichlet
/-- The zero-exterior height carrier reindexed as the dual faces of the free primal box. -/
def dirichletStringEdge (R n : ℕ) (_hn : n ≤ R) (k : Fin n) :
    RotatorInternalBond (sideLength R) :=
  .inr (verticalDualEdgeData
    ⟨R + min (k.val + 1) R, by simp [sideLength]; omega⟩
    ⟨R, by simp [sideLength]; omega⟩)

def dirichletStringShift (R n : ℕ) (hn : n ≤ R) (ξ : ℝ)
    (e : RotatorInternalBond (sideLength R)) : ℝ :=
  ∑ k : Fin n, if e = dirichletStringEdge R n hn k then 2 * Real.pi * ξ else 0

theorem sum_current_mul_dirichletStringShift (R n : ℕ) (hn : n ≤ R) (ξ : ℝ)
    (q : RotatorInternalBond (sideLength R) → ℤ) :
    (∑ e, (q e : ℝ) * dirichletStringShift R n hn ξ e) =
      2 * Real.pi * ξ * ∑ k : Fin n, (q (dirichletStringEdge R n hn k) : ℝ) := by
  classical
  unfold dirichletStringShift
  calc
    (∑ e, (q e : ℝ) * ∑ k : Fin n,
        if e = dirichletStringEdge R n hn k then 2 * Real.pi * ξ else 0) =
        ∑ e, ∑ k : Fin n,
          (q e : ℝ) * (if e = dirichletStringEdge R n hn k then 2 * Real.pi * ξ else 0) := by
            apply Finset.sum_congr rfl
            intro e he
            rw [Finset.mul_sum]
    _ = ∑ k : Fin n, ∑ e,
          (q e : ℝ) * (if e = dirichletStringEdge R n hn k then 2 * Real.pi * ξ else 0) := by
            rw [Finset.sum_comm]
    _ = ∑ k : Fin n, (q (dirichletStringEdge R n hn k) : ℝ) * (2 * Real.pi * ξ) := by
            apply Finset.sum_congr rfl
            intro k hk
            simp
    _ = 2 * Real.pi * ξ * ∑ k : Fin n,
          (q (dirichletStringEdge R n hn k) : ℝ) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k hk
            ring

theorem dirichletStringEdge_current (R n : ℕ) (hn : n ≤ R) (h : Height R)
    (k : Fin n) :
    rotatorFaceHeightCurrent (toRotatorHeight R h) (dirichletStringEdge R n hn k) =
      h.1 (some (⟨R + k.val, by simp [sideLength]; omega⟩, ⟨R, by simp [sideLength]; omega⟩)) -
        h.1 (some (⟨R + k.val + 1, by simp [sideLength]; omega⟩,
          ⟨R, by simp [sideLength]; omega⟩)) := by
  have hkR : k.val < R := lt_of_lt_of_le k.isLt hn
  let i : Fin (sideLength R + 1) :=
    ⟨R + min (k.val + 1) R, by simp [sideLength]; omega⟩
  let j : Fin (sideLength R) := ⟨R, by simp [sideLength]; omega⟩
  have hmin : min (k.val + 1) R = k.val + 1 := Nat.min_eq_left (by omega)
  have hright : R + (k.val + 1) ≤ 2 * R := by omega
  have hlt : R + (k.val + 1) < sideLength R := by simp [sideLength]; omega
  rw [show dirichletStringEdge R n hn k = .inr (verticalDualEdgeData i j) by rfl]
  rw [rotatorFaceHeightCurrent_vertical]
  simp [i, j, hmin, hlt, toRotatorHeight]
  apply congrArg (fun p : Site R => h.1 (some p))
  apply Prod.ext
  · apply Fin.ext
    exact (Nat.add_assoc R k.val 1).symm
  · rfl

def dirichletPathHeight (R : ℕ) (h : Height R) (k : ℕ) : ℤ :=
  h.1 (some (axialSite R (min k R) (Nat.min_le_right k R)))

def dirichletStringEdgeNat (R k : ℕ) : RotatorInternalBond (sideLength R) :=
  .inr (verticalDualEdgeData
    ⟨R + min (k + 1) R, by simp [sideLength]; omega⟩
    ⟨R, by simp [sideLength]; omega⟩)

theorem dirichletStringEdgeNat_current (R : ℕ) (h : Height R) (k : ℕ)
    (hk : k < R) :
    rotatorFaceHeightCurrent (toRotatorHeight R h) (dirichletStringEdgeNat R k) =
      dirichletPathHeight R h k - dirichletPathHeight R h (k + 1) := by
  let i : Fin (sideLength R + 1) :=
    ⟨R + min (k + 1) R, by simp [sideLength]; omega⟩
  let j : Fin (sideLength R) := ⟨R, by simp [sideLength]; omega⟩
  have hmin : min (k + 1) R = k + 1 := Nat.min_eq_left (by omega)
  have hmin' : min k R = k := Nat.min_eq_left (by omega)
  rw [show dirichletStringEdgeNat R k = .inr (verticalDualEdgeData i j) by rfl]
  rw [rotatorFaceHeightCurrent_vertical]
  have hright : R + (k + 1) ≤ 2 * R := by omega
  simp [i, j, dirichletPathHeight, axialSite, sideLength,
    hmin, hmin', hright, toRotatorHeight]
  rfl

theorem dirichletStringCurrent_sum_eq_endpointDifference
    (R n : ℕ) (hn : n ≤ R) (h : Height R) :
    (∑ k : Fin n,
      rotatorFaceHeightCurrent (toRotatorHeight R h) (dirichletStringEdge R n hn k)) =
      h.1 (some (center R)) - h.1 (some (axialSite R n hn)) := by
  classical
  have hterms :
      (∑ k : Fin n,
        rotatorFaceHeightCurrent (toRotatorHeight R h) (dirichletStringEdge R n hn k)) =
      ∑ k : Fin n,
        (dirichletPathHeight R h k.val - dirichletPathHeight R h (k.val + 1)) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hkR : k.val < R := lt_of_lt_of_le k.isLt hn
    have hedges : dirichletStringEdge R n hn k = dirichletStringEdgeNat R k.val := by
      rfl
    rw [hedges]
    exact dirichletStringEdgeNat_current R h k.val hkR
  rw [hterms, Fin.sum_univ_eq_sum_range
    (fun k => dirichletPathHeight R h k - dirichletPathHeight R h (k + 1)) n,
    Finset.sum_range_sub']
  simp [dirichletPathHeight, axialSite, center, sideLength,
    Nat.min_eq_left (show n ≤ R by exact hn)]

end FroehlichSpencer.BKT.VillainDisorder.Dirichlet

namespace FroehlichSpencer.BKT.VillainDisorder.Dirichlet

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

private def dirichletNeutralCurrentEquiv {L : ℕ}
    (root : RotatorSpinSite L) :
    {q : RotatorInternalBond L → ℤ //
      neutralAwayFrom (rotatorFreeGraph L) root q} ≃
      RotatorNeutralCurrents (rotatorFreeGraph L) where
  toFun q := ⟨q.1,
    (neutralAwayFrom_iff_all_divergences_zero (rotatorFreeGraph L) root q.1).mp q.2⟩
  invFun q := ⟨q.1,
    (neutralAwayFrom_iff_all_divergences_zero (rotatorFreeGraph L) root q.1).mpr q.2⟩
  left_inv q := by cases q; rfl
  right_inv q := by cases q; rfl

def dirichletRoot (R : ℕ) : RotatorSpinSite (sideLength R) :=
  ⟨⟨0, by simp [sideLength]⟩, ⟨0, by simp [sideLength]⟩⟩

def dirichletCurrentPhase (R n : ℕ) (hn : n ≤ R) (ξ : ℝ)
    (q : RotatorInternalBond (sideLength R) → ℤ) : ℝ :=
  ∑ e, (q e : ℝ) * dirichletStringShift R n hn ξ e

def dirichletRotatorHeightEquiv (R : ℕ) :
    Height R ≃ RotatorFaceHeight (sideLength R) where
  toFun := toRotatorHeight R
  invFun h := ⟨h.1, h.2⟩
  left_inv h := by cases h; rfl
  right_inv h := by cases h; rfl

theorem dirichletCurrentCosineTsum_eq_height (R n : ℕ) (hn : n ≤ R)
    (β ξ : ℝ) (root : RotatorSpinSite (sideLength R)) :
    (∑' q : RotatorInternalBond (sideLength R) → ℤ,
      neutralCurrentGaussianWeight (rotatorFreeGraph (sideLength R)) root β q *
        Real.cos (dirichletCurrentPhase R n hn ξ q)) =
    ∑' h : Height R,
      gaussianVillainHeightWeight (sideLength R) β (toRotatorHeight R h) *
        dipoleCosine R n hn ξ h := by
  classical
  let G := rotatorFreeGraph (sideLength R)
  let L := sideLength R
  simp_rw [neutralCurrentGaussianWeight, ite_mul, zero_mul]
  rw [tsum_if_eq_subtype]
  let e₀ := dirichletNeutralCurrentEquiv (L := L) root
  have hneutral :
      (∑' q : {q : RotatorInternalBond L → ℤ // neutralAwayFrom G root q},
        currentGaussianWeight β q.1 *
          Real.cos (dirichletCurrentPhase R n hn ξ q.1)) =
      ∑' q : RotatorNeutralCurrents G,
        currentGaussianWeight β q.1 *
          Real.cos (dirichletCurrentPhase R n hn ξ q.1) := by
    exact (Equiv.tsum_eq e₀ (fun q : RotatorNeutralCurrents G =>
      currentGaussianWeight β q.1 *
        Real.cos (dirichletCurrentPhase R n hn ξ q.1)))
  rw [hneutral]
  let e₁ := rotatorNeutralCurrentHeightEquiv L
  have hheight :
      (∑' q : RotatorNeutralCurrents G,
        currentGaussianWeight β q.1 *
          Real.cos (dirichletCurrentPhase R n hn ξ q.1)) =
      ∑' h : RotatorFaceHeight L,
        gaussianVillainHeightWeight L β h *
          Real.cos (dirichletCurrentPhase R n hn ξ (rotatorFaceHeightCurrent h)) := by
    change (∑' q : RotatorNeutralCurrent L,
      currentGaussianWeight β q.1 * Real.cos (dirichletCurrentPhase R n hn ξ q.1)) = _
    calc
      (∑' q : RotatorNeutralCurrent L,
        currentGaussianWeight β q.1 * Real.cos (dirichletCurrentPhase R n hn ξ q.1)) =
          ∑' q : RotatorNeutralCurrent L,
            gaussianVillainHeightWeight L β (e₁ q) *
              Real.cos (dirichletCurrentPhase R n hn ξ
                (rotatorFaceHeightCurrent (e₁ q))) := by
          apply tsum_congr
          intro q
          have hcurrent : rotatorFaceHeightCurrent (e₁ q) = q.1 := by
            change rotatorFaceHeightCurrent (rotatorHeightFromCurrent q.1) = q.1
            exact rotatorHeightFromCurrent_current q.1 q.2
          rw [gaussianVillainHeightWeight, hcurrent]
      _ = ∑' h : RotatorFaceHeight L,
            gaussianVillainHeightWeight L β h *
              Real.cos (dirichletCurrentPhase R n hn ξ (rotatorFaceHeightCurrent h)) :=
          Equiv.tsum_eq e₁ (fun h : RotatorFaceHeight L =>
            gaussianVillainHeightWeight L β h *
              Real.cos (dirichletCurrentPhase R n hn ξ (rotatorFaceHeightCurrent h)))
  rw [hheight]
  let e₂ := dirichletRotatorHeightEquiv R
  rw [show (∑' h : RotatorFaceHeight L,
      gaussianVillainHeightWeight L β h *
        Real.cos (dirichletCurrentPhase R n hn ξ (rotatorFaceHeightCurrent h))) =
      ∑' h : Height R,
        gaussianVillainHeightWeight L β (toRotatorHeight R h) *
          Real.cos (dirichletCurrentPhase R n hn ξ
            (rotatorFaceHeightCurrent (toRotatorHeight R h))) from
      (Equiv.tsum_eq e₂ (fun h : RotatorFaceHeight L =>
        gaussianVillainHeightWeight L β h *
          Real.cos (dirichletCurrentPhase R n hn ξ (rotatorFaceHeightCurrent h)))).symm]
  apply tsum_congr
  intro h
  congr 1
  have hshift := sum_current_mul_dirichletStringShift R n hn ξ
    (rotatorFaceHeightCurrent (toRotatorHeight R h))
  have hpath := dirichletStringCurrent_sum_eq_endpointDifference R n hn h
  have hphase : dirichletCurrentPhase R n hn ξ
      (rotatorFaceHeightCurrent (toRotatorHeight R h)) =
      2 * Real.pi * ξ *
        (((h.1 (some (center R)) - h.1 (some (axialSite R n hn)) : ℤ) : ℝ)) := by
    unfold dirichletCurrentPhase
    rw [hshift]
    rw [← hpath]
    push_cast
    ring
  rw [hphase]
  unfold dipoleCosine
  rfl

/-- The unmarked current partition sum is the zero-exterior Gaussian height partition sum. -/
theorem dirichletCurrentGaussianTsum_eq_height (R n : ℕ) (hn : n ≤ R)
    (β : ℝ) (root : RotatorSpinSite (sideLength R)) :
    (∑' q : RotatorInternalBond (sideLength R) → ℤ,
      neutralCurrentGaussianWeight (rotatorFreeGraph (sideLength R)) root β q) =
    ∑' h : Height R,
      gaussianVillainHeightWeight (sideLength R) β (toRotatorHeight R h) := by
  have h := dirichletCurrentCosineTsum_eq_height R n hn β 0 root
  simpa [dirichletCurrentPhase, dirichletStringShift, dipoleCosine] using h

end FroehlichSpencer.BKT.VillainDisorder.Dirichlet

namespace FroehlichSpencer.BKT.VillainDisorder.Dirichlet

private theorem summable_dirichletGaussianHeightWeight {R : ℕ} {β : ℝ}
    (hR : 1 ≤ R) (hβ : 0 < β) :
    Summable (fun h : Height R =>
      gaussianVillainHeightWeight (sideLength R) β (toRotatorHeight R h)) := by
  let C := fourierConstant β ^ Fintype.card (SquareZeroBond (sideLength R))
  have hC : 0 < C := pow_pos (fourierConstant_pos hβ) _
  have hpoint : ∀ h : Height R,
      gaussianVillainHeightWeight (sideLength R) β (toRotatorHeight R h) =
        C⁻¹ * heightWeight R β h := by
    intro h
    have hh := heightWeight_eq_constant_mul_gaussianVillainHeightWeight hβ h
    have hh' : heightWeight R β h = C *
        gaussianVillainHeightWeight (sideLength R) β (toRotatorHeight R h) := by
      simpa [C] using hh
    rw [hh']
    field_simp [ne_of_gt hC]
  rw [show (fun h : Height R =>
      gaussianVillainHeightWeight (sideLength R) β (toRotatorHeight R h)) =
      fun h => C⁻¹ * heightWeight R β h from by
        funext h
        exact hpoint h]
  exact (summable_heightWeight hR hβ).mul_left _

private theorem summable_dirichletMarkedGaussianHeightWeight {R n : ℕ}
    (hR : 1 ≤ R) (hn : n ≤ R) (β ξ : ℝ) (hβ : 0 < β) :
    Summable (fun h : Height R => dipoleCosine R n hn ξ h *
      gaussianVillainHeightWeight (sideLength R) β (toRotatorHeight R h)) := by
  have hbase := summable_dirichletGaussianHeightWeight hR hβ
  refine hbase.of_norm_bounded fun h => ?_
  have hw : 0 < gaussianVillainHeightWeight (sideLength R) β (toRotatorHeight R h) :=
    currentGaussianWeight_pos β (rotatorFaceHeightCurrent (toRotatorHeight R h))
  unfold dipoleCosine
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos hw]
  calc
    |Real.cos (2 * Real.pi * ξ *
        (((h.1 (some (center R)) - h.1 (some (axialSite R n hn)) : ℤ) : ℝ)))| *
        gaussianVillainHeightWeight (sideLength R) β (toRotatorHeight R h) ≤
        1 * gaussianVillainHeightWeight (sideLength R) β (toRotatorHeight R h) :=
      mul_le_mul_of_nonneg_right
        (Real.abs_cos_le_one _) hw.le
    _ = gaussianVillainHeightWeight (sideLength R) β (toRotatorHeight R h) := one_mul _

/-- The disorder expectation in the root-gauged free primal box, with the shifted bonds of
FS81 (1.32). -/
def dirichletFreeVillainDisorderExpectation (R n : ℕ) (hn : n ≤ R)
    (β ξ : ℝ) (hβ : 0 < β) : ℝ :=
  ∫ θ, villainShiftRatio (rotatorFreeGraph (sideLength R)) (dirichletRoot R) β
      (dirichletStringShift R n hn ξ) θ ∂
    rootedVillainMeasure (rotatorFreeGraph (sideLength R)) (dirichletRoot R) β hβ

/-- Exact finite free-box equality: the expectation of the twisted Villain bond ratio is the
normalized (1.35) zero-exterior dipole cosine expectation. -/
theorem dirichletFreeVillainDisorderExpectation_eq_cosineExpectation
    (R n : ℕ) (hR : 1 ≤ R) (hn : n ≤ R) (β ξ : ℝ) (hβ : 0 < β) :
    dirichletFreeVillainDisorderExpectation R n hn β ξ hβ =
      cosineExpectation R n hn β ξ := by
  let root := dirichletRoot R
  let C := fourierConstant β ^ Fintype.card (SquareZeroBond (sideLength R))
  have hC : 0 < C := pow_pos (fourierConstant_pos hβ) _
  have hgauss := summable_dirichletGaussianHeightWeight hR hβ
  have hmark := summable_dirichletMarkedGaussianHeightWeight hR hn β ξ hβ
  have hden :
      partitionFunction R β = C *
        ∑' h : Height R,
          gaussianVillainHeightWeight (sideLength R) β (toRotatorHeight R h) := by
    rw [partitionFunction]
    calc
      (∑' h : Height R, heightWeight R β h) =
          ∑' h : Height R, C *
            gaussianVillainHeightWeight (sideLength R) β (toRotatorHeight R h) := by
          apply tsum_congr
          intro h
          simpa [C] using (heightWeight_eq_constant_mul_gaussianVillainHeightWeight hβ h)
      _ = C * ∑' h : Height R,
          gaussianVillainHeightWeight (sideLength R) β (toRotatorHeight R h) :=
        hgauss.tsum_mul_left C
  have hnum :
      cosineNumerator R n hn β ξ = C *
        ∑' h : Height R,
          dipoleCosine R n hn ξ h *
            gaussianVillainHeightWeight (sideLength R) β (toRotatorHeight R h) := by
    rw [cosineNumerator]
    calc
      (∑' h : Height R, dipoleCosine R n hn ξ h * heightWeight R β h) =
          ∑' h : Height R, C * (dipoleCosine R n hn ξ h *
            gaussianVillainHeightWeight (sideLength R) β (toRotatorHeight R h)) := by
          apply tsum_congr
          intro h
          rw [heightWeight_eq_constant_mul_gaussianVillainHeightWeight hβ h]
          dsimp [C]
          ring
      _ = C * ∑' h : Height R,
          dipoleCosine R n hn ξ h *
            gaussianVillainHeightWeight (sideLength R) β (toRotatorHeight R h) :=
        hmark.tsum_mul_left C
  have hcurrent := integral_villainShiftRatio (rotatorFreeGraph (sideLength R)) root β hβ
    (dirichletStringShift R n hn ξ)
  have hcurrentNum := dirichletCurrentCosineTsum_eq_height R n hn β ξ root
  have hcurrentDen := dirichletCurrentGaussianTsum_eq_height R n hn β root
  have hmarkorder :
      (∑' h : Height R,
        gaussianVillainHeightWeight (sideLength R) β (toRotatorHeight R h) *
          dipoleCosine R n hn ξ h) =
      ∑' h : Height R,
        dipoleCosine R n hn ξ h *
          gaussianVillainHeightWeight (sideLength R) β (toRotatorHeight R h) := by
    apply tsum_congr
    intro h
    ring
  have hcurrentNum' := by
    simpa only [dirichletCurrentPhase] using hcurrentNum
  change (∫ θ, villainShiftRatio (rotatorFreeGraph (sideLength R)) root β
      (dirichletStringShift R n hn ξ) θ ∂rootedVillainMeasure
        (rotatorFreeGraph (sideLength R)) root β hβ) = _
  rw [hcurrent, hcurrentNum', hcurrentDen]
  unfold cosineExpectation
  rw [hnum, hden]
  rw [hmarkorder]
  field_simp [ne_of_gt hC]

end FroehlichSpencer.BKT.VillainDisorder.Dirichlet

namespace FroehlichSpencer.BKT.VillainDisorder.Dirichlet

/-- Every normalized cosine expectation under the positive carrier law lies in `[-1,1]`. This
provides boundedness of the centered exhaustion independently of the large-square estimate. -/
theorem cosineExpectation_mem_Icc_one {R n : ℕ} (hR : 1 ≤ R) (hn : n ≤ R)
    (β ξ : ℝ) (hβ : 0 < β) : cosineExpectation R n hn β ξ ∈ Set.Icc (-1) 1 := by
  have hweight := summable_heightWeight hR hβ
  have hmarked : Summable (fun h : Height R =>
      dipoleCosine R n hn ξ h * heightWeight R β h) := by
    refine hweight.of_norm_bounded fun h => ?_
    have hw := heightWeight_pos hβ h
    unfold dipoleCosine
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hw]
    calc
      |Real.cos (2 * Real.pi * ξ *
          (((h.1 (some (center R)) - h.1 (some (axialSite R n hn)) : ℤ) : ℝ)))| *
          heightWeight R β h ≤ 1 * heightWeight R β h :=
        mul_le_mul_of_nonneg_right (Real.abs_cos_le_one _) hw.le
      _ = heightWeight R β h := one_mul _
  have hlowTerm (h : Height R) : -heightWeight R β h ≤
      dipoleCosine R n hn ξ h * heightWeight R β h := by
    have hw := heightWeight_pos hβ h
    have hc := Real.neg_one_le_cos (2 * Real.pi * ξ *
      (((h.1 (some (center R)) - h.1 (some (axialSite R n hn)) : ℤ) : ℝ)))
    unfold dipoleCosine
    calc
      -heightWeight R β h = (-1) * heightWeight R β h := by ring
      _ ≤ Real.cos (2 * Real.pi * ξ *
          (((h.1 (some (center R)) - h.1 (some (axialSite R n hn)) : ℤ) : ℝ))) *
          heightWeight R β h := mul_le_mul_of_nonneg_right hc hw.le
  have hhighTerm (h : Height R) : dipoleCosine R n hn ξ h * heightWeight R β h ≤
      heightWeight R β h := by
    have hw := heightWeight_pos hβ h
    have hc := Real.cos_le_one (2 * Real.pi * ξ *
      (((h.1 (some (center R)) - h.1 (some (axialSite R n hn)) : ℤ) : ℝ)))
    unfold dipoleCosine
    exact (mul_le_mul_of_nonneg_right hc hw.le).trans_eq (one_mul _)
  have hlow : -partitionFunction R β ≤ cosineNumerator R n hn β ξ := by
    rw [partitionFunction, cosineNumerator, ← tsum_neg]
    exact hweight.neg.tsum_le_tsum hlowTerm hmarked
  have hhigh : cosineNumerator R n hn β ξ ≤ partitionFunction R β := by
    simpa [partitionFunction, cosineNumerator] using
      hmarked.tsum_le_tsum hhighTerm hweight
  have hZ : 0 < partitionFunction R β := partitionFunction_pos hR hβ
  constructor
  · change -1 ≤ cosineExpectation R n hn β ξ
    unfold cosineExpectation
    rw [le_div_iff₀ hZ]
    simpa using hlow
  · change cosineExpectation R n hn β ξ ≤ 1
    unfold cosineExpectation
    rw [div_le_iff₀ hZ]
    simpa using hhigh

end FroehlichSpencer.BKT.VillainDisorder.Dirichlet
