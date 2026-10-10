/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Clock.VillainClock.SelfDuality
public import FroehlichSpencer.BKT.Clock.VillainClock.Model
public import FroehlichSpencer.BKT.Clock.Compact.TwoPoint
import Mathlib.Tactic

/-!
# The wired dual Villain clock dominates the free one

The dual of the free spin square `rotatorFreeGraph (K + 1)` is the Villain clock on its faces,
which form the square `RotatorSpinSite K`, with the exterior face pinned to `0`. Pinning adds, for
each boundary face, Villain bonds to the fixed angle `0`. These are positive-definite single-site
factors, so by Ginibre's inequality the wired two-point function dominates the free one
(`integral_cos_pairGibbs_le` with the pairs `(w, w)` and `(w, 1)`). The free one is the Ginibre
Villain-clock model `VillainClock.model` on the square `squareBoxZ K`.

* `villainClockModel_twoPoint_squareBox`: the Villain-clock two-point function on `{0, …, K}²` as a
  ratio of finite sums;
* `dualEdgeFrequency`, `prod_freeDualWeight_eq`: the interior dual edges are the bonds of the face
  square;
* **`villainClockModel_twoPoint_le_dual`**: the free face two-point function is at most the wired
  dual two-point function of `DualPartition.lean`.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Clock.VillainClock

open MeasureTheory
open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Rotator
open FroehlichSpencer.BKT.Rotator.Ginibre
open FroehlichSpencer.BKT.Duality
open FroehlichSpencer.BKT.Lattice2D
open FroehlichSpencer.BKT.Ginibre
open FroehlichSpencer.BKT.Clock.Compact

/-! ### The Villain-clock model on the square `{0, …, K}²` -/

theorem villainClockModel_pairWeight_squareBox (N K : ℕ) (hN : 0 < N) {β : ℝ} (hβ : 0 < β)
    (θ : squareBoxZ K → ℝ) :
    pairWeight (bondFrequency (squareBoxZ K)) ((model N hN β hβ).bondWeight (squareBoxZ K)) θ =
      ∏ e : RotatorInternalBond K, villainWeight β
        (θ (squareBoxEquiv K ((rotatorFreeGraph K).src e)) -
          θ (squareBoxEquiv K ((rotatorFreeGraph K).tgt e))) := by
  classical
  have hpos : ∀ x, 0 < villainWeight β x := VillainWeight.villainWeight_pos hβ
  have hsum := sum_rotatorInternalBond_eq_sum_latticeStep K
    (fun y z => Real.log (villainWeight β (latticeAngle θ y - latticeAngle θ z)))
  simp only [latticeAngle_siteToZ, latticeAngle_coe] at hsum
  have hL : pairWeight (bondFrequency (squareBoxZ K)) ((model N hN β hβ).bondWeight (squareBoxZ K))
      θ = Real.exp (∑ b : ↥(squareBoxZ K) × ↥(squareBoxZ K),
        if LatticeStep (b.1 : ℤ × ℤ) (b.2 : ℤ × ℤ) then
          Real.log (villainWeight β (θ b.1 - θ b.2)) else 0) := by
    rw [pairWeight, Real.exp_sum]
    refine Fintype.prod_congr _ _ fun c => ?_
    rw [FreeModel.bondWeight, phase_bondFrequency]
    split_ifs
    · exact (Real.exp_log (hpos _)).symm
    · simp
  rw [hL, ← hsum, Real.exp_sum]
  refine Fintype.prod_congr _ _ fun e => ?_
  exact Real.exp_log (hpos _)

/-- **The Villain-clock two-point function on the square `{0, …, K}²`** as a ratio of finite sums
over the clock configurations of the free spin box. -/
theorem villainClockModel_twoPoint_squareBox (N K : ℕ) (hN : 0 < N) {β : ℝ} (hβ : 0 < β)
    (ξ : ℤ) (a b : RotatorSpinSite K) :
    (model N hN β hβ).twoPoint ξ (squareBoxZ K) (siteToZ a) (siteToZ b) =
      (∑ s : RotatorSpinSite K → Fin N,
          Real.cos (ξ * (clockAngles N s a - clockAngles N s b)) *
            configurationWeight (rotatorFreeGraph K) β N s) /
        ∑ s : RotatorSpinSite K → Fin N, configurationWeight (rotatorFreeGraph K) β N s := by
  classical
  have hν : (model N hN β hβ).ν = clockMeasure N := rfl
  rw [FreeModel.twoPoint, FreeModel.gibbs, integral_pairGibbs (model N hN β hβ).mass_ne_zero
    ((model N hN β hβ).isBondWeight_bondWeight (squareBoxZ K)), pairPartition, hν,
    integral_siteProduct_clockMeasure, integral_siteProduct_clockMeasure]
  have he' : ∀ (k : squareBoxZ K → Fin N) (p : RotatorSpinSite K),
      (Equiv.arrowCongr (squareBoxEquiv K).symm (Equiv.refl (Fin N))) k p =
        k (squareBoxEquiv K p) := fun k p => rfl
  congr 1
  · refine Fintype.sum_equiv (Equiv.arrowCongr (squareBoxEquiv K).symm (Equiv.refl (Fin N)))
      _ _ fun k => ?_
    rw [villainClockModel_pairWeight_squareBox]
    simp only [latticeAngle_siteToZ, configurationWeight, angleField, clockAngle, clockAngles, he']
  · refine Fintype.sum_equiv (Equiv.arrowCongr (squareBoxEquiv K).symm (Equiv.refl (Fin N)))
      _ _ fun k => ?_
    rw [villainClockModel_pairWeight_squareBox]
    simp only [configurationWeight, angleField, clockAngle, he']

/-! ### Dual edges on the face square -/

section DualEdges

variable {K : ℕ}

/-- A face angle field extended by `0` on the exterior face. -/
def faceExtAngle (θ : RotatorSpinSite K → ℝ) : RotatorDualFace (K + 1) → ℝ
  | none => 0
  | some v => θ v

/-- The frequency of the dual edge crossing a spin bond, as a vector on the faces; the pinned
exterior face is omitted. -/
def dualEdgeFrequency (e : RotatorInternalBond (K + 1)) : Frequency (RotatorSpinSite K) :=
  fun v => (if (rotatorDualGraph (K + 1)).src e = some v then 1 else 0) -
    (if (rotatorDualGraph (K + 1)).tgt e = some v then 1 else 0)

theorem sum_ite_some_mul {f : RotatorDualFace (K + 1)} (θ : RotatorSpinSite K → ℝ) :
    (∑ v : RotatorSpinSite K, if f = some v then θ v else 0) = faceExtAngle θ f := by
  classical
  cases f with
  | none => simp [faceExtAngle]
  | some w => simp [faceExtAngle]

theorem phase_dualEdgeFrequency (e : RotatorInternalBond (K + 1)) (θ : RotatorSpinSite K → ℝ) :
    phase (dualEdgeFrequency e) θ = faceExtAngle θ ((rotatorDualGraph (K + 1)).src e) -
      faceExtAngle θ ((rotatorDualGraph (K + 1)).tgt e) := by
  classical
  simp only [phase, dualEdgeFrequency, Int.cast_sub, Int.cast_ite, Int.cast_one, Int.cast_zero,
    sub_mul, ite_mul, one_mul, zero_mul, Finset.sum_sub_distrib, sum_ite_some_mul]

/-- A dual edge between two bounded faces. -/
def IsInteriorDualEdge (e : RotatorInternalBond (K + 1)) : Prop :=
  ((rotatorDualGraph (K + 1)).src e).isSome ∧ ((rotatorDualGraph (K + 1)).tgt e).isSome

instance (e : RotatorInternalBond (K + 1)) : Decidable (IsInteriorDualEdge e) := by
  unfold IsInteriorDualEdge
  infer_instance

/-- The free face weights: the Villain weight on interior dual edges and `1` on the edges to the
pinned exterior face. -/
def freeDualWeight (β : ℝ) (e : RotatorInternalBond (K + 1)) : ℝ → ℝ :=
  if IsInteriorDualEdge e then villainWeight β else fun _ => 1

/-- The interior dual edges are the bonds of the face square, with the same Villain factors. -/
theorem prod_freeDualWeight_eq (β : ℝ) (θ : RotatorSpinSite K → ℝ) :
    (∏ e : RotatorInternalBond (K + 1), freeDualWeight β e (phase (dualEdgeFrequency e) θ)) =
      ∏ e : RotatorInternalBond K, villainWeight β
        (θ ((rotatorFreeGraph K).src e) - θ ((rotatorFreeGraph K).tgt e)) := by
  classical
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type, mul_comm]
  congr 1
  · -- primal vertical bonds ↔ face horizontal bonds
    let ι : SquareFreeHorizontalEdge (K + 1) → SquareFreeVerticalEdge (K + 2) := fun q =>
      (⟨q.1.1.val + 1, by have := q.1.2; omega⟩,
        ⟨⟨q.2.val, by have := q.2.isLt; omega⟩, by have := q.2.isLt; simp; omega⟩)
    symm
    refine Finset.prod_of_injOn ι ?_ (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _)) ?_ ?_
    · intro q _ q' _ hqq'
      have h1 := congrArg (fun p : SquareFreeVerticalEdge (K + 2) => p.1.val) hqq'
      have h2 := congrArg (fun p : SquareFreeVerticalEdge (K + 2) => p.2.1.val) hqq'
      simp only [ι] at h1 h2
      exact Prod.ext (Subtype.ext (Fin.ext (by omega))) (Fin.ext h2)
    · intro p _ hp
      have hnot : ¬ IsInteriorDualEdge (K := K) (.inr p) := by
        intro hint
        apply hp
        obtain ⟨hs, ht⟩ := hint
        simp only [rotatorDualGraph, wiredBoxGraph, wiredBoxSrc, wiredBoxTgt,
          verticalPrimalSrc, verticalPrimalTgt] at hs ht
        have hx0 : p.1.val ≠ 0 := by
          intro hc
          simp [hc] at hs
        have hx1 : p.1.val < K + 1 := by
          by_contra hc
          simp [hc] at ht
        refine ⟨(⟨⟨p.1.val - 1, by omega⟩, by simp; omega⟩, ⟨p.2.1.val, by have := p.2.2; omega⟩),
          Finset.mem_coe.mpr (Finset.mem_univ _), ?_⟩
        apply Prod.ext
        · apply Fin.ext
          simp only [ι]
          omega
        · exact Subtype.ext (Fin.ext rfl)
      simp only [freeDualWeight, hnot, ↓reduceIte]
    · intro q _
      have hx : q.1.1.val + 1 < K + 1 := q.1.2
      have hint : IsInteriorDualEdge (K := K) (.inr (ι q)) := by
        constructor <;>
        simp [ι, rotatorDualGraph, wiredBoxGraph, wiredBoxSrc, wiredBoxTgt,
          verticalPrimalSrc, verticalPrimalTgt, hx]
      simp only [freeDualWeight, hint, ↓reduceIte, phase_dualEdgeFrequency]
      congr 1
      simp [ι, rotatorDualGraph, wiredBoxGraph, wiredBoxSrc, wiredBoxTgt, verticalPrimalSrc,
        verticalPrimalTgt, verticalFaceY, faceExtAngle, rotatorFreeGraph, squareFreeGraph, hx]
  · -- primal horizontal bonds ↔ face vertical bonds
    let ι : SquareFreeVerticalEdge (K + 1) → SquareFreeHorizontalEdge (K + 2) := fun q =>
      (⟨⟨q.1.val, by have := q.1.isLt; omega⟩, by have := q.1.isLt; simp; omega⟩,
        ⟨q.2.1.val + 1, by have := q.2.2; omega⟩)
    symm
    refine Finset.prod_of_injOn ι ?_ (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _)) ?_ ?_
    · intro q _ q' _ hqq'
      have h1 := congrArg (fun p : SquareFreeHorizontalEdge (K + 2) => p.1.1.val) hqq'
      have h2 := congrArg (fun p : SquareFreeHorizontalEdge (K + 2) => p.2.val) hqq'
      simp only [ι] at h1 h2
      exact Prod.ext (Fin.ext h1) (Subtype.ext (Fin.ext (by omega)))
    · intro p _ hp
      have hnot : ¬ IsInteriorDualEdge (K := K) (.inl p) := by
        intro hint
        apply hp
        obtain ⟨hs, ht⟩ := hint
        simp only [rotatorDualGraph, wiredBoxGraph, wiredBoxSrc, wiredBoxTgt,
          horizontalPrimalSrc, horizontalPrimalTgt] at hs ht
        have hy1 : p.2.val < K + 1 := by
          by_contra hc
          simp [hc] at hs
        have hy0 : p.2.val ≠ 0 := by
          intro hc
          simp [hc] at ht
        refine ⟨(⟨p.1.1.val, by have := p.1.2; omega⟩, ⟨⟨p.2.val - 1, by omega⟩, by simp; omega⟩),
          Finset.mem_coe.mpr (Finset.mem_univ _), ?_⟩
        apply Prod.ext
        · exact Subtype.ext (Fin.ext rfl)
        · apply Fin.ext
          simp only [ι]
          omega
      simp only [freeDualWeight, hnot, ↓reduceIte]
    · intro q _
      have hint : IsInteriorDualEdge (K := K) (.inl (ι q)) := by
        constructor <;>
        simp [ι, rotatorDualGraph, wiredBoxGraph, wiredBoxSrc, wiredBoxTgt,
          horizontalPrimalSrc, horizontalPrimalTgt, q.2.2]
      simp only [freeDualWeight, hint, ↓reduceIte, phase_dualEdgeFrequency]
      rw [← VillainWeight.villainWeight_neg, neg_sub]
      have hy : q.2.1.val + 1 < K + 1 := q.2.2
      congr 1
      simp [ι, rotatorDualGraph, wiredBoxGraph, wiredBoxSrc, wiredBoxTgt, horizontalPrimalSrc,
        horizontalPrimalTgt, horizontalFaceX, faceExtAngle, rotatorFreeGraph, squareFreeGraph, hy]

end DualEdges

/-! ### Wired dominates free -/

section Comparison

variable {K N : ℕ}

/-- The two-point frequency `k (e_a − e_b)`. -/
def faceTwoPointFrequency (k : ℤ) (a b : RotatorSpinSite K) : Frequency (RotatorSpinSite K) :=
  fun v => k * ((if v = a then 1 else 0) - (if v = b then 1 else 0))

theorem phase_faceTwoPointFrequency (k : ℤ) (a b : RotatorSpinSite K) (θ : RotatorSpinSite K → ℝ) :
    phase (faceTwoPointFrequency k a b) θ = k * (θ a - θ b) := by
  classical
  simp only [phase, faceTwoPointFrequency, Int.cast_mul, Int.cast_sub, Int.cast_ite, Int.cast_one,
    Int.cast_zero, mul_assoc, sub_mul, ite_mul, one_mul, zero_mul, ← Finset.mul_sum,
    Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

theorem isBondWeight_freeDualWeight {β : ℝ} (hβ : 0 < β) (e : RotatorInternalBond (K + 1)) :
    IsBondWeight (freeDualWeight β e) := by
  unfold freeDualWeight
  split_ifs
  · exact isBondWeight_villain hβ
  · exact isBondWeight_one

/-- **Ginibre: the wired dual Villain clock dominates the free face model.** -/
theorem villainClockModel_twoPoint_le_dual (hN : 0 < N) {βd : ℝ} (hβd : 0 < βd) (k : ℤ)
    (a b : RotatorSpinSite K) :
    (model N hN βd hβd).twoPoint k (squareBoxZ K) (siteToZ a) (siteToZ b) ≤
      (∑ h : SquareFreeVertex (K + 1) → Fin N, dualFaceWeight βd h *
          Real.cos ((k : ℝ) * (dualFaceAngle h (some a) - dualFaceAngle h (some b)))) /
        ∑ h : SquareFreeVertex (K + 1) → Fin N, dualFaceWeight βd h := by
  classical
  have hν0 := clockMeasure_univ_ne_zero hN
  have hw₁ : ∀ e : RotatorInternalBond (K + 1), IsBondWeight
      ((fun _ => villainWeight βd) e) := fun _ => isBondWeight_villain hβd
  have hw₂ : ∀ e : RotatorInternalBond (K + 1), IsBondWeight (freeDualWeight βd e) :=
    isBondWeight_freeDualWeight hβd
  have hpair : ∀ e : RotatorInternalBond (K + 1),
      IsGinibrePair (RotatorSpinSite K) ((fun _ => villainWeight βd) e) (freeDualWeight βd e) := by
    intro e
    unfold freeDualWeight
    split_ifs
    · exact isGinibrePair_villain hβd le_rfl
    · exact isGinibrePair_villain_one hβd
  have hcomp := integral_cos_pairGibbs_le (hasRealFourier_clock hN) (hasRealFourier_clock hN)
    hν0 hν0 (hasEquivKernel_clock N) (d := dualEdgeFrequency (K := K)) hw₁ hw₂ hpair
    (faceTwoPointFrequency k a b)
  -- the free side is the Villain-clock model on the face square
  have hfree : ∫ θ, Real.cos (phase (faceTwoPointFrequency k a b) θ)
      ∂pairGibbs (clockMeasure N) (dualEdgeFrequency (K := K)) (freeDualWeight βd) =
      (model N hN βd hβd).twoPoint k (squareBoxZ K) (siteToZ a) (siteToZ b) := by
    rw [villainClockModel_twoPoint_squareBox, integral_pairGibbs hν0 hw₂, pairPartition,
      integral_siteProduct_clockMeasure, integral_siteProduct_clockMeasure]
    congr 1
    · refine Finset.sum_congr rfl fun s _ => ?_
      rw [phase_faceTwoPointFrequency, pairWeight, prod_freeDualWeight_eq]
      rfl
    · refine Finset.sum_congr rfl fun s _ => ?_
      rw [pairWeight, prod_freeDualWeight_eq]
      rfl
  -- the wired side is the dual height sum
  have hface : ∀ (h : SquareFreeVertex (K + 1) → Fin N) (f : RotatorDualFace (K + 1)),
      faceExtAngle (fun i => 2 * Real.pi * ((h i : ℕ) : ℝ) / N) f = dualFaceAngle h f := by
    intro h f
    cases f with
    | none => simp [faceExtAngle, dualFaceAngle, clockFaceLift]
    | some v => simp [faceExtAngle, dualFaceAngle, clockFaceLift]
  have hwired : ∫ θ, Real.cos (phase (faceTwoPointFrequency k a b) θ)
      ∂pairGibbs (clockMeasure N) (dualEdgeFrequency (K := K)) (fun _ => villainWeight βd) =
      (∑ h : SquareFreeVertex (K + 1) → Fin N, dualFaceWeight βd h *
          Real.cos ((k : ℝ) * (dualFaceAngle h (some a) - dualFaceAngle h (some b)))) /
        ∑ h : SquareFreeVertex (K + 1) → Fin N, dualFaceWeight βd h := by
    rw [integral_pairGibbs hν0 hw₁, pairPartition, integral_siteProduct_clockMeasure,
      integral_siteProduct_clockMeasure]
    have hpw : ∀ h : SquareFreeVertex (K + 1) → Fin N,
        pairWeight (dualEdgeFrequency (K := K)) (fun _ => villainWeight βd)
          (fun i => 2 * Real.pi * ((h i : ℕ) : ℝ) / N) = dualFaceWeight βd h := by
      intro h
      unfold pairWeight dualFaceWeight
      refine Finset.prod_congr rfl fun e _ => ?_
      rw [phase_dualEdgeFrequency, hface, hface]
    congr 1
    · refine Finset.sum_congr rfl fun h _ => ?_
      rw [phase_faceTwoPointFrequency, hpw, mul_comm]
      congr 2
    · exact Finset.sum_congr rfl fun h _ => hpw h
  rw [← hfree, ← hwired]
  exact hcomp

end Comparison

end FroehlichSpencer.BKT.Clock.VillainClock

end
