/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Clock.Disorder.VortexProfile
import Mathlib.Tactic

/-!
# Logarithmic seam profile on the compact clock carrier

The straight vertical seam in the centered spin square is a horizontal unit-current path in a
larger auxiliary free square. Its dual faces identify with the original spin sites by reflecting
the second coordinate. The harmonic-field profile therefore gives an exact site-gradient
plus residual decomposition on the compact clock carrier, with a finite coarse logarithmic-energy
constant.
-/

@[expose] public section

noncomputable section

open FroehlichSpencer.BKT.Rotator
open FroehlichSpencer.BKT.Rotator.TheoremC
open FroehlichSpencer.BKT.Lattice2D
open FroehlichSpencer.BKT.Villain
open FroehlichSpencer.BKT.Duality

namespace FroehlichSpencer.BKT.Clock.Disorder

def auxPathCurrent {M u u' y : ℕ} : RotatorInternalBond M → ℤ :=
  boxCurrent M (hJ (u : ℤ) (u' : ℤ) (y : ℤ)) (fun _ _ => 0)

def auxiliarySeamCurrent {L r : ℕ} : RotatorInternalBond (2 * L + 1) → ℤ :=
  auxPathCurrent (M := 2 * L + 1) (u := L + 1) (u' := L + r + 1) (y := L)

def siteAt {M : ℕ} (x y : ℕ) (hx : x ≤ M) (hy : y ≤ M) : RotatorSpinSite M :=
  (⟨x, by omega⟩, ⟨y, by omega⟩)

def auxiliarySeamStart {L : ℕ} (hL : 0 < L) : RotatorSpinSite (2 * L + 1) :=
  siteAt (L + 1) L (by omega) (by omega)

def auxiliarySeamFinish {L r : ℕ} (hL : 0 < L) (hr : r ≤ L) :
    RotatorSpinSite (2 * L + 1) := siteAt (L + r + 1) L (by omega) (by omega)

theorem auxPathCurrent_divergence {M u u' y : ℕ} (hu : 0 < u) (hu' : 0 < u')
    (huM : u ≤ M)
    (hu'M : u' ≤ M) (hyM : y ≤ M) :
    ∀ v : RotatorSpinSite M,
      rotatorCurrentDivergence (auxPathCurrent (M := M) (u := u) (u' := u') (y := y)) v =
        rotatorTwoPointFrequency (siteAt u y huM hyM) (siteAt u' y hu'M hyM) 1 v := by
  classical
  intro v
  change rotatorCurrentDivergence
      (boxCurrent M (hJ (u : ℤ) (u' : ℤ) (y : ℤ)) (fun _ _ => 0)) v = _
  rw [div_boxCurrent
    (fun x z hx => by
      have hs := hJ_ne_zero hx
      have huZ : 0 ≤ (u : ℤ) := by exact_mod_cast Nat.zero_le u
      have hu'Z : 0 ≤ (u' : ℤ) := by exact_mod_cast Nat.zero_le u'
      have huPosZ : 0 < (u : ℤ) := by exact_mod_cast hu
      have hu'PosZ : 0 < (u' : ℤ) := by exact_mod_cast hu'
      have huMZ : (u : ℤ) ≤ M := by exact_mod_cast huM
      have hu'MZ : (u' : ℤ) ≤ M := by exact_mod_cast hu'M
      have hmax : max (u : ℤ) (u' : ℤ) ≤ M := max_le huMZ hu'MZ
      have hmin : 0 < min (u : ℤ) (u' : ℤ) := lt_min huPosZ hu'PosZ
      omega)
    (fun _ _ hx => by simp at hx)]
  simp only [add_zero, sub_zero]
  have hh := hJ_div (u : ℤ) (u' : ℤ) (y : ℤ)
    ((v.1 : ℕ) : ℤ) ((v.2 : ℕ) : ℤ)
  have hstart : (v = siteAt u y huM hyM) ↔ (v.1.val = u ∧ v.2.val = y) := by
    constructor
    · intro hv
      have hv1 := congrArg Prod.fst hv
      have hv2 := congrArg Prod.snd hv
      constructor
      · simpa [siteAt] using congrArg Fin.val hv1
      · simpa [siteAt] using congrArg Fin.val hv2
    · rintro ⟨hx, hy⟩
      apply Prod.ext
      · apply Fin.ext; exact hx
      · apply Fin.ext; exact hy
  have hfinish : (v = siteAt u' y hu'M hyM) ↔ (v.1.val = u' ∧ v.2.val = y) := by
    constructor
    · intro hv
      have hv1 := congrArg Prod.fst hv
      have hv2 := congrArg Prod.snd hv
      constructor
      · simpa [siteAt] using congrArg Fin.val hv1
      · simpa [siteAt] using congrArg Fin.val hv2
    · rintro ⟨hx, hy⟩
      apply Prod.ext
      · apply Fin.ext; exact hx
      · apply Fin.ext; exact hy
  have hPcast : (((v.1.val : ℤ) = u ∧ (v.2.val : ℤ) = y) ↔
      (v.1.val = u ∧ v.2.val = y)) := by norm_cast
  have hQcast : (((v.1.val : ℤ) = u' ∧ (v.2.val : ℤ) = y) ↔
      (v.1.val = u' ∧ v.2.val = y)) := by norm_cast
  have hhNat : hJ (u : ℤ) (u' : ℤ) (y : ℤ) ((v.1 : ℕ) : ℤ)
      ((v.2 : ℕ) : ℤ) -
        hJ (u : ℤ) (u' : ℤ) (y : ℤ) (((v.1 : ℕ) : ℤ) - 1) ((v.2 : ℕ) : ℤ) =
      (if v.1.val = u ∧ v.2.val = y then 1 else 0) -
        (if v.1.val = u' ∧ v.2.val = y then 1 else 0) := by
    simpa only [hPcast, hQcast] using hh
  change hJ (u : ℤ) (u' : ℤ) (y : ℤ) ((v.1 : ℕ) : ℤ) ((v.2 : ℕ) : ℤ) -
        hJ (u : ℤ) (u' : ℤ) (y : ℤ) (((v.1 : ℕ) - 1 : ℤ)) ((v.2 : ℕ) : ℤ) = _
  by_cases hx : v.1.val = 0
  · have huZ : (0 : ℤ) < u := by exact_mod_cast hu
    have hcurr : hJ (u : ℤ) (u' : ℤ) (y : ℤ) 0 ((v.2 : ℕ) : ℤ) = 0 := by
      by_contra hne
      have hs := hJ_ne_zero hne
      have huZ : (0 : ℤ) < u := by exact_mod_cast hu
      have hu'Z : (0 : ℤ) < u' := by exact_mod_cast hu'
      have hmin : 0 < min (u : ℤ) (u' : ℤ) := lt_min huZ hu'Z
      omega
    have hprev : hJ (u : ℤ) (u' : ℤ) (y : ℤ) (-1) ((v.2 : ℕ) : ℤ) = 0 := by
      by_contra hne
      have hs := hJ_ne_zero hne
      have huZ : (0 : ℤ) < u := by exact_mod_cast hu
      have hu'Z : (0 : ℤ) < u' := by exact_mod_cast hu'
      have hmin : 0 < min (u : ℤ) (u' : ℤ) := lt_min huZ hu'Z
      omega
    have hcoord0 : ((v.1 : ℕ) : ℤ) = 0 := by exact_mod_cast hx
    rw [hcoord0, hcurr, show (0 : ℤ) - 1 = -1 by norm_num, hprev]
    have hstartFalse : v ≠ siteAt u y huM hyM := by
      intro hv
      have hcoord := (hstart.mp hv).1
      omega
    have hfinishFalse : v ≠ siteAt u' y hu'M hyM := by
      intro hv
      have hcoord := (hfinish.mp hv).1
      have hu'Z : (0 : ℤ) < u' := by exact_mod_cast hu'
      omega
    simp [rotatorTwoPointFrequency, hstartFalse, hfinishFalse]
  · rw [hhNat]
    simp only [rotatorTwoPointFrequency, if_congr hstart, if_congr hfinish]
    have hneg : (if v.1.val = u' ∧ v.2.val = y then (-1 : ℤ) else 0) =
        -(if v.1.val = u' ∧ v.2.val = y then (1 : ℤ) else 0) := by
      by_cases hq : v.1.val = u' ∧ v.2.val = y <;> simp [hq]
    rw [hneg]
    ring

def auxEdgeMap {L : ℕ} : RotatorInternalBond (2 * L) → RotatorInternalBond (2 * L + 1)
  | .inl e => .inr (verticalDualEdgeData ⟨e.1.1.val + 1, by omega⟩ ⟨2 * L - e.2.val, by omega⟩)
  | .inr e => .inl (horizontalDualEdgeData ⟨e.1.val, by omega⟩ ⟨2 * L - e.2.1.val, by omega⟩)

def auxFaceShift {L : ℕ} (ψ : RotatorDualFace (2 * L + 1) → ℝ) :
    RotatorSpinSite (2 * L) → ℝ := fun v =>
  ψ (some (v.1, ⟨2 * L - v.2.val, by omega⟩))

def auxPulledCurrent {L r : ℕ} (e : RotatorInternalBond (2 * L)) : ℤ :=
  auxPathCurrent (M := 2 * L + 1) (u := L + 1) (u' := L + r + 1) (y := L)
    (auxEdgeMap e)

theorem auxSeamEdge_iff {L r : ℕ} (hbuf : 2 * r + 1 ≤ L)
    (e : SquareFreeVerticalEdge (2 * L + 1)) :
    (∃ i : Fin r, e = verticalDualEdgeData ⟨L + i.val + 1, by omega⟩ ⟨L, by omega⟩) ↔
      (L < e.1.val ∧ e.1.val < L + r + 1 ∧ e.2.1.val = L) := by
  constructor
  · rintro ⟨i, hi⟩
    have h₁ := congrArg (fun z : SquareFreeVerticalEdge (2 * L + 1) => z.1.val) hi
    have h₂ := congrArg (fun z : SquareFreeVerticalEdge (2 * L + 1) => z.2.1.val) hi
    simp only [verticalDualEdgeData, Fin.val_castLE] at h₁ h₂
    refine ⟨by omega, by omega, by omega⟩
  · rintro ⟨hlo, hhi, hy⟩
    let i : Fin r := ⟨e.1.val - (L + 1), by omega⟩
    refine ⟨i, ?_⟩
    apply Prod.ext
    · apply Fin.ext
      change e.1.val = L + (e.1.val - (L + 1)) + 1
      omega
    · apply Subtype.ext
      apply Fin.ext
      change e.2.1.val = L
      omega

theorem auxPulledCurrent_inr {L r : ℕ}
    (e : SquareFreeVerticalEdge (2 * L + 1)) :
    auxPulledCurrent (L := L) (r := r) (.inr e) =
      if L < e.1.val ∧ e.1.val < L + r + 1 ∧ e.2.1.val = L then 1 else 0 := by
  change hJ (L + 1 : ℤ) (L + r + 1 : ℤ) (L : ℤ) (e.1.val : ℤ)
    ((2 * L - e.2.1.val : ℕ) : ℤ) = _
  unfold hJ
  have hlength : segLen (L + 1 : ℤ) (L + r + 1 : ℤ) = r := by
    unfold segLen
    rw [show (L + r + 1 : ℤ) - (L + 1 : ℤ) = (r : ℤ) by omega]
    simp
  have hsign : segSign (L + 1 : ℤ) (L + r + 1 : ℤ) = 1 := by
    simp [segSign, show (L + 1 : ℤ) ≤ L + r + 1 by omega]
  rw [hlength, hsign]
  have hmin : min (L + 1 : ℤ) (L + r + 1 : ℤ) = (L + 1 : ℤ) := by
    apply min_eq_left
    omega
  rw [hmin]
  unfold jlay
  have hrow : ((2 * L - e.2.1.val : ℕ) : ℤ) - (L : ℤ) = 0 ↔ e.2.1.val = L := by
    have he := e.2.1.isLt
    omega
  have hcol :
      (0 ≤ (e.1.val : ℤ) - (L + 1 : ℤ) ∧
        (e.1.val : ℤ) - (L + 1 : ℤ) < (r : ℤ)) ↔
        (L < e.1.val ∧ e.1.val < L + r + 1) := by
    omega
  have hcond :
      (0 ≤ (e.1.val : ℤ) - (L + 1 : ℤ) ∧
          ((e.1.val : ℤ) - (L + 1 : ℤ) < (r : ℤ) ∧
            ((2 * L - e.2.1.val : ℕ) : ℤ) - (L : ℤ) = 0)) ↔
        (L < e.1.val ∧ e.1.val < L + r + 1 ∧ e.2.1.val = L) := by
    constructor
    · rintro ⟨ha, hb, hc⟩
      exact ⟨hcol.mp ⟨ha, hb⟩ |>.1, (hcol.mp ⟨ha, hb⟩).2, hrow.mp hc⟩
    · rintro ⟨ha, hb, hc⟩
      have hab := hcol.mpr ⟨ha, hb⟩
      exact ⟨hab.1, hab.2, hrow.mpr hc⟩
  simp only [hcond, mul_ite, one_mul]

theorem auxPulledCurrent_seam_indicator {L r : ℕ} (hbuf : 2 * r + 1 ≤ L)
    (e : RotatorInternalBond (2 * L)) :
    auxPulledCurrent (L := L) (r := r) e =
      if ∃ i : Fin r, e = .inr (verticalDualEdgeData ⟨L + i.val + 1, by omega⟩ ⟨L, by omega⟩)
      then 1 else 0 := by
  classical
  cases e with
  | inl e =>
      simp [auxPulledCurrent, auxPathCurrent, auxEdgeMap, boxCurrent]
  | inr e =>
      rw [auxPulledCurrent_inr e]
      simp only [Sum.inr.injEq]
      have hiff := auxSeamEdge_iff hbuf e
      exact if_congr hiff.symm rfl rfl

theorem auxEdgeMap_injective {L : ℕ} :
    Function.Injective (auxEdgeMap (L := L)) := by
  intro e₁ e₂ h
  cases e₁ with
  | inl a =>
    cases e₂ with
    | inl b =>
      simp only [auxEdgeMap, Sum.inr.injEq] at h
      have hx := congrArg (fun z : SquareFreeVerticalEdge (2 * L + 2) => z.1.val) h
      have hy := congrArg (fun z : SquareFreeVerticalEdge (2 * L + 2) => z.2.1.val) h
      simp only [verticalDualEdgeData, Fin.val_castLE] at hx hy
      have hab : a = b := by
        apply Prod.ext
        · apply Subtype.ext
          apply Fin.ext
          omega
        · apply Fin.ext
          omega
      exact congrArg Sum.inl hab
    | inr b => simp [auxEdgeMap] at h
  | inr a =>
    cases e₂ with
    | inl b => simp [auxEdgeMap] at h
    | inr b =>
      simp only [auxEdgeMap, Sum.inl.injEq] at h
      have hx := congrArg (fun z : SquareFreeHorizontalEdge (2 * L + 2) => z.1.1.val) h
      have hy := congrArg (fun z : SquareFreeHorizontalEdge (2 * L + 2) => z.2.val) h
      simp only [horizontalDualEdgeData, Fin.val_castLE] at hx hy
      have hab : a = b := by
        apply Prod.ext
        · apply Fin.ext
          omega
        · apply Subtype.ext
          apply Fin.ext
          omega
      exact congrArg Sum.inr hab

theorem auxFaceShift_grad_eq {L : ℕ} (ψ : RotatorDualFace (2 * L + 1) → ℝ)
    (e : RotatorInternalBond (2 * L)) :
    (rotatorDualGraph (2 * L + 1)).grad ψ (auxEdgeMap e) =
      (rotatorFreeGraph (2 * L)).grad (auxFaceShift ψ) e := by
  cases e with
  | inl e =>
      have hlt : e.1.1.val + 1 < 2 * L + 1 := e.1.2
      simp [Multigraph.grad, rotatorDualGraph, wiredBoxGraph, wiredBoxSrc, wiredBoxTgt,
        verticalPrimalSrc, verticalPrimalTgt, verticalFaceY, auxEdgeMap, auxFaceShift,
        verticalDualEdgeData, rotatorFreeGraph, squareFreeGraph, hlt]
  | inr e =>
      have hy := e.2.2
      have hpos : 2 * L - e.2.1.val ≠ 0 := by omega
      have hlt : 2 * L - e.2.1.val < 2 * L + 1 := by omega
      simp [Multigraph.grad, rotatorDualGraph, wiredBoxGraph, wiredBoxSrc, wiredBoxTgt,
        horizontalPrimalSrc, horizontalPrimalTgt, horizontalFaceX, auxEdgeMap, auxFaceShift,
        horizontalDualEdgeData, Fin.val_castLE, rotatorFreeGraph, squareFreeGraph, hpos, hlt]
      congr 1

theorem auxEdgeMap_energy_le {L : ℕ} (θ : RotatorInternalBond (2 * L + 1) → ℝ) :
    (∑ e : RotatorInternalBond (2 * L), θ (auxEdgeMap e) ^ 2) ≤
      ∑ e : RotatorInternalBond (2 * L + 1), θ e ^ 2 := by
  classical
  have himage :
      (∑ e ∈ Finset.univ.image (auxEdgeMap (L := L)), θ e ^ 2) =
        ∑ e : RotatorInternalBond (2 * L), θ (auxEdgeMap e) ^ 2 := by
    rw [Finset.sum_image fun e _ e' _ he => auxEdgeMap_injective he]
  rw [← himage]
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
  intro e _ _
  positivity

def originalSeamPullback {L r : ℕ} (e : RotatorInternalBond (2 * L)) : ℤ :=
  auxiliarySeamCurrent (L := L) (r := r) (auxEdgeMap e)

theorem originalSeamPullback_indicator {L r : ℕ} (hbuf : 2 * r + 1 ≤ L)
    (e : RotatorInternalBond (2 * L)) :
    originalSeamPullback (L := L) (r := r) e =
      if ∃ i : Fin r,
        e = .inr (verticalDualEdgeData ⟨L + i.val + 1, by omega⟩ ⟨L, by omega⟩)
      then 1 else 0 := by
  change auxPulledCurrent (L := L) (r := r) e = _
  exact auxPulledCurrent_seam_indicator hbuf e

theorem auxiliarySeamCurrent_divergence {L r : ℕ} (hbuf : 2 * r + 1 ≤ L)
    (hL : 0 < L) :
    ∀ v : RotatorSpinSite (2 * L + 1),
      rotatorCurrentDivergence (auxiliarySeamCurrent (L := L) (r := r)) v =
        rotatorTwoPointFrequency (auxiliarySeamStart (L := L) hL)
          (auxiliarySeamFinish (L := L) (r := r) hL (by omega)) 1 v := by
  have h := auxPathCurrent_divergence (M := 2 * L + 1) (u := L + 1) (u' := L + r + 1)
    (y := L) (by omega) (by omega) (by omega) (by omega) (by omega)
  simpa [auxiliarySeamCurrent, auxiliarySeamStart, auxiliarySeamFinish] using h

theorem exists_auxiliarySeamProfile {L r : ℕ} (hbuf : 2 * r + 1 ≤ L) (hL : 0 < L) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ ξ : ℝ,
      ∃ (σ : RotatorSpinSite (2 * L) → ℝ) (θ : RotatorInternalBond (2 * L) → ℝ),
        (∀ e, 2 * Real.pi * ξ *
          (if ∃ i : Fin r,
            e = .inr (verticalDualEdgeData ⟨L + i.val + 1, by omega⟩ ⟨L, by omega⟩)
            then (1 : ℤ) else 0 : ℝ) =
          (rotatorFreeGraph (2 * L)).grad σ e + θ e) ∧
        (∑ e, θ e ^ 2) ≤ ξ ^ 2 * C₀ * (1 + Real.log (1 + (r : ℝ))) := by
  let a := auxiliarySeamStart (L := L) hL
  let x := auxiliarySeamFinish (L := L) (r := r) hL (by omega)
  have hdist : siteL1 a x = r := by
    dsimp [siteL1, a, x, auxiliarySeamStart, auxiliarySeamFinish, siteAt]
    have hcoord : (L : ℤ) + 1 - ((L : ℤ) + (r : ℤ) + 1) = -(r : ℤ) := by ring
    rw [hcoord]
    simp
  have ha1 : a.1.val = L + 1 := by simp [a, auxiliarySeamStart, siteAt]
  have ha2 : a.2.val = L := by simp [a, auxiliarySeamStart, siteAt]
  have hx1 : x.1.val = L + r + 1 := by simp [x, auxiliarySeamFinish, siteAt]
  have hx2 : x.2.val = L := by simp [x, auxiliarySeamFinish, siteAt]
  have h₁ : siteL1 a x + 1 ≤ a.1.val := by rw [hdist, ha1]; omega
  have h₂ : a.1.val + siteL1 a x + 1 ≤ 2 * L + 1 := by rw [hdist, ha1]; omega
  have h₃ : siteL1 a x + 1 ≤ a.2.val := by rw [hdist, ha2]; omega
  have h₄ : a.2.val + siteL1 a x + 1 ≤ 2 * L + 1 := by rw [hdist, ha2]; omega
  have h₅ : siteL1 a x + 1 ≤ x.1.val := by rw [hdist, hx1]; omega
  have h₆ : x.1.val + siteL1 a x + 1 ≤ 2 * L + 1 := by rw [hdist, hx1]; omega
  have h₇ : siteL1 a x + 1 ≤ x.2.val := by rw [hdist, hx2]; omega
  have h₈ : x.2.val + siteL1 a x + 1 ≤ 2 * L + 1 := by rw [hdist, hx2]; omega
  obtain ⟨C₀, hC₀, hprofile⟩ := exists_scaled_vortex_decomposition
    (L := 2 * L + 1) a x h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈
  refine ⟨C₀, hC₀, fun ξ => ?_⟩
  have hdiv : ∀ v, rotatorCurrentDivergence (auxiliarySeamCurrent (L := L) (r := r)) v =
      rotatorTwoPointFrequency a x 1 v := by
    simpa only [a, x] using auxiliarySeamCurrent_divergence hbuf hL
  obtain ⟨ψ, θaux, heq, henergy⟩ := hprofile ξ auxiliarySeamCurrent hdiv
  let σ : RotatorSpinSite (2 * L) → ℝ := auxFaceShift ψ
  let θ : RotatorInternalBond (2 * L) → ℝ := fun e => θaux (auxEdgeMap e)
  refine ⟨σ, θ, ?_, ?_⟩
  · intro e
    have hq := originalSeamPullback_indicator hbuf e
    have hlocal := heq (auxEdgeMap e)
    change 2 * Real.pi * ξ * (originalSeamPullback e : ℝ) =
      (rotatorDualGraph (2 * L + 1)).grad ψ (auxEdgeMap e) + θaux (auxEdgeMap e) at hlocal
    rw [hq] at hlocal
    rw [auxFaceShift_grad_eq] at hlocal
    simpa [σ, θ, Int.cast_ite] using hlocal
  · calc
      (∑ e, θ e ^ 2) ≤ ∑ e : RotatorInternalBond (2 * L + 1), θaux e ^ 2 :=
        auxEdgeMap_energy_le θaux
      _ ≤ ξ ^ 2 * C₀ * (1 + Real.log (1 + (siteL1 a x : ℝ))) := henergy
      _ = ξ ^ 2 * C₀ * (1 + Real.log (1 + (r : ℝ))) := by rw [hdist]

end FroehlichSpencer.BKT.Clock.Disorder

end
