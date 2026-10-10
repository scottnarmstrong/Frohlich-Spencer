/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.SpinWaves.Prop47
public import FroehlichSpencer.BKT.SpinWaves.FlattenedWave
public import FroehlichSpencer.BKT.SpinWaves.BoundaryShellPacking
import Mathlib.Tactic
import Mathlib.Tactic.Linarith

/-! # Gradient bounds for flattened square profiles

The edgewise estimate for a flattened ramp is `sq_flatten_ramp_edge_le`.  Combining it with the
component diameter estimate supplied by the root-distance clause of KP Lemma 4.6 gives the
scale-decaying gradient bound needed for a graded square-profile piece.  We keep the finite
boundary incidence count explicit: on the free and even-periodic square lattices it is bounded
from the degree-four geometry.
-/

@[expose] public section

namespace FroehlichSpencer.BKT.Generic.SpinWave

open FroehlichSpencer.BKT.SpinWaves
open FroehlichSpencer.BKT.SpinWaves.P47

variable {V : Type} {E : Type} [Fintype V] [Fintype E] [DecidableEq V]

/-- A scale-uniform bound on the boundary contribution in the flattened-ramp edge estimate.
`D` bounds one plus the diameter of every relevant component, and `N` bounds how many such
component boundaries can meet one edge. -/
theorem squareWaveProfile_grad_sq_le
    (G : Multigraph V E) (N₁ : Finset (V → ℤ)) (centerOf : (V → ℤ) → V)
    (hG : G.toSimpleGraph.Connected) {s : Finset V} (hs : s.Nonempty)
    {r S : ℕ} (hrS : r ≤ S) (D N : ℝ)
    (hdiam : ∀ c ∈ relevantComponents G N₁ centerOf s S,
      (densityPlusComponentDiameter G N₁ centerOf c : ℝ) + 1 ≤ D)
    (hcount : ∀ e : E,
      (((relevantComponents G N₁ centerOf s S).filter fun c =>
        G.src e ∈ densityPlusExternalBoundary G N₁ centerOf c ∨
          G.tgt e ∈ densityPlusExternalBoundary G N₁ centerOf c).card : ℝ) ≤ N)
    (e : E) :
    (G.grad (flatten G N₁ centerOf (fun j => ramp r S (setDist G s j))
      (componentRep G N₁ centerOf (setDist G s) r S)) e) ^ 2 ≤
      (1 + N * D ^ 2) / ((S + 1 - r : ℕ) : ℝ) ^ 2 := by
  have hq : 0 < ((S + 1 - r : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < S + 1 - r by omega)
  have hfirst : (if setDist G s (G.src e) ≤ S + 1 then
      1 / ((S + 1 - r : ℕ) : ℝ) ^ 2 else 0) ≤
      1 / ((S + 1 - r : ℕ) : ℝ) ^ 2 := by
    by_cases h : setDist G s (G.src e) ≤ S + 1
    · simp [h]
    · simp [h]
  have hterms : ∀ c ∈ relevantComponents G N₁ centerOf s S,
      (if G.src e ∈ densityPlusExternalBoundary G N₁ centerOf c ∨
          G.tgt e ∈ densityPlusExternalBoundary G N₁ centerOf c then
        ((densityPlusComponentDiameter G N₁ centerOf c : ℝ) + 1) ^ 2 /
          ((S + 1 - r : ℕ) : ℝ) ^ 2 else 0) ≤
      (if G.src e ∈ densityPlusExternalBoundary G N₁ centerOf c ∨
          G.tgt e ∈ densityPlusExternalBoundary G N₁ centerOf c then
        D ^ 2 / ((S + 1 - r : ℕ) : ℝ) ^ 2 else 0) := by
    intro c hc
    split_ifs with hhit
    · apply (div_le_div_iff_of_pos_right (sq_pos_of_pos hq)).2
      exact pow_le_pow_left₀ (by positivity) (hdiam c hc) 2
    · rfl
  have hsum := Finset.sum_le_sum fun c hc => hterms c hc
  have hfilter :
      (∑ c ∈ relevantComponents G N₁ centerOf s S,
        if G.src e ∈ densityPlusExternalBoundary G N₁ centerOf c ∨
            G.tgt e ∈ densityPlusExternalBoundary G N₁ centerOf c then
          D ^ 2 / ((S + 1 - r : ℕ) : ℝ) ^ 2 else 0) =
      (( (relevantComponents G N₁ centerOf s S).filter fun c =>
        G.src e ∈ densityPlusExternalBoundary G N₁ centerOf c ∨
          G.tgt e ∈ densityPlusExternalBoundary G N₁ centerOf c).card : ℝ) *
        (D ^ 2 / ((S + 1 - r : ℕ) : ℝ) ^ 2) := by
    rw [← Finset.sum_filter]
    simp [mul_comm]
  have hsumBound :
      (∑ c ∈ relevantComponents G N₁ centerOf s S,
        if G.src e ∈ densityPlusExternalBoundary G N₁ centerOf c ∨
            G.tgt e ∈ densityPlusExternalBoundary G N₁ centerOf c then
          ((densityPlusComponentDiameter G N₁ centerOf c : ℝ) + 1) ^ 2 /
            ((S + 1 - r : ℕ) : ℝ) ^ 2 else 0) ≤
      N * D ^ 2 / ((S + 1 - r : ℕ) : ℝ) ^ 2 := by
    calc
      _ ≤ ∑ c ∈ relevantComponents G N₁ centerOf s S,
          if G.src e ∈ densityPlusExternalBoundary G N₁ centerOf c ∨
              G.tgt e ∈ densityPlusExternalBoundary G N₁ centerOf c then
            D ^ 2 / ((S + 1 - r : ℕ) : ℝ) ^ 2 else 0 := hsum
      _ = _ := by rw [hfilter]
      _ ≤ _ := by
          have hfactor : 0 ≤ D ^ 2 / ((S + 1 - r : ℕ) : ℝ) ^ 2 := by positivity
          exact (mul_le_mul_of_nonneg_right (hcount e) hfactor).trans_eq (by ring)
  have hraw := sq_flatten_ramp_edge_le G N₁ centerOf hG hs hrS e
  have hgrad := hraw.trans (add_le_add hfirst hsumBound)
  convert hgrad using 1
  field_simp [hq.ne']

/--
Pointwise `L∞` gradient bound for a flattened P4.7 square profile.
-/
theorem squareWaveProfile_grad_le
    (G : Multigraph V E) (N₁ : Finset (V → ℤ)) (centerOf : (V → ℤ) → V)
    (hG : G.toSimpleGraph.Connected) {s : Finset V} (hs : s.Nonempty) (k : ℕ)
    (D N : ℝ)
    (hdiam : ∀ c ∈ relevantComponents G N₁ centerOf s (2 ^ (k - 1)),
      (densityPlusComponentDiameter G N₁ centerOf c : ℝ) + 1 ≤ D)
    (hcount : ∀ e : E,
      (((relevantComponents G N₁ centerOf s (2 ^ (k - 1))).filter fun c =>
        G.src e ∈ densityPlusExternalBoundary G N₁ centerOf c ∨
          G.tgt e ∈ densityPlusExternalBoundary G N₁ centerOf c).card : ℝ) ≤ N)
    (e : E) :
    |G.grad (squareWaveProfile G N₁ centerOf s k) e| ≤
      Real.sqrt ((1 + N * D ^ 2) /
        (((2 ^ (k - 1) + 1 - 2 ^ (k - 3) : ℕ) : ℝ) ^ 2)) := by
  have hsq := squareWaveProfile_grad_sq_le G N₁ centerOf hG hs
    (plateau_le_support k) D N hdiam hcount e
  have hN : 0 ≤ N := by
    have h := hcount e
    exact (by positivity : 0 ≤ (((relevantComponents G N₁ centerOf s (2 ^ (k - 1))).filter
      fun c => G.src e ∈ densityPlusExternalBoundary G N₁ centerOf c ∨
        G.tgt e ∈ densityPlusExternalBoundary G N₁ centerOf c).card : ℝ)).trans h
  have hnum : 0 ≤ 1 + N * D ^ 2 := by
    have := mul_nonneg hN (sq_nonneg D)
    linarith
  have hR : 0 ≤ (1 + N * D ^ 2) /
      (((2 ^ (k - 1) + 1 - 2 ^ (k - 3) : ℕ) : ℝ) ^ 2) :=
    div_nonneg hnum (sq_nonneg _)
  have hsq' : |G.grad (squareWaveProfile G N₁ centerOf s k) e| ^ 2 ≤
      Real.sqrt ((1 + N * D ^ 2) /
        (((2 ^ (k - 1) + 1 - 2 ^ (k - 3) : ℕ) : ℝ) ^ 2)) ^ 2 := by
    rw [Real.sq_sqrt hR]
    simpa [squareWaveProfile, sq_abs] using hsq
  nlinarith [abs_nonneg (G.grad (squareWaveProfile G N₁ centerOf s k) e),
    Real.sqrt_nonneg ((1 + N * D ^ 2) /
      (((2 ^ (k - 1) + 1 - 2 ^ (k - 3) : ℕ) : ℝ) ^ 2))]

/-- The L4.6(2) root-distance inequality and the scale separation estimate used in P4.7 give
the coarse diameter power bound recorded inHere `d` is the component diameter and
`R` its distance from the charge center. -/
theorem componentDiameter_rpow_le_of_l46
    {M d R : ℝ} {k : ℕ} (hM : 0 < M) (hd : 0 ≤ d)
    (hl46 : M / 128 * d ^ (7 / 4 : ℝ) ≤ R)
    (hroot : R ≤ (5 / 2 : ℝ) * (2 : ℝ) ^ k + d)
    (hsmall : d ≤ (2 : ℝ) ^ k / 200) :
    d ^ (7 / 4 : ℝ) ≤ (384 / M) * (2 : ℝ) ^ k := by
  have hpow : 0 ≤ d ^ (7 / 4 : ℝ) := Real.rpow_nonneg hd _
  have hM128 : 0 < M / 128 := by positivity
  have hbound : M / 128 * d ^ (7 / 4 : ℝ) ≤ (3 : ℝ) * (2 : ℝ) ^ k := by
    calc
      M / 128 * d ^ (7 / 4 : ℝ) ≤ R := hl46
      _ ≤ (5 / 2 : ℝ) * (2 : ℝ) ^ k + d := hroot
      _ ≤ (5 / 2 : ℝ) * (2 : ℝ) ^ k + (2 : ℝ) ^ k / 200 := by linarith
      _ ≤ 3 * (2 : ℝ) ^ k := by
        have hx : 0 ≤ (2 : ℝ) ^ k := by positivity
        nlinarith
  have htarget : (M / 128) * ((384 / M) * (2 : ℝ) ^ k) =
      3 * (2 : ℝ) ^ k := by field_simp [hM.ne']; ring
  have hmul : (M / 128) * d ^ (7 / 4 : ℝ) ≤
      (M / 128) * ((384 / M) * (2 : ℝ) ^ k) := by rw [htarget]; exact hbound
  exact le_of_mul_le_mul_left hmul hM128

end FroehlichSpencer.BKT.Generic.SpinWave

end
