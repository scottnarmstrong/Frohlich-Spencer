/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.PinnedCharges.BoundaryEntropyGeometry
public import FroehlichSpencer.BKT.Generic.PinnedCharges.SelectionGGeometry

/-! # Euclidean overlap bounds for multiscale boundary profiles

This module proves the geometric packing step behind the cross-scale energy
estimate: if a fine square neighborhood met two neighborhoods of separated
coarse squares, then the coarse squares would be too close.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic.PinnedCharges

open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Generic.PinnedCharges.SelectionG

variable {L : ℕ}

/-- The Euclidean norm on two coordinate differences satisfies the triangle
inequality. -/
private theorem sqrt_sum_sq_triangle (a b c d : ℝ) :
    Real.sqrt ((a + c) ^ 2 + (b + d) ^ 2) ≤
      Real.sqrt (a ^ 2 + b ^ 2) + Real.sqrt (c ^ 2 + d ^ 2) := by
  let X := Real.sqrt (a ^ 2 + b ^ 2)
  let Y := Real.sqrt (c ^ 2 + d ^ 2)
  have hX : X ^ 2 = a ^ 2 + b ^ 2 := by
    dsimp [X]
    rw [Real.sq_sqrt (add_nonneg (sq_nonneg a) (sq_nonneg b))]
  have hY : Y ^ 2 = c ^ 2 + d ^ 2 := by
    dsimp [Y]
    rw [Real.sq_sqrt (add_nonneg (sq_nonneg c) (sq_nonneg d))]
  have hXY : 0 ≤ X * Y := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hdotSq : (a * c + b * d) ^ 2 ≤ (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) := by
    nlinarith [sq_nonneg (a * d - b * c)]
  have hdot : a * c + b * d ≤ X * Y := by
    have habs : |a * c + b * d| ≤ X * Y := by
      calc
        |a * c + b * d| = Real.sqrt ((a * c + b * d) ^ 2) := by
          rw [Real.sqrt_sq_eq_abs]
        _ ≤ Real.sqrt ((X * Y) ^ 2) := Real.sqrt_le_sqrt (by
          have hprod : (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) = (X * Y) ^ 2 := by
            rw [← hX, ← hY]
            ring
          rw [← hprod]
          exact hdotSq)
        _ = X * Y := by rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hXY]
    exact (le_abs_self _).trans habs
  have hsquares :
      (a + c) ^ 2 + (b + d) ^ 2 ≤ (X + Y) ^ 2 := by
    nlinarith [hX, hY, hdot]
  calc
    Real.sqrt ((a + c) ^ 2 + (b + d) ^ 2) ≤ Real.sqrt ((X + Y) ^ 2) :=
      Real.sqrt_le_sqrt hsquares
    _ = X + Y := by
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
    _ = Real.sqrt (a ^ 2 + b ^ 2) + Real.sqrt (c ^ 2 + d ^ 2) := rfl

/-- The lattice Euclidean distance obeys the triangle inequality. -/
theorem euclideanSiteDistance_triangle (x y z : Site L) :
    euclideanSiteDistance x z ≤ euclideanSiteDistance x y + euclideanSiteDistance y z := by
  unfold euclideanSiteDistance
  have h := sqrt_sum_sq_triangle
    ((x.1.val : ℝ) - y.1.val) ((x.2.val : ℝ) - y.2.val)
    ((y.1.val : ℝ) - z.1.val) ((y.2.val : ℝ) - z.2.val)
  have hcoord1 :
      ((x.1.val : ℝ) - y.1.val) + ((y.1.val : ℝ) - z.1.val) =
        (x.1.val : ℝ) - z.1.val := by ring
  have hcoord2 :
      ((x.2.val : ℝ) - y.2.val) + ((y.2.val : ℝ) - z.2.val) =
        (x.2.val : ℝ) - z.2.val := by ring
  rw [← hcoord1, ← hcoord2]
  exact h

/-- A finite set's radius-`r` Euclidean neighborhood. -/
def boundaryEnergyNeighborhood (r : ℝ) (s : Finset (Site L)) : Finset (Site L) :=
  Finset.univ.filter fun x => ∃ y ∈ s, euclideanSiteDistance y x ≤ r

theorem mem_boundaryEnergyNeighborhood_iff (r : ℝ) (s : Finset (Site L)) (x : Site L) :
    x ∈ boundaryEnergyNeighborhood r s ↔
      ∃ y ∈ s, euclideanSiteDistance y x ≤ r := by
  simp [boundaryEnergyNeighborhood]

/-- If a fine neighborhood meets two coarse neighborhoods, then the two
coarse bases are within `2R + 2r + diam(s)`. -/
theorem boundaryEnergy_two_coarse_neighborhoods_close
    (s t₁ t₂ : Finset (Site L)) (r R : ℝ)
    (hnear₁ : (boundaryEnergyNeighborhood r s ∩ boundaryEnergyNeighborhood R t₁).Nonempty)
    (hnear₂ : (boundaryEnergyNeighborhood r s ∩ boundaryEnergyNeighborhood R t₂).Nonempty) :
    euclideanSetDistance t₁ t₂ ≤ 2 * R + 2 * r + euclideanSetDiameter s := by
  obtain ⟨u, hu⟩ := hnear₁
  obtain ⟨x₁, hx₁, hux₁⟩ := (mem_boundaryEnergyNeighborhood_iff r s u).mp
    (Finset.mem_inter.mp hu).1
  obtain ⟨y₁, hy₁, huy₁⟩ := (mem_boundaryEnergyNeighborhood_iff R t₁ u).mp
    (Finset.mem_inter.mp hu).2
  obtain ⟨v, hv⟩ := hnear₂
  obtain ⟨x₂, hx₂, hvx₂⟩ := (mem_boundaryEnergyNeighborhood_iff r s v).mp
    (Finset.mem_inter.mp hv).1
  obtain ⟨y₂, hy₂, hvy₂⟩ := (mem_boundaryEnergyNeighborhood_iff R t₂ v).mp
    (Finset.mem_inter.mp hv).2
  have hdiam' : euclideanSiteDistance x₁ x₂ ≤ euclideanSetDiameter s :=
    SelectionG.siteDist_le_diam hx₁ hx₂
  have hsym₁ : euclideanSiteDistance y₁ u = euclideanSiteDistance u y₁ :=
    SelectionG.siteDist_comm _ _
  have hsym₂ : euclideanSiteDistance v y₂ = euclideanSiteDistance y₂ v :=
    SelectionG.siteDist_comm _ _
  have hsymX₁ : euclideanSiteDistance u x₁ = euclideanSiteDistance x₁ u :=
    SelectionG.siteDist_comm _ _
  have hpath : euclideanSiteDistance y₁ y₂ ≤ 2 * R + 2 * r +
      euclideanSetDiameter s := by
    calc
      euclideanSiteDistance y₁ y₂ ≤ euclideanSiteDistance y₁ u +
          euclideanSiteDistance u y₂ := euclideanSiteDistance_triangle y₁ u y₂
      _ ≤ euclideanSiteDistance y₁ u + euclideanSiteDistance u x₁ +
          euclideanSiteDistance x₁ y₂ := by
        nlinarith [euclideanSiteDistance_triangle u x₁ y₂]
      _ ≤ euclideanSiteDistance y₁ u + euclideanSiteDistance u x₁ +
          euclideanSiteDistance x₁ x₂ + euclideanSiteDistance x₂ y₂ := by
        nlinarith [euclideanSiteDistance_triangle x₁ x₂ y₂]
      _ ≤ euclideanSiteDistance y₁ u + euclideanSiteDistance u x₁ +
          euclideanSiteDistance x₁ x₂ + euclideanSiteDistance x₂ v +
            euclideanSiteDistance v y₂ := by
        nlinarith [euclideanSiteDistance_triangle x₂ v y₂]
      _ ≤ R + r + euclideanSetDiameter s + r + R := by
        rw [hsymX₁, hsym₂]
        nlinarith [huy₁, hux₁, hdiam', hvx₂, hvy₂]
      _ = 2 * R + 2 * r + euclideanSetDiameter s := by ring
  exact (setDist_le_siteDist hy₁ hy₂).trans hpath

/-- Intersecting equal-radius neighborhoods force their bases within twice the
radius. -/
theorem boundaryEnergy_two_neighborhoods_close
    (t₁ t₂ : Finset (Site L)) (R : ℝ)
    (hnear : (boundaryEnergyNeighborhood R t₁ ∩
      boundaryEnergyNeighborhood R t₂).Nonempty) :
    euclideanSetDistance t₁ t₂ ≤ 2 * R := by
  obtain ⟨x, hx⟩ := hnear
  obtain ⟨y₁, hy₁, h₁⟩ := (mem_boundaryEnergyNeighborhood_iff R t₁ x).mp
    (Finset.mem_inter.mp hx).1
  obtain ⟨y₂, hy₂, h₂⟩ := (mem_boundaryEnergyNeighborhood_iff R t₂ x).mp
    (Finset.mem_inter.mp hx).2
  have hsym : euclideanSiteDistance x y₂ = euclideanSiteDistance y₂ x :=
    SelectionG.siteDist_comm _ _
  calc
    euclideanSetDistance t₁ t₂ ≤ euclideanSiteDistance y₁ y₂ :=
      setDist_le_siteDist hy₁ hy₂
    _ ≤ euclideanSiteDistance y₁ x + euclideanSiteDistance x y₂ :=
      euclideanSiteDistance_triangle y₁ x y₂
    _ ≤ R + R := by rw [hsym]; nlinarith [h₁, h₂]
    _ = 2 * R := by ring

/-- Strong coarse-scale separation prevents two coarse profile neighborhoods
from meeting the same fine profile neighborhood. -/
theorem boundaryEnergy_neighborhood_overlap_excludes_two_coarse
    (s t₁ t₂ : Finset (Site L)) (r R M : ℝ) (α : ℝ)
    (hdiam : euclideanSetDiameter s ≤ Real.sqrt 2 * r)
    (hr : 0 < r) (hR : 0 ≤ R) (hRone : 1 ≤ R) (hscale : r ≤ R / 2)
    (hM : 4 ≤ M) (hα : 1 ≤ α)
    (hsep : 2 * M * R ^ α ≤ euclideanSetDistance t₁ t₂)
    (hnear₁ : (boundaryEnergyNeighborhood r s ∩ boundaryEnergyNeighborhood R t₁).Nonempty)
    (hnear₂ : (boundaryEnergyNeighborhood r s ∩ boundaryEnergyNeighborhood R t₂).Nonempty) :
    False := by
  have hclose := boundaryEnergy_two_coarse_neighborhoods_close s t₁ t₂ r R
    hnear₁ hnear₂
  have hRpow : R ≤ R ^ α := by
    exact Real.self_le_rpow_of_one_le hRone hα
  have hsep4 : 4 * R ≤ euclideanSetDistance t₁ t₂ := by
    calc
      4 * R ≤ 2 * M * R := by nlinarith [hR]
      _ ≤ 2 * M * R ^ α := by nlinarith [hM, hR, hRpow]
      _ ≤ euclideanSetDistance t₁ t₂ := hsep
  have hbound : 2 * R + 2 * r + Real.sqrt 2 * r < 4 * R := by
    have hcoeff : 2 + Real.sqrt 2 < 4 := by
      have hsqrt2 : Real.sqrt 2 < 2 := by nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      linarith
    have hmul : (2 + Real.sqrt 2) * r < 4 * r :=
      mul_lt_mul_of_pos_right hcoeff hr
    have h4r : 4 * r ≤ 2 * R := by nlinarith [hscale]
    nlinarith
  have : euclideanSetDistance t₁ t₂ < 4 * R := by
    exact hclose.trans_lt (by nlinarith [hdiam, hbound])
  linarith

end FroehlichSpencer.BKT.Generic.PinnedCharges

end
