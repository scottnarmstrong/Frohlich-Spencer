/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.VillainDisorder.Dirichlet.MarkedInterface
public import FroehlichSpencer.BKT.Generic.PinnedCharges.LayerRoutineBase
import Mathlib.Tactic

/-!
# Bounded-face base waves for rooted marked composites

The free marked-wave construction selects a checkerboard class on a bipartite degree-four graph.
The wired graph `squareZero` is not bipartite, because its exterior root is adjacent to boundary
faces of both parities. Here the base choice is made only on bounded faces. Neutrality bounds the
root charge by the total face mass, and doubling the sign bumps on the heavier face parity restores
the half-mass estimate for a real source.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.VillainDisorder.Dirichlet

open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Rotator
open FroehlichSpencer.BKT.Lattice2D
open FroehlichSpencer.BKT.Generic.PinnedCharges.Layer
open FroehlichSpencer.BKT.Generic.SpinWave

variable {L : ℕ}

/-- The absolute mass of a real source on one parity class of bounded faces. -/
def rootedRealParityMass (ρ : RotatorDualFace L → ℝ) (b : ℕ) : ℝ :=
  ∑ x : SquareFreeVertex L,
    if (x.1.val + x.2.val) % 2 = b then |ρ (some x)| else 0

/-- The heavier parity class, computed using bounded faces only. -/
def rootedRealBaseParity (ρ : RotatorDualFace L → ℝ) : ℕ :=
  if rootedRealParityMass ρ 1 ≤ rootedRealParityMass ρ 0 then 0 else 1

/-- The nonzero bounded-face charges in the heavier parity class. -/
def rootedRealBaseSites (ρ : RotatorDualFace L → ℝ) : Finset (SquareFreeVertex L) := by
  classical
  exact Finset.univ.filter fun x => ρ (some x) ≠ 0 ∧
    (x.1.val + x.2.val) % 2 = rootedRealBaseParity ρ

/-- An integer sign with the sign of a real charge. -/
def rootedRealSignInt (q : ℝ) : ℤ :=
  if 0 < q then 1 else if q < 0 then -1 else 0

/-- A doubled sign bump on one bounded face, expressed using the pinned layer base-piece API. -/
def rootedRealBasePiece (ρ : RotatorDualFace L → ℝ) (x : SquareFreeVertex L) :
    RotatorDualFace L → ℝ :=
  basePiece (fun j => if j = some x then rootedRealSignInt (ρ (some x)) else 0) x

/-- The doubled bumps on the selected face parity carry at least half of the full `ℓ¹` mass of
any neutral real source on the rooted carrier. -/
theorem half_mass_le_rootedRealBase (ρ : RotatorDualFace L → ℝ)
    (hsum : ∑ j, ρ j = 0) :
    (1 / 2 : ℝ) * ∑ j, |ρ j| ≤
      ∑ x ∈ rootedRealBaseSites ρ, 2 * |ρ (some x)| := by
  classical
  let faceMass : ℝ := ∑ x : SquareFreeVertex L, |ρ (some x)|
  let faceSum : ℝ := ∑ x : SquareFreeVertex L, ρ (some x)
  have hroot : ρ none = -faceSum := by
    have h := hsum
    rw [Fintype.sum_option] at h
    dsimp [faceSum]
    linarith
  have hrootBound : |ρ none| ≤ faceMass := by
    rw [hroot, abs_neg]
    simpa [faceSum, faceMass] using (Finset.abs_sum_le_sum_abs _ _)
  have hfull : ∑ j, |ρ j| ≤ 2 * faceMass := by
    rw [Fintype.sum_option]
    dsimp [faceMass]
    linarith
  have hsplit : faceMass = rootedRealParityMass ρ 0 + rootedRealParityMass ρ 1 := by
    dsimp [faceMass, rootedRealParityMass]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rcases Nat.mod_two_eq_zero_or_one (x.1.val + x.2.val) with h | h <;> simp [h]
  have hsites :
      (∑ x ∈ rootedRealBaseSites ρ, |ρ (some x)|) =
        rootedRealParityMass ρ (rootedRealBaseParity ρ) := by
    unfold rootedRealBaseSites rootedRealParityMass
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hx : ρ (some x) = 0 <;> simp [hx]
  have hheavy : rootedRealParityMass ρ 0 + rootedRealParityMass ρ 1 ≤
      2 * rootedRealParityMass ρ (rootedRealBaseParity ρ) := by
    unfold rootedRealBaseParity
    split_ifs <;> linarith
  have hbase : faceMass ≤
      2 * ∑ x ∈ rootedRealBaseSites ρ, |ρ (some x)| := by
    rw [hsplit, hsites]
    exact hheavy
  calc
    (1 / 2 : ℝ) * ∑ j, |ρ j| ≤ (1 / 2) * (2 * faceMass) :=
      mul_le_mul_of_nonneg_left hfull (by norm_num)
    _ = faceMass := by ring
    _ ≤ 2 * ∑ x ∈ rootedRealBaseSites ρ, |ρ (some x)| := hbase
    _ = ∑ x ∈ rootedRealBaseSites ρ, 2 * |ρ (some x)| := by rw [← Finset.mul_sum]

/-- The real marked bump pairs with its source as twice the absolute charge at its face. -/
theorem pairing_rootedRealBasePiece (ρ : RotatorDualFace L → ℝ)
    {x : SquareFreeVertex L}
    (hx : ρ (some x) ≠ 0) :
    Multigraph.pairing (rootedRealBasePiece ρ x) ρ = 2 * |ρ (some x)| := by
  classical
  have hsign : signUnit (rootedRealSignInt (ρ (some x))) * ρ (some x) =
      |ρ (some x)| := by
    rcases lt_trichotomy (ρ (some x)) 0 with hneg | hz | hpos
    · have hnotpos : ¬ 0 < ρ (some x) := not_lt.mpr (le_of_lt hneg)
      simp [rootedRealSignInt, signUnit, hneg, hnotpos, abs_of_neg hneg]
    · exact (hx hz).elim
    · norm_num [rootedRealSignInt, signUnit, hpos, abs_of_pos hpos]
  unfold Multigraph.pairing rootedRealBasePiece basePiece
  dsimp
  rw [Finset.sum_eq_single (some x)]
  · simp only [ite_true]
    calc
      2 * signUnit (rootedRealSignInt (ρ (some x))) * ρ (some x) =
          2 * (signUnit (rootedRealSignInt (ρ (some x))) * ρ (some x)) := by ring
      _ = 2 * |ρ (some x)| := by rw [hsign]
  · intro j _ hj
    simp [hj]
  · simp

/-- A real marked bump is supported away from the wired root. -/
theorem rootedRealBasePiece_root (ρ : RotatorDualFace L → ℝ)
    (x : SquareFreeVertex L) :
    rootedRealBasePiece ρ x none = 0 := by
  simp [rootedRealBasePiece, basePiece]

/-- The gradient of a real marked bump is bounded by two. -/
theorem abs_grad_rootedRealBasePiece_le (ρ : RotatorDualFace L → ℝ)
    (x : SquareFreeVertex L)
    (e : FroehlichSpencer.BKT.Generic.PinnedCharges.SquareZeroBond L) :
    |(squareZero L).grad (rootedRealBasePiece ρ x) e| ≤ 2 := by
  let q : RotatorDualFace L → ℤ := fun j =>
    if j = some x then rootedRealSignInt (ρ (some x)) else 0
  have h := abs_grad_basePiece_le q x e
  simpa [rootedRealBasePiece, q] using h

/-- A real marked bump has energy at most sixteen, uniformly up to the boundary. -/
theorem energy_rootedRealBasePiece_le (ρ : RotatorDualFace L → ℝ)
    (x : SquareFreeVertex L) :
    (squareZero L).energy (rootedRealBasePiece ρ x) ≤ 16 := by
  let q : RotatorDualFace L → ℤ := fun j =>
    if j = some x then rootedRealSignInt (ρ (some x)) else 0
  have h := energy_basePiece_le q x
  simpa [rootedRealBasePiece, q] using h

/-- Nonzero gradients of bumps at distinct faces force those faces to be adjacent in the bounded
square. -/
theorem l1_eq_one_of_grad_rootedRealBasePiece
    {ρ σ : RotatorDualFace L → ℝ} {x y : SquareFreeVertex L} (hne : x ≠ y)
    {e : FroehlichSpencer.BKT.Generic.PinnedCharges.SquareZeroBond L}
    (hx : (squareZero L).grad (rootedRealBasePiece ρ x) e ≠ 0)
    (hy : (squareZero L).grad (rootedRealBasePiece σ y) e ≠ 0) :
    l1 x y = 1 := by
  let qx : RotatorDualFace L → ℤ := fun j =>
    if j = some x then rootedRealSignInt (ρ (some x)) else 0
  let qy : RotatorDualFace L → ℤ := fun j =>
    if j = some y then rootedRealSignInt (σ (some y)) else 0
  have h := l1_eq_one_of_grad_basePiece (ϱ := qx) (ϱ' := qy) hne
    (by simpa [rootedRealBasePiece, qx] using hx)
    (by simpa [rootedRealBasePiece, qy] using hy)
  exact h

/-- Two bumps chosen from the same bounded-face parity have disjoint gradients. -/
theorem grad_rootedRealBasePiece_disjoint_of_sameParity
    {ρ σ : RotatorDualFace L → ℝ} {x y : SquareFreeVertex L} (hne : x ≠ y)
    (hpar : (x.1.val + x.2.val) % 2 = (y.1.val + y.2.val) % 2)
    (e : FroehlichSpencer.BKT.Generic.PinnedCharges.SquareZeroBond L) :
    (squareZero L).grad (rootedRealBasePiece ρ x) e = 0 ∨
      (squareZero L).grad (rootedRealBasePiece σ y) e = 0 := by
  by_contra h
  push Not at h
  obtain ⟨hx, hy⟩ := h
  have hdist := l1_eq_one_of_grad_rootedRealBasePiece hne hx hy
  have hpar' : (x.1.val + x.2.val) % 2 ≠ (y.1.val + y.2.val) % 2 := by
    unfold l1 at hdist
    omega
  exact hpar' hpar

end FroehlichSpencer.BKT.VillainDisorder.Dirichlet

end
