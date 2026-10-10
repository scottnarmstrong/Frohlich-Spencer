/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.PinnedCharges.TerminalProfileGSplit
public import FroehlichSpencer.BKT.Generic.PinnedCharges.BoundaryEnergyOverlap
public import FroehlichSpencer.BKT.Generic.PinnedCharges.BoundaryEnergyPairing

/-!
# Lattice and density geometry for the terminal profiles

* lattice steps: `l1 ≤ (3/2)·eucl`, a step towards a target that does not increase the Euclidean
  distance to it, and the two propagation principles along such steps: a real potential that is
  1-Lipschitz on lattice steps satisfies `f x ≤ f y + l1 x y`
  (`le_add_l1_of_lipschitz`), and a potential constant on the steps inside a set containing a
  Euclidean ball is constant on the ball (`eq_of_steps_in_ball`);
* boundary depth: it is 1-Lipschitz for the Euclidean distance (`depth_le_add_siteDist`), a
  charged density lies within depth `2 d_Λ` (`depth_le_two_boundaryAdjustedSize`), and a
  `squareZero` edge to the wired root starts at depth one (`depth_le_one_of_root_edge`);
* the wired graph distance between bounded faces is at least `min(l1, depth + depth)`
  (`min_l1_depth_le_dist`).
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic.PinnedCharges.Layer

open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Rotator
open FroehlichSpencer.BKT.Generic.PinnedCharges.SelectionG

variable {L : ℕ}

/-! ## Lattice steps -/

/-- `ℓ¹ ≤ (3/2) ℓ²` on the lattice (`√2 < 3/2`). -/
theorem l1_le_three_halves_siteDist (x y : Site L) :
    (l1 x y : ℝ) ≤ 3 / 2 * euclideanSiteDistance x y := by
  unfold euclideanSiteDistance l1
  push_cast
  rw [Nat.cast_natAbs, Nat.cast_natAbs]
  push_cast
  set a : ℝ := (x.1.val : ℝ) - y.1.val
  set b : ℝ := (x.2.val : ℝ) - y.2.val
  have h : (|a| + |b|) ^ 2 ≤ 9 / 4 * (a ^ 2 + b ^ 2) := by
    nlinarith [sq_abs a, sq_abs b, sq_nonneg (|a| - |b|)]
  calc |a| + |b| = Real.sqrt ((|a| + |b|) ^ 2) := (Real.sqrt_sq (by positivity)).symm
    _ ≤ Real.sqrt (9 / 4 * (a ^ 2 + b ^ 2)) := Real.sqrt_le_sqrt h
    _ = 3 / 2 * Real.sqrt (a ^ 2 + b ^ 2) := by
      rw [Real.sqrt_mul (by norm_num), show (9 / 4 : ℝ) = (3 / 2) ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num)]

/-- Coordinatewise closer is Euclidean closer. -/
theorem siteDist_le_of_coord {x y z : Site L}
    (h1 : |(z.1.val : ℝ) - y.1.val| ≤ |(x.1.val : ℝ) - y.1.val|)
    (h2 : |(z.2.val : ℝ) - y.2.val| ≤ |(x.2.val : ℝ) - y.2.val|) :
    euclideanSiteDistance z y ≤ euclideanSiteDistance x y := by
  unfold euclideanSiteDistance
  apply Real.sqrt_le_sqrt
  have e1 := pow_le_pow_left₀ (abs_nonneg _) h1 2
  have e2 := pow_le_pow_left₀ (abs_nonneg _) h2 2
  rw [sq_abs, sq_abs] at e1 e2
  linarith

/-- **A step towards a target**: a lattice neighbour one `ℓ¹` unit closer and not farther in the
Euclidean distance. -/
theorem exists_step_toward {x y : Site L} (hxy : x ≠ y) :
    ∃ z : Site L, l1 x z = 1 ∧ l1 z y + 1 = l1 x y ∧
      euclideanSiteDistance z y ≤ euclideanSiteDistance x y := by
  rcases lt_trichotomy x.1.val y.1.val with h | h | h
  · refine ⟨(⟨x.1.val + 1, by omega⟩, x.2), ?_, ?_, ?_⟩
    · unfold l1; simp only; omega
    · unfold l1; simp only; omega
    · refine siteDist_le_of_coord ?_ le_rfl
      simp only
      have : (x.1.val : ℝ) + 1 ≤ y.1.val := by exact_mod_cast h
      push_cast
      rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
      linarith
  · have h2 : x.2.val ≠ y.2.val := fun h2 => hxy (Prod.ext (Fin.ext h) (Fin.ext h2))
    rcases Nat.lt_or_gt_of_ne h2 with h2 | h2
    · refine ⟨(x.1, ⟨x.2.val + 1, by omega⟩), ?_, ?_, ?_⟩
      · unfold l1; simp only; omega
      · unfold l1; simp only; omega
      · refine siteDist_le_of_coord le_rfl ?_
        simp only
        have : (x.2.val : ℝ) + 1 ≤ y.2.val := by exact_mod_cast h2
        push_cast
        rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
        linarith
    · refine ⟨(x.1, ⟨x.2.val - 1, by omega⟩), ?_, ?_, ?_⟩
      · unfold l1; simp only; omega
      · unfold l1; simp only; omega
      · refine siteDist_le_of_coord le_rfl ?_
        simp only
        have : (y.2.val : ℝ) + 1 ≤ x.2.val := by exact_mod_cast h2
        rw [Nat.cast_sub (by omega)]
        push_cast
        rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
        linarith
  · refine ⟨(⟨x.1.val - 1, by omega⟩, x.2), ?_, ?_, ?_⟩
    · unfold l1; simp only; omega
    · unfold l1; simp only; omega
    · refine siteDist_le_of_coord ?_ le_rfl
      simp only
      have : (y.1.val : ℝ) + 1 ≤ x.1.val := by exact_mod_cast h
      rw [Nat.cast_sub (by omega)]
      push_cast
      rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
      linarith

/-- **Lipschitz propagation**: a potential that grows by at most one per lattice step grows by at
most the `ℓ¹` distance. -/
theorem le_add_l1_of_lipschitz {f : Site L → ℝ} (hf : ∀ x y : Site L, l1 x y = 1 → f x ≤ f y + 1)
    (x y : Site L) : f x ≤ f y + l1 x y := by
  induction h : l1 x y using Nat.strong_induction_on generalizing x with
  | _ n ih =>
    by_cases hxy : x = y
    · subst hxy; simp
    · obtain ⟨z, hxz, hzy, -⟩ := exists_step_toward hxy
      have h1 := hf x z hxz
      have h2 := ih (l1 z y) (by omega) z rfl
      have h3 : ((l1 z y : ℕ) : ℝ) + 1 = n := by rw [← h, ← hzy]; push_cast; ring
      linarith

/-- **Constancy on a ball**: a potential constant across every lattice step inside `E` is constant
on every Euclidean ball about `y` contained in `E`. -/
theorem eq_of_steps_in_ball {β : Type*} {f : Site L → β} {E : Finset (Site L)}
    (hE : ∀ x ∈ E, ∀ y ∈ E, l1 x y = 1 → f x = f y) {y : Site L} {r : ℝ}
    (hball : ∀ z : Site L, euclideanSiteDistance z y ≤ r → z ∈ E) (x : Site L)
    (hx : euclideanSiteDistance x y ≤ r) : f x = f y := by
  induction h : l1 x y using Nat.strong_induction_on generalizing x with
  | _ n ih =>
    by_cases hxy : x = y
    · rw [hxy]
    · obtain ⟨z, hxz, hzy, hdist⟩ := exists_step_toward hxy
      rw [hE x (hball x hx) z (hball z (hdist.trans hx)) hxz]
      exact ih (l1 z y) (by omega) z (hdist.trans hx) rfl

/-! ## Boundary depth -/

/-- The boundary depth is 1-Lipschitz for the Euclidean distance. -/
theorem depth_le_add_siteDist (x y : Site L) :
    (siteBoundaryDepth x : ℝ) ≤ siteBoundaryDepth y + euclideanSiteDistance x y := by
  have a1 := abs_le.mp (abs_fst_le_siteDist x y)
  have a2 := abs_le.mp (abs_snd_le_siteDist x y)
  have hx1 := x.1.isLt
  have hx2 := x.2.isLt
  have hy1 := y.1.isLt
  have hy2 := y.2.isLt
  have dx₁ : (siteBoundaryDepth x : ℝ) ≤ x.1.val + 1 := by
    have : siteBoundaryDepth x ≤ x.1.val + 1 := by unfold siteBoundaryDepth; omega
    exact_mod_cast this
  have dx₂ : (siteBoundaryDepth x : ℝ) ≤ (L : ℝ) - x.1.val := by
    have : siteBoundaryDepth x ≤ L - x.1.val := by unfold siteBoundaryDepth; omega
    have h := (Nat.cast_le (α := ℝ)).mpr this
    rwa [Nat.cast_sub hx1.le] at h
  have dx₃ : (siteBoundaryDepth x : ℝ) ≤ x.2.val + 1 := by
    have : siteBoundaryDepth x ≤ x.2.val + 1 := by unfold siteBoundaryDepth; omega
    exact_mod_cast this
  have dx₄ : (siteBoundaryDepth x : ℝ) ≤ (L : ℝ) - x.2.val := by
    have : siteBoundaryDepth x ≤ L - x.2.val := by unfold siteBoundaryDepth; omega
    have h := (Nat.cast_le (α := ℝ)).mpr this
    rwa [Nat.cast_sub hx2.le] at h
  have hy : siteBoundaryDepth y = y.1.val + 1 ∨ siteBoundaryDepth y = L - y.1.val ∨
      siteBoundaryDepth y = y.2.val + 1 ∨ siteBoundaryDepth y = L - y.2.val := by
    unfold siteBoundaryDepth; omega
  rcases hy with h | h | h | h <;> rw [h] <;> push_cast
  · linarith
  · rw [Nat.cast_sub hy1.le]; linarith
  · linarith
  · rw [Nat.cast_sub hy2.le]; linarith

/-- The support-to-boundary distance is attained. -/
theorem exists_depth_eq_chargeBoundaryDistance {τ : ChargeDensity L} (hτ : τ ≠ 0) :
    ∃ y ∈ chargeSupport τ, (siteBoundaryDepth y : ℝ) = chargeBoundaryDistance τ := by
  have hne := chargeSupport_nonempty_of_ne_zero τ hτ
  unfold chargeBoundaryDistance euclideanBoundaryDistance
  rw [dite_eq_left hne]
  obtain ⟨y, hy, hyeq⟩ := Finset.mem_image.mp (Finset.min'_mem ((chargeSupport τ).image
    fun x => (siteBoundaryDepth x : ℝ)) (Finset.image_nonempty.mpr hne))
  exact ⟨y, hy, hyeq⟩

/-- A charged density lies within boundary depth `2 d_Λ`. -/
theorem depth_le_two_boundaryAdjustedSize {τ : ChargeDensity L} (hq : totalCharge τ ≠ 0)
    {x : Site L} (hx : x ∈ chargeSupport τ) :
    (siteBoundaryDepth x : ℝ) ≤ 2 * boundaryAdjustedSize τ := by
  have hτ : τ ≠ 0 := fun h => hq (by simp [h, totalCharge])
  obtain ⟨y, hy, hyeq⟩ := exists_depth_eq_chargeBoundaryDistance hτ
  have h1 := depth_le_add_siteDist x y
  have h2 : euclideanSiteDistance x y ≤ chargeEuclideanDiameter τ := siteDist_le_diam hx hy
  rw [boundaryAdjustedSize_of_charged τ hq]
  have h3 := le_max_left (chargeBoundaryDistance τ) (chargeEuclideanDiameter τ)
  have h4 := le_max_right (chargeBoundaryDistance τ) (chargeEuclideanDiameter τ)
  linarith

/-- A `squareZero` edge into the wired root starts at boundary depth one. -/
theorem depth_le_one_of_root_edge (hL : 1 < L) {e : SquareZeroBond L} {x : Site L}
    (hs : (squareZero L).src e = some x) (ht : (squareZero L).tgt e = none) :
    siteBoundaryDepth x ≤ 1 := by
  have hadj : (squareZero L).toSimpleGraph.Adj (some x) none := by
    rw [Multigraph.toSimpleGraph, SimpleGraph.fromRel_adj]
    exact ⟨by simp, Or.inl ⟨e, Or.inl ⟨hs, ht⟩⟩⟩
  rw [← squareZero_distance_root_eq_siteBoundaryDepth hL, SimpleGraph.dist_eq_one_iff_adj.mpr hadj]

/-! ## The wired graph distance -/

/-- A wired geodesic between bounded faces avoids the root (length `≥ ℓ¹`) or passes it (length
`≥ depth + depth`). -/
theorem min_l1_depth_le_dist (hL : 1 < L) (x y : Site L) :
    min (l1 x y) (siteBoundaryDepth x + siteBoundaryDepth y) ≤
      (squareZero L).toSimpleGraph.dist (some x) (some y) := by
  classical
  obtain ⟨w, hw⟩ :=
    ((squareZero_connected L hL).preconnected (some x) (some y)).exists_walk_length_eq_dist
  rw [← hw]
  by_cases hn : none ∈ w.support
  · have hspec : (w.takeUntil none hn).append (w.dropUntil none hn) = w := w.take_spec hn
    have hlen : (w.takeUntil none hn).length + (w.dropUntil none hn).length = w.length := by
      rw [← SimpleGraph.Walk.length_append, hspec]
    have h1 : siteBoundaryDepth x ≤ (w.takeUntil none hn).length := by
      rw [← squareZero_distance_root_eq_siteBoundaryDepth hL]
      exact SimpleGraph.dist_le _
    have h2 : siteBoundaryDepth y ≤ (w.dropUntil none hn).length := by
      rw [← squareZero_distance_root_eq_siteBoundaryDepth hL, SimpleGraph.dist_comm]
      exact SimpleGraph.dist_le _
    omega
  · exact (min_le_left _ _).trans (l1_le_length_of_root_free w hn x y rfl rfl)

end FroehlichSpencer.BKT.Generic.PinnedCharges.Layer

end
