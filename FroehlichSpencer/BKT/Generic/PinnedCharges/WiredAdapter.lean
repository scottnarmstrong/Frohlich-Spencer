/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Rotator.FreeBox
public import FroehlichSpencer.BKT.Bridge.WiredBoxCarrier
public import FroehlichSpencer.BKT.Bridge.WiredVillainModel
public import FroehlichSpencer.BKT.Surface.SquareZeroConnected
public import FroehlichSpencer.BKT.Generic.EdgeLaw.Defs
public import FroehlichSpencer.BKT.Generic.PinnedCharges.Geometry

/-!
# The wired exterior adapter for pinned rotator fields

The dual face carrier in `Rotator.FreeBox` is the vertex carrier of the `squareZero`
multigraph.

Its boundary edge multiplicities are exactly the dual edges crossing the box boundary.

This file records the two finite-dimensional adapters needed to use that carrier: pin a field by
setting the wired vertex to zero, and neutralize a pinned charge by placing its negative total at
the wired vertex.

The latter makes its character invariant under the common root phase of the
rooted edge law.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic.PinnedCharges

open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Duality
open FroehlichSpencer.BKT.Rotator
open FroehlichSpencer.BKT.Rotator.Contour

variable {L : ℕ}

/-- A bounded-face field extended by zero to the exterior face. -/
def zeroExtendFaceField (φ : Fin L × Fin L → ℝ) : RotatorDualFace L → ℝ
  | none => 0
  | some x => φ x

/-- A pinned field read as differences from the wired root of an unrestricted field. -/
def relativeToWiredRoot (θ : RotatorDualFace L → ℝ) : Fin L × Fin L → ℝ :=
  fun x => θ (some x) - θ none

/-- The compensating integer charge at the wired exterior vertex. -/
def neutralizeAtWiredRoot (q : (Fin L × Fin L) → ℤ) : RotatorDualFace L → ℤ
  | none => -∑ x, q x
  | some x => q x

@[simp] theorem zeroExtendFaceField_none (φ : Fin L × Fin L → ℝ) :
    zeroExtendFaceField φ none = 0 := rfl

@[simp] theorem zeroExtendFaceField_some (φ : Fin L × Fin L → ℝ) (x : Fin L × Fin L) :
    zeroExtendFaceField φ (some x) = φ x := rfl

@[simp] theorem neutralizeAtWiredRoot_none (q : (Fin L × Fin L) → ℤ) :
    neutralizeAtWiredRoot q none = -∑ x, q x := rfl

@[simp] theorem neutralizeAtWiredRoot_some (q : (Fin L × Fin L) → ℤ)
    (x : Fin L × Fin L) : neutralizeAtWiredRoot q (some x) = q x := rfl

/-- Every pinned charge becomes neutral after adding the compensating wired charge. -/
theorem sum_neutralizeAtWiredRoot (q : (Fin L × Fin L) → ℤ) :
    ∑ x : RotatorDualFace L, neutralizeAtWiredRoot q x = 0 := by
  classical
  simp [neutralizeAtWiredRoot, Fintype.sum_option]

/-- The rooted character of the neutralized charge is exactly the pinned character of the
root-relative field. -/
theorem pairing_neutralizeAtWiredRoot (q : (Fin L × Fin L) → ℤ)
    (θ : RotatorDualFace L → ℝ) :
    ∑ x : RotatorDualFace L, θ x * (neutralizeAtWiredRoot q x : ℝ) =
      ∑ x, relativeToWiredRoot θ x * (q x : ℝ) := by
  classical
  rw [Fintype.sum_option]
  simp only [neutralizeAtWiredRoot, Int.cast_neg, Int.cast_sum]
  simp only [relativeToWiredRoot]
  simp only [sub_mul]
  rw [Finset.sum_sub_distrib]
  rw [← Finset.mul_sum]
  ring

/--
The rooted and pinned carrier are the same graph after the edge reindexing: the
`squareZero` vertices are definitionally the free-box dual faces, and the graph isomorphism
preserves every edge, including all parallel exterior incidences.
-/
noncomputable def squareZero_dualFace_carrier_isomorphism (L : ℕ) :
    Multigraph.Isomorphism (squareZero L) (rotatorDualGraph L) := by
  exact squareZeroWiredBoxGraphIsomorphism L

abbrev SquareZeroBond (L : ℕ) := SquareFreeEdge L ⊕ SquareZeroBoundaryIndex L

/-- Under the carrier isomorphism, an individual dual gradient agrees with the source gradient
or its negative according to the endpoint orientation. -/
theorem squareZero_gradient_transport (f : RotatorDualFace L → ℝ)
    (e : SquareZeroBond L) :
    (rotatorDualGraph L).grad
        ((squareZero_dualFace_carrier_isomorphism L).pushField f)
        ((squareZero_dualFace_carrier_isomorphism L).edges e) =
      (squareZero L).grad f e ∨
    (rotatorDualGraph L).grad
        ((squareZero_dualFace_carrier_isomorphism L).pushField f)
        ((squareZero_dualFace_carrier_isomorphism L).edges e) =
      -((squareZero L).grad f e) := by
  rcases (squareZero_dualFace_carrier_isomorphism L).endpoints e with ⟨hs, ht⟩ | ⟨hs, ht⟩
  · left
    simp [Multigraph.grad, Multigraph.Isomorphism.pushField, hs, ht]
  · right
    simp [Multigraph.grad, Multigraph.Isomorphism.pushField, hs, ht]

/-- The pinned graph obtained by orienting every wired edge from its free endpoint toward the
exterior. If the source orientation points from the exterior, this reverses that edge. -/
def squareZeroPinnedGraph (L : ℕ) :
    PinnedGraph (Fin L × Fin L) (SquareZeroBond L) where
  head e := by
    classical
    by_cases hs : (squareZero L).src e = none
    · exact ((squareZero L).tgt e).get (by
        cases ht : (squareZero L).tgt e with
        | none => exact False.elim ((squareZero L).src_ne_tgt e (hs.trans ht.symm))
        | some _ => rfl)
    · exact ((squareZero L).src e).get (by
        cases ht : (squareZero L).src e with
        | none => exact False.elim (hs ht)
        | some _ => rfl)
  tail e := if (squareZero L).src e = none then none else (squareZero L).tgt e
  pin := fun _ => 0

/-- On every edge the pinned gradient is the wired graph gradient, up to the orientation sign. -/
theorem squareZeroPinnedGraph_realGrad_eq (φ : Fin L × Fin L → ℝ)
    (e : SquareZeroBond L) :
    (squareZeroPinnedGraph L).realGrad φ e =
      if (squareZero L).src e = none then
        -((squareZero L).grad (zeroExtendFaceField φ) e)
      else (squareZero L).grad (zeroExtendFaceField φ) e := by
  classical
  cases hs : (squareZero L).src e with
  | none =>
      cases ht : (squareZero L).tgt e with
      | none => exact False.elim ((squareZero L).src_ne_tgt e (hs.trans ht.symm))
      | some y => simp [squareZeroPinnedGraph, PinnedGraph.realGrad,
          Multigraph.grad, zeroExtendFaceField, hs, ht]
  | some x =>
      cases ht : (squareZero L).tgt e with
      | none => simp [squareZeroPinnedGraph, PinnedGraph.realGrad,
          Multigraph.grad, zeroExtendFaceField, hs, ht]
      | some y => simp [squareZeroPinnedGraph, PinnedGraph.realGrad,
          Multigraph.grad, zeroExtendFaceField, hs, ht]

/-- On every edge the pinned gradient has the same magnitude as the wired graph gradient. -/
theorem squareZeroPinnedGraph_realGrad_abs (φ : Fin L × Fin L → ℝ)
    (e : SquareZeroBond L) :
    |(squareZeroPinnedGraph L).realGrad φ e| =
      |(squareZero L).grad (zeroExtendFaceField φ) e| := by
  rw [squareZeroPinnedGraph_realGrad_eq]
  split_ifs <;> simp

/-- The free-box height current is the oriented gradient of its zero-exterior dual-face height.
This equality uses the Appendix A source orientation verbatim. -/
theorem rotatorFaceHeightCurrent_eq_sourceGradient (h : RotatorFaceHeight L)
    (e : RotatorInternalBond L) :
    rotatorFaceHeightCurrent h e = (rotatorDualGraph L).grad h.1 e := rfl

/-- The absolute pinned gradient on the bounded faces is precisely the absolute gradient on the
augmented `squareZero` graph after extension by zero. -/
theorem squareZeroPinnedGradient_eq_faceGradient_abs (φ : Fin L × Fin L → ℝ)
    (e : SquareZeroBond L) :
    |(squareZeroPinnedGraph L).realGrad φ e| =
      |(rotatorDualGraph L).grad (zeroExtendFaceField φ)
        ((squareZero_dualFace_carrier_isomorphism L).edges e)| := by
  have h := squareZero_gradient_transport (L := L) (zeroExtendFaceField φ) e
  have habs := squareZeroPinnedGraph_realGrad_abs (L := L) φ e
  rw [habs]
  have hp : (squareZero_dualFace_carrier_isomorphism L).pushField
      (zeroExtendFaceField φ) = zeroExtendFaceField φ := by
    funext x
    rfl
  rw [hp] at h
  rcases h with h | h
  · simp [h]
  · simp [h, abs_neg]

/-- The distance from a bounded face to the wired exterior is exactly its distance to the
complementary square boundary in the pinned carrier's site convention. -/
theorem squareZero_distance_root_eq_siteBoundaryDepth (hL : 1 < L)
    (x : Fin L × Fin L) :
    (squareZero L).toSimpleGraph.dist (some x) none = siteBoundaryDepth x := by
  rw [Duality.squareZero_dist_root_eq L hL x]
  have hdepth : wiredBoundaryDepth L x + 1 = siteBoundaryDepth x := by
    simp only [wiredBoundaryDepth, siteBoundaryDepth]
    omega
  exact hdepth

/-- The wired exterior creates graph-metric shortcuts between remote boundary faces: opposite
corners of the box are at graph distance at most two, via `none`. This is why Euclidean support
separation in Appendix D cannot be silently read as distance in `squareZero`. -/
theorem squareZero_oppositeCorner_distance_le_two (hL : 3 ≤ L) :
    (squareZero L).toSimpleGraph.dist
      (some ((⟨0, by omega⟩ : Fin L), (⟨0, by omega⟩ : Fin L)))
      (some ((⟨L - 1, by omega⟩ : Fin L), (⟨L - 1, by omega⟩ : Fin L))) ≤ 2 := by
  let x : Fin L × Fin L := (⟨0, by omega⟩, ⟨0, by omega⟩)
  let y : Fin L × Fin L := (⟨L - 1, by omega⟩, ⟨L - 1, by omega⟩)
  have hG : (squareZero L).toSimpleGraph.Connected := squareZero_connected L (by omega)
  have hxdepth : siteBoundaryDepth x = 1 := by
    simp [x, siteBoundaryDepth]
    omega
  have hydepth : siteBoundaryDepth y = 1 := by
    simp [y, siteBoundaryDepth]
    omega
  have hx : (squareZero L).toSimpleGraph.dist (some x) none = 1 := by
    rw [squareZero_distance_root_eq_siteBoundaryDepth (by omega) x, hxdepth]
  have hy : (squareZero L).toSimpleGraph.dist (some y) none = 1 := by
    rw [squareZero_distance_root_eq_siteBoundaryDepth (by omega) y, hydepth]
  have hy' : (squareZero L).toSimpleGraph.dist none (some y) = 1 := by
    rw [SimpleGraph.dist_comm]
    exact hy
  have htri := hG.dist_triangle (u := some x) (v := none) (w := some y)
  simpa [x, y, hx, hy'] using htri

/-- The same opposite corners have Euclidean separation growing linearly with the box side. -/
theorem euclideanSiteDistance_oppositeCorners (hL : 3 ≤ L) :
    euclideanSiteDistance
      ((⟨0, by omega⟩ : Fin L), (⟨0, by omega⟩ : Fin L))
      ((⟨L - 1, by omega⟩ : Fin L), (⟨L - 1, by omega⟩ : Fin L)) =
      Real.sqrt (2 * ((L - 1 : ℕ) : ℝ) ^ 2) := by
  unfold euclideanSiteDistance
  congr 1
  norm_num
  ring

end FroehlichSpencer.BKT.Generic.PinnedCharges

end
