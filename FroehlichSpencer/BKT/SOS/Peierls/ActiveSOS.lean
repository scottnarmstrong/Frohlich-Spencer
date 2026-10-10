/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Clock.Peierls.ActiveContour
public import FroehlichSpencer.BKT.SOS.Peierls.RemovalEstimate
import Mathlib.Tactic

/-! # Active contours for integer SOS gradients -/

@[expose] public section

noncomputable section

open Classical
open scoped BigOperators

namespace FroehlichSpencer.BKT.SOS.Peierls

open FroehlichSpencer.BKT.Lattice2D
open FroehlichSpencer.BKT.Clock.Peierls
open FroehlichSpencer.BKT.Clock.Peierls.GenericGradient

/-- The five-segment detour flux above a horizontal path at height `y`. -/
def sosHorizontalDetourFluxUp {N : ℕ} (η : Lattice2D.SquareFreeEdge N → ℤ)
    (R j k y : ℕ) : ℤ :=
  squareFreeHorizontalSegmentSum η y 0 (j - (k + 3)) +
    squareFreeVerticalSegmentSum η (j - (k + 3)) y (k + 3) +
    squareFreeHorizontalSegmentSum η (y + (k + 3)) (j - (k + 3)) (2 * (k + 3)) -
    squareFreeVerticalSegmentSum η (j + (k + 3)) y (k + 3) +
    squareFreeHorizontalSegmentSum η y (j + (k + 3)) (R - (j + (k + 3)))

/-- The reflected five-segment detour flux below a horizontal path at height `y`. -/
def sosHorizontalDetourFluxDown {N : ℕ} (η : Lattice2D.SquareFreeEdge N → ℤ)
    (R j k y : ℕ) : ℤ :=
  squareFreeHorizontalSegmentSum η y 0 (j - (k + 3)) -
    squareFreeVerticalSegmentSum η (j - (k + 3)) (y - (k + 3)) (k + 3) +
    squareFreeHorizontalSegmentSum η (y - (k + 3)) (j - (k + 3)) (2 * (k + 3)) +
    squareFreeVerticalSegmentSum η (j + (k + 3)) (y - (k + 3)) (k + 3) +
    squareFreeHorizontalSegmentSum η y (j + (k + 3)) (R - (j + (k + 3)))

/-- A closed field has unchanged horizontal flux after detouring above a crossing edge. -/
theorem sosHorizontalSegmentSum_eq_detourUp {N : ℕ}
    (η : Lattice2D.SquareFreeEdge N → ℤ)
    (hclosed : GenericGradient.squareFreePlaquetteClosed η) (R j k y : ℕ)
    (hleft : k + 3 < j) (hright : k + 3 < R - j)
    (hR : R < N) (hy : y < N) (hheight : y + (k + 3) < N) :
    squareFreeHorizontalSegmentSum η y 0 R =
      sosHorizontalDetourFluxUp η R j k y := by
  obtain ⟨f, hf⟩ := squareFreeEdgeField_isGradient η hclosed
  have hη : η = (squareFreeGraph N).grad f := funext fun e => (hf e).symm
  rw [hη]
  unfold sosHorizontalDetourFluxUp
  rw [squareFreeHorizontalSegmentSum_grad f y 0 R hy (by omega),
    squareFreeHorizontalSegmentSum_grad f y 0 (j - (k + 3)) hy (by omega),
    squareFreeVerticalSegmentSum_grad f (j - (k + 3)) y (k + 3) (by omega) (by omega),
    squareFreeHorizontalSegmentSum_grad f (y + (k + 3)) (j - (k + 3))
      (2 * (k + 3)) (by omega) (by omega),
    squareFreeVerticalSegmentSum_grad f (j + (k + 3)) y (k + 3)
      (by omega) (by omega),
    squareFreeHorizontalSegmentSum_grad f y (j + (k + 3))
      (R - (j + (k + 3))) hy (by omega)]
  have hcross : j - (k + 3) + 2 * (k + 3) = j + (k + 3) := by omega
  have hend : j + (k + 3) + (R - (j + (k + 3))) = R := by omega
  simp only [Nat.zero_add, hcross, hend]
  abel

/-- A closed field has unchanged horizontal flux after detouring below a crossing edge. -/
theorem sosHorizontalSegmentSum_eq_detourDown {N : ℕ}
    (η : Lattice2D.SquareFreeEdge N → ℤ)
    (hclosed : GenericGradient.squareFreePlaquetteClosed η) (R j k y : ℕ)
    (hleft : k + 3 < j) (hright : k + 3 < R - j)
    (hR : R < N) (hy : y < N) (hheight : k + 3 < y) :
    squareFreeHorizontalSegmentSum η y 0 R =
      sosHorizontalDetourFluxDown η R j k y := by
  obtain ⟨f, hf⟩ := squareFreeEdgeField_isGradient η hclosed
  have hη : η = (squareFreeGraph N).grad f := funext fun e => (hf e).symm
  rw [hη]
  unfold sosHorizontalDetourFluxDown
  rw [squareFreeHorizontalSegmentSum_grad f y 0 R hy (by omega),
    squareFreeHorizontalSegmentSum_grad f y 0 (j - (k + 3)) hy (by omega),
    squareFreeVerticalSegmentSum_grad f (j - (k + 3)) (y - (k + 3))
      (k + 3) (by omega) (by omega),
    squareFreeHorizontalSegmentSum_grad f (y - (k + 3)) (j - (k + 3))
      (2 * (k + 3)) (by omega) (by omega),
    squareFreeVerticalSegmentSum_grad f (j + (k + 3)) (y - (k + 3))
      (k + 3) (by omega) (by omega),
    squareFreeHorizontalSegmentSum_grad f y (j + (k + 3))
      (R - (j + (k + 3))) hy (by omega)]
  have hcross : j - (k + 3) + 2 * (k + 3) = j + (k + 3) := by omega
  have hend : j + (k + 3) + (R - (j + (k + 3))) = R := by omega
  have hlow : y - (k + 3) + (k + 3) = y := by omega
  simp only [Nat.zero_add, hcross, hend, hlow]
  abel_nf

/-- Edge statement of the frame route above the row segment. -/
def sosHorizontalFrameUp (R j k y : ℕ) : Finset (ℕ × ℕ) :=
  clockPeierlsHorizontalFrameSegment y 0 (j - (k + 3)) ∪
    clockPeierlsVerticalFrameSegment (j - (k + 3)) y (y + (k + 3)) ∪
    clockPeierlsHorizontalFrameSegment (y + (k + 3)) (j - (k + 3)) (j + (k + 3)) ∪
    clockPeierlsVerticalFrameSegment (j + (k + 3)) y (y + (k + 3)) ∪
    clockPeierlsHorizontalFrameSegment y (j + (k + 3)) R

/-- Edge statement of the frame route below the row segment. -/
def sosHorizontalFrameDown (R j k y : ℕ) : Finset (ℕ × ℕ) :=
  clockPeierlsHorizontalFrameSegment y 0 (j - (k + 3)) ∪
    clockPeierlsVerticalFrameSegment (j - (k + 3)) (y - (k + 3)) y ∪
    clockPeierlsHorizontalFrameSegment (y - (k + 3)) (j - (k + 3)) (j + (k + 3)) ∪
    clockPeierlsVerticalFrameSegment (j + (k + 3)) (y - (k + 3)) y ∪
    clockPeierlsHorizontalFrameSegment y (j + (k + 3)) R

private theorem sosHorizontalFrameUp_row_ge (R j k y : ℕ) {p : ℕ × ℕ}
    (hp : p ∈ sosHorizontalFrameUp R j k y) : y ≤ p.2 := by
  have hp' :
      (∃ x ∈ Finset.Ico 0 (j - (k + 3)), (x, y) = p) ∨
      (∃ z ∈ Finset.Ico y (y + (k + 3)), (j - (k + 3), z) = p) ∨
      (∃ x ∈ Finset.Ico (j - (k + 3)) (j + (k + 3)),
        (x, y + (k + 3)) = p) ∨
      (∃ z ∈ Finset.Ico y (y + (k + 3)), (j + (k + 3), z) = p) ∨
      (∃ x ∈ Finset.Ico (j + (k + 3)) R, (x, y) = p) := by
    simpa [sosHorizontalFrameUp, clockPeierlsHorizontalFrameSegment,
      clockPeierlsVerticalFrameSegment, Finset.mem_union] using hp
  rcases hp' with hleft | hleftV | htop | hrightV | hright
  · rcases hleft with ⟨x, hx, rfl⟩
    exact Nat.le_refl _
  · rcases hleftV with ⟨z, hz, rfl⟩
    exact (Finset.mem_Ico.mp hz).1
  · rcases htop with ⟨x, hx, rfl⟩
    omega
  · rcases hrightV with ⟨z, hz, rfl⟩
    exact (Finset.mem_Ico.mp hz).1
  · rcases hright with ⟨x, hx, rfl⟩
    exact Nat.le_refl _

private theorem sosHorizontalFrameDown_row_le (R j k y : ℕ) {p : ℕ × ℕ}
    (hp : p ∈ sosHorizontalFrameDown R j k y) : p.2 ≤ y := by
  have hp' :
      (∃ x ∈ Finset.Ico 0 (j - (k + 3)), (x, y) = p) ∨
      (∃ z ∈ Finset.Ico (y - (k + 3)) y, (j - (k + 3), z) = p) ∨
      (∃ x ∈ Finset.Ico (j - (k + 3)) (j + (k + 3)),
        (x, y - (k + 3)) = p) ∨
      (∃ z ∈ Finset.Ico (y - (k + 3)) y, (j + (k + 3), z) = p) ∨
      (∃ x ∈ Finset.Ico (j + (k + 3)) R, (x, y) = p) := by
    simpa [sosHorizontalFrameDown, clockPeierlsHorizontalFrameSegment,
      clockPeierlsVerticalFrameSegment, Finset.mem_union] using hp
  rcases hp' with hleft | hleftV | hbottom | hrightV | hright
  · rcases hleft with ⟨x, hx, rfl⟩
    exact Nat.le_refl _
  · rcases hleftV with ⟨z, hz, rfl⟩
    exact (Finset.mem_Ico.mp hz).2.le
  · rcases hbottom with ⟨x, hx, rfl⟩
    omega
  · rcases hrightV with ⟨z, hz, rfl⟩
    exact (Finset.mem_Ico.mp hz).2.le
  · rcases hright with ⟨x, hx, rfl⟩
    exact Nat.le_refl _

private theorem sosHorizontalFrameUp_far (R j k y : ℕ)
    (hleft : k + 3 < j) (_hright : k + 3 < R - j) {p : ℕ × ℕ}
    (hp : p ∈ sosHorizontalFrameUp R j k y) :
    ¬ clockPeierlsCoordWithin p (j - 1, y) (k + 1) := by
  have hp' :
      (∃ x ∈ Finset.Ico 0 (j - (k + 3)), (x, y) = p) ∨
      (∃ z ∈ Finset.Ico y (y + (k + 3)), (j - (k + 3), z) = p) ∨
      (∃ x ∈ Finset.Ico (j - (k + 3)) (j + (k + 3)),
        (x, y + (k + 3)) = p) ∨
      (∃ z ∈ Finset.Ico y (y + (k + 3)), (j + (k + 3), z) = p) ∨
      (∃ x ∈ Finset.Ico (j + (k + 3)) R, (x, y) = p) := by
    simpa [sosHorizontalFrameUp, clockPeierlsHorizontalFrameSegment,
      clockPeierlsVerticalFrameSegment, Finset.mem_union] using hp
  intro hnear
  rcases hp' with hleft | hleftV | htop | hrightV | hright
  · rcases hleft with ⟨x, hx, rfl⟩
    rcases Finset.mem_Ico.mp hx with ⟨hx0, hxhi⟩
    dsimp [clockPeierlsCoordWithin] at hnear
    omega
  · rcases hleftV with ⟨z, hz, rfl⟩
    rcases Finset.mem_Ico.mp hz with ⟨hzlo, hzhi⟩
    dsimp [clockPeierlsCoordWithin] at hnear
    omega
  · rcases htop with ⟨x, hx, rfl⟩
    rcases Finset.mem_Ico.mp hx with ⟨hxlo, hxhi⟩
    dsimp [clockPeierlsCoordWithin] at hnear
    omega
  · rcases hrightV with ⟨z, hz, rfl⟩
    rcases Finset.mem_Ico.mp hz with ⟨hzlo, hzhi⟩
    dsimp [clockPeierlsCoordWithin] at hnear
    omega
  · rcases hright with ⟨x, hx, rfl⟩
    rcases Finset.mem_Ico.mp hx with ⟨hxlo, hxhi⟩
    dsimp [clockPeierlsCoordWithin] at hnear
    omega

private theorem sosHorizontalFrameDown_far (R j k y : ℕ)
    (hleft : k + 3 < j) (_hright : k + 3 < R - j)
    (hheight : k + 3 ≤ y) {p : ℕ × ℕ}
    (hp : p ∈ sosHorizontalFrameDown R j k y) :
    ¬ clockPeierlsCoordWithin p (j - 1, y) (k + 1) := by
  have hp' :
      (∃ x ∈ Finset.Ico 0 (j - (k + 3)), (x, y) = p) ∨
      (∃ z ∈ Finset.Ico (y - (k + 3)) y, (j - (k + 3), z) = p) ∨
      (∃ x ∈ Finset.Ico (j - (k + 3)) (j + (k + 3)),
        (x, y - (k + 3)) = p) ∨
      (∃ z ∈ Finset.Ico (y - (k + 3)) y, (j + (k + 3), z) = p) ∨
      (∃ x ∈ Finset.Ico (j + (k + 3)) R, (x, y) = p) := by
    simpa [sosHorizontalFrameDown, clockPeierlsHorizontalFrameSegment,
      clockPeierlsVerticalFrameSegment, Finset.mem_union] using hp
  intro hnear
  rcases hp' with hleft | hleftV | hbottom | hrightV | hright
  · rcases hleft with ⟨x, hx, rfl⟩
    rcases Finset.mem_Ico.mp hx with ⟨hx0, hxhi⟩
    dsimp [clockPeierlsCoordWithin] at hnear
    omega
  · rcases hleftV with ⟨z, hz, rfl⟩
    rcases Finset.mem_Ico.mp hz with ⟨hzlo, hzhi⟩
    dsimp [clockPeierlsCoordWithin] at hnear
    omega
  · rcases hbottom with ⟨x, hx, rfl⟩
    rcases Finset.mem_Ico.mp hx with ⟨hxlo, hxhi⟩
    dsimp [clockPeierlsCoordWithin] at hnear
    omega
  · rcases hrightV with ⟨z, hz, rfl⟩
    rcases Finset.mem_Ico.mp hz with ⟨hzlo, hzhi⟩
    dsimp [clockPeierlsCoordWithin] at hnear
    omega
  · rcases hright with ⟨x, hx, rfl⟩
    rcases Finset.mem_Ico.mp hx with ⟨hxlo, hxhi⟩
    dsimp [clockPeierlsCoordWithin] at hnear
    omega

/-- The positively oriented edge at a horizontal path index. -/
def sosHorizontalPathEdge {N R y : ℕ} (hR : R < N) (hy : y < N)
    (i : Fin R) : Lattice2D.SquareFreeEdge N :=
  GenericGradient.squareFreeHorizontalEdgeAt i.val y (by omega) hy

private def sosAnchorCoordUp {N : ℕ} (y : ℕ) (e : Lattice2D.SquareFreeEdge N) : ℕ × ℕ :=
  ((clockPeierlsEdgeAnchor e).1, (clockPeierlsEdgeAnchor e).2 - y)

private def sosAnchorCoordDown {N : ℕ} (y : ℕ) (e : Lattice2D.SquareFreeEdge N) : ℕ × ℕ :=
  ((clockPeierlsEdgeAnchor e).1, y - (clockPeierlsEdgeAnchor e).2)

private theorem sosAnchorCoordUp_step {N y : ℕ} {e f : Lattice2D.SquareFreeEdge N}
    (hef : (clockPeierlsAdjacencyGraph N).Adj e f) :
    clockPeierlsCoordWithin (sosAnchorCoordUp y e) (sosAnchorCoordUp y f) 1 := by
  rcases clockPeierlsAdjacencyGraph_anchor_step hef with ⟨h₁, h₂, h₃, h₄⟩
  dsimp [clockPeierlsCoordWithin, sosAnchorCoordUp]
  exact ⟨h₁, h₂, by omega, by omega⟩

private theorem sosAnchorCoordDown_step {N y : ℕ} {e f : Lattice2D.SquareFreeEdge N}
    (hef : (clockPeierlsAdjacencyGraph N).Adj e f) :
    clockPeierlsCoordWithin (sosAnchorCoordDown y e) (sosAnchorCoordDown y f) 1 := by
  rcases clockPeierlsAdjacencyGraph_anchor_step hef with ⟨h₁, h₂, h₃, h₄⟩
  dsimp [clockPeierlsCoordWithin, sosAnchorCoordDown]
  exact ⟨h₁, h₂, by omega, by omega⟩

private theorem sosHorizontalPathFlux_eq_segmentSum {N R y : ℕ}
    (η : Lattice2D.SquareFreeEdge N → ℤ) (hR : R < N) (hy : y < N) :
    clockPeierlsPathFlux η (sosHorizontalPathEdge hR hy) =
      squareFreeHorizontalSegmentSum η y 0 R := by
  classical
  unfold clockPeierlsPathFlux
  let f : ℕ → ℤ := fun i =>
    if hi : i + 1 < N then
      η (GenericGradient.squareFreeHorizontalEdgeAt i y hi hy) else 0
  have hpath : (∑ i : Fin R, η (sosHorizontalPathEdge hR hy i)) =
      ∑ i : Fin R, f i.val := by
    apply Finset.sum_congr rfl
    intro i hi
    have hiN : i.val + 1 < N := by omega
    simp [f, sosHorizontalPathEdge, hiN]
  rw [hpath, Fin.sum_univ_eq_sum_range f R]
  have hseg (r : ℕ) : squareFreeHorizontalSegmentSum η y 0 r =
      ∑ i ∈ Finset.range r, GenericGradient.squareFreeHorizontalValue η i y := by
    induction r with
    | zero => simp [squareFreeHorizontalSegmentSum]
    | succ r ih =>
        rw [squareFreeHorizontalSegmentSum, Finset.sum_range_succ, ih]
        simp
  rw [hseg]
  apply Finset.sum_congr rfl
  intro i hi
  have hiN : i + 1 < N := by have := Finset.mem_range.mp hi; omega
  simp [f, GenericGradient.squareFreeHorizontalValue, hiN, hy]

private theorem sosHorizontalValue_restrict_zero {N : ℕ}
    (S : Finset (Lattice2D.SquareFreeEdge N)) (η : Lattice2D.SquareFreeEdge N → ℤ)
    (i y : ℕ) (hi : i + 1 < N) (hy : y < N)
    (hnot : GenericGradient.squareFreeHorizontalEdgeAt i y hi hy ∉ S) :
    GenericGradient.squareFreeHorizontalValue (restrictEdgeField S η) i y = 0 := by
  simp [GenericGradient.squareFreeHorizontalValue, hi, hy, restrictEdgeField, hnot]

private theorem sosVerticalValue_restrict_zero {N : ℕ}
    (S : Finset (Lattice2D.SquareFreeEdge N)) (η : Lattice2D.SquareFreeEdge N → ℤ)
    (i j : ℕ) (hi : i < N) (hj : j + 1 < N)
    (hnot : GenericGradient.squareFreeVerticalEdgeAt i j hi hj ∉ S) :
    GenericGradient.squareFreeVerticalValue (restrictEdgeField S η) i j = 0 := by
  simp [GenericGradient.squareFreeVerticalValue, hi, hj, restrictEdgeField, hnot]

private theorem sosHorizontalSegmentSum_restrict_zero {N : ℕ}
    (S : Finset (Lattice2D.SquareFreeEdge N)) (η : Lattice2D.SquareFreeEdge N → ℤ)
    (y x r : ℕ) (hy : y < N) (hx : x + r < N)
    (hnot : ∀ t (_ht : t < r) (hi : x + t + 1 < N),
      GenericGradient.squareFreeHorizontalEdgeAt (x + t) y hi hy ∉ S) :
    squareFreeHorizontalSegmentSum (restrictEdgeField S η) y x r = 0 := by
  revert x hx hnot
  induction r with
  | zero => intro x hx hnot; simp [squareFreeHorizontalSegmentSum]
  | succ r ih =>
      intro x hx hnot
      have hx' : x + r < N := by omega
      rw [squareFreeHorizontalSegmentSum, ih x hx' (by
        intro t ht hi
        exact hnot t (by omega) hi)]
      rw [sosHorizontalValue_restrict_zero S η (x + r) y (by omega) hy
        (hnot r (by omega) hx)]
      simp

private theorem sosVerticalSegmentSum_restrict_zero {N : ℕ}
    (S : Finset (Lattice2D.SquareFreeEdge N)) (η : Lattice2D.SquareFreeEdge N → ℤ)
    (x y r : ℕ) (hx : x < N) (hy : y + r < N)
    (hnot : ∀ t (_ht : t < r) (hj : y + t + 1 < N),
      GenericGradient.squareFreeVerticalEdgeAt x (y + t) hx hj ∉ S) :
    squareFreeVerticalSegmentSum (restrictEdgeField S η) x y r = 0 := by
  revert y hy hnot
  induction r with
  | zero => intro y hy hnot; simp [squareFreeVerticalSegmentSum]
  | succ r ih =>
      intro y hy hnot
      have hy' : y + r < N := by omega
      rw [squareFreeVerticalSegmentSum, ih y hy' (by
        intro t ht hj
        exact hnot t (by omega) hj)]
      rw [sosVerticalValue_restrict_zero S η x (y + r) hx (by omega)
        (hnot r (by omega) hy)]
      simp

/-- A nonzero flux of a saturated integer-gradient contour on a horizontal route forces a large
contour. The detour may be taken above or below the route, whichever has more room in the box. -/
theorem sosComponent_minContourSize_row_le {N R y : ℕ}
    (hR : R < N) (hy : y < N) (η : Lattice2D.SquareFreeEdge N → ℤ)
    (hclosed : GenericGradient.squareFreePlaquetteClosed η)
    (c : (clockPeierlsBadGraph (clockPeierlsAdjacencyGraph N) η).ConnectedComponent)
    (hsaturated : squareFreePlaquetteSaturated η
      (clockPeierlsComponentSupport (clockPeierlsAdjacencyGraph N) η c))
    (i : Fin R)
    (hflux : clockPeierlsComponentFlux (clockPeierlsAdjacencyGraph N) η
      (sosHorizontalPathEdge hR hy) c ≠ 0)
    (hroot : sosHorizontalPathEdge hR hy i ∈
      clockPeierlsComponentSupport (clockPeierlsAdjacencyGraph N) η c) :
    clockPeierlsMinContourSize R (max y (N - 1 - y)) (i.val + 1) ≤
      (clockPeierlsComponentSupport (clockPeierlsAdjacencyGraph N) η c).card := by
  classical
  let G := clockPeierlsAdjacencyGraph N
  let S := clockPeierlsComponentSupport G η c
  let j := i.val + 1
  let k := S.card
  have hsize : 0 < k := by
    dsimp [k]
    exact Finset.card_pos.mpr ⟨sosHorizontalPathEdge hR hy i, hroot⟩
  have hconn : (G.induce (S : Set (Lattice2D.SquareFreeEdge N))).Connected := by
    exact clockPeierlsComponentSupport_connected G η c
  let edgeAnchor : Lattice2D.SquareFreeEdge N → ℕ × ℕ :=
    fun e => clockPeierlsEdgeAnchor e
  let coordUp : Lattice2D.SquareFreeEdge N → ℕ × ℕ := sosAnchorCoordUp y
  let coordDown : Lattice2D.SquareFreeEdge N → ℕ × ℕ := sosAnchorCoordDown y
  have hstepUp : ∀ {e f : Lattice2D.SquareFreeEdge N}, G.Adj e f →
      clockPeierlsCoordWithin (coordUp e) (coordUp f) 1 := by
    intro e f hef
    exact sosAnchorCoordUp_step hef
  have hstepDown : ∀ {e f : Lattice2D.SquareFreeEdge N}, G.Adj e f →
      clockPeierlsCoordWithin (coordDown e) (coordDown f) 1 := by
    intro e f hef
    exact sosAnchorCoordDown_step hef
  have hcoordUpRoot : coordUp (sosHorizontalPathEdge hR hy i) = (i.val, 0) := by
    simp [coordUp, sosAnchorCoordUp, sosHorizontalPathEdge,
      clockPeierlsEdgeAnchor, GenericGradient.squareFreeHorizontalEdgeAt]
  have hcoordDownRoot : coordDown (sosHorizontalPathEdge hR hy i) = (i.val, 0) := by
    simp [coordDown, sosAnchorCoordDown, sosHorizontalPathEdge,
      clockPeierlsEdgeAnchor, GenericGradient.squareFreeHorizontalEdgeAt]
  let TUp := S.image coordUp
  let TDown := S.image coordDown
  have hnearUpAll : ∀ p ∈ TUp, clockPeierlsCoordWithin p (i.val, 0) (k + 1) := by
    exact clockPeierlsConnectedAnchors_near (Lattice2D.SquareFreeEdge N) j k G
      coordUp hstepUp S hconn hroot (by simpa [j] using hcoordUpRoot) (by rfl)
  have hnearUp : ∀ p ∈ TUp, clockPeierlsCoordWithin p (i.val, 0) (k + 1) := by
    exact hnearUpAll
  have hnearDownAll : ∀ p ∈ TDown, clockPeierlsCoordWithin p (i.val, 0) (k + 1) := by
    exact clockPeierlsConnectedAnchors_near (Lattice2D.SquareFreeEdge N) j k G
      coordDown hstepDown S hconn hroot (by simpa [j] using hcoordDownRoot) (by rfl)
  have hnearDown : ∀ p ∈ TDown, clockPeierlsCoordWithin p (i.val, 0) (k + 1) := by
    exact hnearDownAll
  have hnearEdgeUp (e : Lattice2D.SquareFreeEdge N) (he : e ∈ S) :
      clockPeierlsCoordWithin (coordUp e) (i.val, 0) (k + 1) :=
    hnearUp (coordUp e) (Finset.mem_image.mpr ⟨e, he, rfl⟩)
  have hnearEdgeDown (e : Lattice2D.SquareFreeEdge N) (he : e ∈ S) :
      clockPeierlsCoordWithin (coordDown e) (i.val, 0) (k + 1) :=
    hnearDown (coordDown e) (Finset.mem_image.mpr ⟨e, he, rfl⟩)
  have hcomponentFlux : clockPeierlsComponentFlux G η
      (sosHorizontalPathEdge hR hy) c =
        clockPeierlsPathFlux (restrictEdgeField S η) (sosHorizontalPathEdge hR hy) := by
    unfold clockPeierlsComponentFlux clockPeierlsPathFlux
    apply Finset.sum_congr rfl
    intro t ht
    simp [restrictEdgeField, S]
  have hstraight : squareFreeHorizontalSegmentSum (restrictEdgeField S η) y 0 R ≠ 0 := by
    rw [← sosHorizontalPathFlux_eq_segmentSum (restrictEdgeField S η) hR hy,
      ← hcomponentFlux]
    exact hflux
  have hsplit := squareFreePlaquetteClosed_restrict_split η S hclosed hsaturated
  have hnotMargins : ¬ (k + 3 < j ∧ k + 3 < R - j ∧
      k + 3 < max y (N - 1 - y)) := by
    intro hm
    have hleft := hm.1
    have hright := hm.2.1
    have hheight := hm.2.2
    have hleftSize : k + 3 < j := hm.1
    have hrightSize : k + 3 < R - j := hm.2.1
    have hleftSub : j - (k + 3) + (k + 3) = j :=
      Nat.sub_add_cancel (by omega)
    have hheight' : k + 3 < max (N - 1 - y) y := by simpa [max_comm] using hheight
    rcases lt_max_iff.mp hheight' with hup | hdown
    · have hup' : y + (k + 3) < N := by omega
      have hnotH1 : ∀ t (_ht : t < j - (k + 3))
          (hi : 0 + t + 1 < N),
          GenericGradient.squareFreeHorizontalEdgeAt (0 + t) y hi hy ∉ S := by
        intro t ht hi heS
        have hn := hnearEdgeUp
          (GenericGradient.squareFreeHorizontalEdgeAt (0 + t) y hi hy) heS
        simp [coordUp, sosAnchorCoordUp, clockPeierlsEdgeAnchor,
          GenericGradient.squareFreeHorizontalEdgeAt] at hn
        dsimp [clockPeierlsCoordWithin] at hn
        have htf : t + (k + 3) < j := by
          calc
            t + (k + 3) < (j - (k + 3)) + (k + 3) := Nat.add_lt_add_right ht _
            _ = j := hleftSub
        rcases hn with ⟨_, hnearX, _, _⟩
        have hnearX' : i.val ≤ t + (k + 1) := by omega
        omega
      have hnotV1 : ∀ t (_ht : t < k + 3) (hj : y + t + 1 < N),
          GenericGradient.squareFreeVerticalEdgeAt (j - (k + 3)) (y + t)
            (by omega) hj ∉ S := by
        intro t ht hj heS
        have hn := hnearEdgeUp
          (GenericGradient.squareFreeVerticalEdgeAt (j - (k + 3)) (y + t)
            (by omega) hj) heS
        simp [coordUp, sosAnchorCoordUp, clockPeierlsEdgeAnchor,
          GenericGradient.squareFreeVerticalEdgeAt] at hn
        dsimp [clockPeierlsCoordWithin] at hn
        have htf : t + (k + 3) < j := by omega
        rcases hn with ⟨_, hnearX, _, _⟩
        have hnearX' : i.val ≤ (j - (k + 3)) + (k + 1) := by omega
        omega
      have hnotH2 : ∀ t (_ht : t < 2 * (k + 3))
          (hi : j - (k + 3) + t + 1 < N),
          GenericGradient.squareFreeHorizontalEdgeAt (j - (k + 3) + t)
            (y + (k + 3)) hi (by omega) ∉ S := by
        intro t ht hi heS
        have hn := hnearEdgeUp
          (GenericGradient.squareFreeHorizontalEdgeAt (j - (k + 3) + t)
            (y + (k + 3)) hi (by omega)) heS
        simp [coordUp, sosAnchorCoordUp, clockPeierlsEdgeAnchor,
          GenericGradient.squareFreeHorizontalEdgeAt] at hn
        dsimp [clockPeierlsCoordWithin] at hn
        rcases hn with ⟨_, _, hnearY, _⟩
        omega
      have hnotV2 : ∀ t (_ht : t < k + 3)
          (hj : y + t + 1 < N),
          GenericGradient.squareFreeVerticalEdgeAt (j + (k + 3)) (y + t)
            (by omega) hj ∉ S := by
        intro t ht hj heS
        have hn := hnearEdgeUp
          (GenericGradient.squareFreeVerticalEdgeAt (j + (k + 3)) (y + t)
            (by omega) hj) heS
        simp [coordUp, sosAnchorCoordUp, clockPeierlsEdgeAnchor,
          GenericGradient.squareFreeVerticalEdgeAt] at hn
        dsimp [clockPeierlsCoordWithin] at hn
        rcases hn with ⟨hnearX, _, _, _⟩
        omega
      have hnotH3 : ∀ t (_ht : t < R - (j + (k + 3)))
          (hi : j + (k + 3) + t + 1 < N),
          GenericGradient.squareFreeHorizontalEdgeAt (j + (k + 3) + t)
            y hi hy ∉ S := by
        intro t ht hi heS
        have hn := hnearEdgeUp
          (GenericGradient.squareFreeHorizontalEdgeAt (j + (k + 3) + t)
            y hi hy) heS
        simp [coordUp, sosAnchorCoordUp, clockPeierlsEdgeAnchor,
          GenericGradient.squareFreeHorizontalEdgeAt] at hn
        dsimp [clockPeierlsCoordWithin] at hn
        rcases hn with ⟨hnearX, _, _, _⟩
        omega
      have hzero : sosHorizontalDetourFluxUp (restrictEdgeField S η) R j k y = 0 := by
        simp [sosHorizontalDetourFluxUp,
          sosHorizontalSegmentSum_restrict_zero S η y 0 (j - (k + 3)) hy (by omega)
            (fun t ht hi => hnotH1 t ht (by omega)),
          sosVerticalSegmentSum_restrict_zero S η (j - (k + 3)) y (k + 3)
            (by omega) (by omega) hnotV1,
          sosHorizontalSegmentSum_restrict_zero S η (y + (k + 3))
            (j - (k + 3)) (2 * (k + 3)) (by omega) (by omega) hnotH2,
          sosVerticalSegmentSum_restrict_zero S η (j + (k + 3)) y (k + 3)
            (by omega) (by omega) hnotV2,
          sosHorizontalSegmentSum_restrict_zero S η y (j + (k + 3))
            (R - (j + (k + 3))) hy (by omega) hnotH3]
      exact hstraight (by
        rw [sosHorizontalSegmentSum_eq_detourUp (restrictEdgeField S η) hsplit.1
          R j k y hleftSize hrightSize hR hy hup']
        exact hzero)
    · have hdown' : k + 3 < y := by omega
      have hnotH1 : ∀ t (_ht : t < j - (k + 3))
          (hi : 0 + t + 1 < N),
          GenericGradient.squareFreeHorizontalEdgeAt (0 + t) y hi hy ∉ S := by
        intro t ht hi heS
        have hn := hnearEdgeDown
          (GenericGradient.squareFreeHorizontalEdgeAt (0 + t) y hi hy) heS
        simp [coordDown, sosAnchorCoordDown, clockPeierlsEdgeAnchor,
          GenericGradient.squareFreeHorizontalEdgeAt] at hn
        dsimp [clockPeierlsCoordWithin] at hn
        have htf : t + (k + 3) < j := by
          calc
            t + (k + 3) < (j - (k + 3)) + (k + 3) := Nat.add_lt_add_right ht _
            _ = j := hleftSub
        rcases hn with ⟨_, hnearX, _, _⟩
        have hnearX' : i.val ≤ t + (k + 1) := by omega
        omega
      have hnotV1 : ∀ t (_ht : t < k + 3) (hj : y - (k + 3) + t + 1 < N),
          GenericGradient.squareFreeVerticalEdgeAt (j - (k + 3))
            (y - (k + 3) + t) (by omega) hj ∉ S := by
        intro t ht hj heS
        have hn := hnearEdgeDown
          (GenericGradient.squareFreeVerticalEdgeAt (j - (k + 3))
            (y - (k + 3) + t) (by omega) hj) heS
        simp [coordDown, sosAnchorCoordDown, clockPeierlsEdgeAnchor,
          GenericGradient.squareFreeVerticalEdgeAt] at hn
        dsimp [clockPeierlsCoordWithin] at hn
        have htf : t + (k + 3) < j := by omega
        rcases hn with ⟨_, hnearX, _, _⟩
        have hnearX' : i.val ≤ (j - (k + 3)) + (k + 1) := by omega
        omega
      have hnotH2 : ∀ t (_ht : t < 2 * (k + 3))
          (hi : j - (k + 3) + t + 1 < N),
          GenericGradient.squareFreeHorizontalEdgeAt (j - (k + 3) + t)
            (y - (k + 3)) hi (by omega) ∉ S := by
        intro t ht hi heS
        have hn := hnearEdgeDown
          (GenericGradient.squareFreeHorizontalEdgeAt (j - (k + 3) + t)
            (y - (k + 3)) hi (by omega)) heS
        simp [coordDown, sosAnchorCoordDown, clockPeierlsEdgeAnchor,
          GenericGradient.squareFreeHorizontalEdgeAt] at hn
        dsimp [clockPeierlsCoordWithin] at hn
        rcases hn with ⟨_, _, hnearY, _⟩
        omega
      have hnotV2 : ∀ t (_ht : t < k + 3)
          (hj : y - (k + 3) + t + 1 < N),
          GenericGradient.squareFreeVerticalEdgeAt (j + (k + 3))
            (y - (k + 3) + t) (by omega) hj ∉ S := by
        intro t ht hj heS
        have hn := hnearEdgeDown
          (GenericGradient.squareFreeVerticalEdgeAt (j + (k + 3))
            (y - (k + 3) + t) (by omega) hj) heS
        simp [coordDown, sosAnchorCoordDown, clockPeierlsEdgeAnchor,
          GenericGradient.squareFreeVerticalEdgeAt] at hn
        dsimp [clockPeierlsCoordWithin] at hn
        rcases hn with ⟨hnearX, _, _, _⟩
        omega
      have hnotH3 : ∀ t (_ht : t < R - (j + (k + 3)))
          (hi : j + (k + 3) + t + 1 < N),
          GenericGradient.squareFreeHorizontalEdgeAt (j + (k + 3) + t)
            y hi hy ∉ S := by
        intro t ht hi heS
        have hn := hnearEdgeDown
          (GenericGradient.squareFreeHorizontalEdgeAt (j + (k + 3) + t)
            y hi hy) heS
        simp [coordDown, sosAnchorCoordDown, clockPeierlsEdgeAnchor,
          GenericGradient.squareFreeHorizontalEdgeAt] at hn
        dsimp [clockPeierlsCoordWithin] at hn
        rcases hn with ⟨hnearX, _, _, _⟩
        omega
      have hzero : sosHorizontalDetourFluxDown (restrictEdgeField S η) R j k y = 0 := by
        simp [sosHorizontalDetourFluxDown,
          sosHorizontalSegmentSum_restrict_zero S η y 0 (j - (k + 3)) hy (by omega)
            hnotH1,
          sosVerticalSegmentSum_restrict_zero S η (j - (k + 3))
            (y - (k + 3)) (k + 3) (by omega) (by omega) hnotV1,
          sosHorizontalSegmentSum_restrict_zero S η (y - (k + 3))
            (j - (k + 3)) (2 * (k + 3)) (by omega) (by omega) hnotH2,
          sosVerticalSegmentSum_restrict_zero S η (j + (k + 3))
            (y - (k + 3)) (k + 3) (by omega) (by omega) hnotV2,
          sosHorizontalSegmentSum_restrict_zero S η y (j + (k + 3))
            (R - (j + (k + 3))) hy (by omega) hnotH3]
      exact hstraight (by
        rw [sosHorizontalSegmentSum_eq_detourDown (restrictEdgeField S η) hsplit.1
          R j k y hleftSize hrightSize hR hy hdown']
        exact hzero)
  have hmargin : min j (min (R - j) (max y (N - 1 - y))) ≤ k + 3 := by
    by_contra h
    have hlarge : k + 3 < min j (min (R - j) (max y (N - 1 - y))) := by omega
    have hleft : k + 3 < j := lt_of_lt_of_le hlarge (Nat.min_le_left _ _)
    have hrest : k + 3 < min (R - j) (max y (N - 1 - y)) :=
      lt_of_lt_of_le hlarge (Nat.min_le_right _ _)
    have hright : k + 3 < R - j := lt_of_lt_of_le hrest (Nat.min_le_left _ _)
    have hheight : k + 3 < max y (N - 1 - y) :=
      lt_of_lt_of_le hrest (Nat.min_le_right _ _)
    exact hnotMargins ⟨hleft, hright, hheight⟩
  unfold clockPeierlsMinContourSize
  change max 1 (min (i.val + 1) (min (R - (i.val + 1)) (max y (N - 1 - y))) - 3) ≤ S.card
  have hmargin' : min (i.val + 1)
      (min (R - (i.val + 1)) (max y (N - 1 - y))) ≤ S.card + 3 := by
    simpa [j, k] using hmargin
  omega

end FroehlichSpencer.BKT.SOS.Peierls

end
