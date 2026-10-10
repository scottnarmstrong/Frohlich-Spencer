/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Clock.Peierls.ComponentFlux
public import FroehlichSpencer.BKT.Clock.Peierls.ContourGeometry
public import FroehlichSpencer.BKT.Clock.Peierls.Counting
public import FroehlichSpencer.BKT.Clock.Peierls.Detour
public import FroehlichSpencer.BKT.Clock.Peierls.EdgeAdjacency
public import FroehlichSpencer.BKT.Clock.Peierls.FieldSplittingSquare
public import FroehlichSpencer.BKT.Clock.Peierls.StraightPath
import Mathlib.Tactic

/-! # Active clock contours are large near the middle of a long path -/

@[expose] public section

namespace FroehlichSpencer.BKT.Clock.Peierls

open FroehlichSpencer.BKT.Lattice2D
open GenericGradient

/-- The positive horizontal edge at position `i` on the bottom row of a square of side `M + 1`.
The path itself has `R` edges and `R ≤ M`. -/
def clockPeierlsPathEdge {R M : ℕ} (hRM : R ≤ M) (i : Fin R) :
    Lattice2D.SquareFreeEdge (M + 1) :=
  clockPeierlsHorizontalEdgeAt (L := M + 1) i.val 0 (by omega) (by omega)

private theorem horizontalSegmentSum_eq_sum_range {L : ℕ} {A : Type*}
    [AddCommGroup A] (η : Lattice2D.SquareFreeEdge L → A) (y x r : ℕ) :
    squareFreeHorizontalSegmentSum η y x r =
      ∑ i ∈ Finset.range r, GenericGradient.squareFreeHorizontalValue (L := L) η (x + i) y := by
  induction r with
  | zero => simp [squareFreeHorizontalSegmentSum]
  | succ r ih =>
      rw [squareFreeHorizontalSegmentSum, Finset.sum_range_succ, ih]

/-- The indexed edge-path flux is the coordinate segment sum. -/
theorem clockPeierlsPathFlux_eq_horizontalSegmentSum {R M : ℕ} (hRM : R ≤ M)
    {A : Type*} [AddCommGroup A] (η : Lattice2D.SquareFreeEdge (M + 1) → A) :
    clockPeierlsPathFlux η (clockPeierlsPathEdge hRM) =
      squareFreeHorizontalSegmentSum η 0 0 R := by
  classical
  unfold clockPeierlsPathFlux
  let f : ℕ → A := fun i =>
    if hi : i + 1 < M + 1 then
      η (GenericGradient.squareFreeHorizontalEdgeAt (L := M + 1) i 0 hi (by omega))
    else 0
  have hpath : (∑ i : Fin R, η (clockPeierlsPathEdge hRM i)) =
      ∑ i : Fin R, f i.val := by
    apply Finset.sum_congr rfl
    intro i hi
    have hiM : i.val < M := by omega
    simp [f, clockPeierlsPathEdge, clockPeierlsHorizontalEdgeAt,
      GenericGradient.squareFreeHorizontalEdgeAt, hiM]
  rw [hpath, Fin.sum_univ_eq_sum_range f R]
  rw [horizontalSegmentSum_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i hi
  have hiR : i < R := Finset.mem_range.mp hi
  have hiM : i < M := by omega
  simp [f, GenericGradient.squareFreeHorizontalValue,
    show i + 1 < M + 1 by omega, hiM]

private theorem horizontalSegmentSum_restrict_zero {L n : ℕ}
    (S : Finset (Lattice2D.SquareFreeEdge L))
    (η : Lattice2D.SquareFreeEdge L → ZMod n) (y x r : ℕ)
    (hx : x + r < L) (hy : y < L)
    (hnot : ∀ t, ∀ (ht : t < r),
      GenericGradient.squareFreeHorizontalEdgeAt (L := L) (x + t) y
        (by omega) hy ∉ S) :
    squareFreeHorizontalSegmentSum (restrictEdgeField S η) y x r = 0 := by
  induction r with
  | zero => simp [squareFreeHorizontalSegmentSum]
  | succ r ih =>
      have hx' : x + r < L := by omega
      rw [squareFreeHorizontalSegmentSum, ih hx' (by
        intro t ht
        exact hnot t (by omega))]
      have hlast : GenericGradient.squareFreeHorizontalValue
          (restrictEdgeField S η) (x + r) y = 0 := by
        simp [GenericGradient.squareFreeHorizontalValue,
          show x + r + 1 < L by omega, hy,
          restrictEdgeField, hnot r (by omega)]
      rw [hlast]
      simp

private theorem verticalSegmentSum_restrict_zero {L n : ℕ}
    (S : Finset (Lattice2D.SquareFreeEdge L))
    (η : Lattice2D.SquareFreeEdge L → ZMod n) (x y r : ℕ)
    (hx : x < L) (hy : y + r < L)
    (hnot : ∀ t, ∀ (ht : t < r),
      GenericGradient.squareFreeVerticalEdgeAt (L := L) x (y + t)
        hx (by omega) ∉ S) :
    squareFreeVerticalSegmentSum (restrictEdgeField S η) x y r = 0 := by
  induction r with
  | zero => simp [squareFreeVerticalSegmentSum]
  | succ r ih =>
      have hy' : y + r < L := by omega
      rw [squareFreeVerticalSegmentSum, ih hy' (by
        intro t ht
        exact hnot t (by omega))]
      have hlast : GenericGradient.squareFreeVerticalValue
          (restrictEdgeField S η) x (y + r) = 0 := by
        simp [GenericGradient.squareFreeVerticalValue,
          hx, show y + r + 1 < L by omega,
          restrictEdgeField, hnot r (by omega)]
      rw [hlast]
      simp

private theorem clockPeierlsFrameEdge_not_mem
    {L : ℕ} (S : Finset (Lattice2D.SquareFreeEdge L))
    (frame : Finset (ℕ × ℕ)) (hdisj : Disjoint (S.image clockPeierlsEdgeAnchor) frame)
    (e : Lattice2D.SquareFreeEdge L) {p : ℕ × ℕ}
    (hp : p ∈ frame) (heq : clockPeierlsEdgeAnchor e = p) : e ∉ S := by
  intro heS
  have himage : clockPeierlsEdgeAnchor e ∈ S.image clockPeierlsEdgeAnchor :=
    Finset.mem_image.mpr ⟨e, heS, rfl⟩
  exact (Finset.disjoint_left.mp hdisj) (by simpa [heq] using himage) hp

private theorem clockPeierlsHorizontalFrameEdge_not_mem {L : ℕ}
    (S : Finset (Lattice2D.SquareFreeEdge L))
    (frame : Finset (ℕ × ℕ)) (hdisj : Disjoint (S.image clockPeierlsEdgeAnchor) frame)
    (x y : ℕ) (hi : x + 1 < L) (hj : y < L) {p : ℕ × ℕ}
    (hp : p ∈ frame) (hpcoord : p = (x, y)) :
    clockPeierlsHorizontalEdgeAt (L := L) x y hi hj ∉ S := by
  apply clockPeierlsFrameEdge_not_mem S frame hdisj _ hp
  · simp [clockPeierlsEdgeAnchor, clockPeierlsHorizontalEdgeAt, hpcoord]

private theorem clockPeierlsVerticalFrameEdge_not_mem {L : ℕ}
    (S : Finset (Lattice2D.SquareFreeEdge L))
    (frame : Finset (ℕ × ℕ)) (hdisj : Disjoint (S.image clockPeierlsEdgeAnchor) frame)
    (x y : ℕ) (hi : x < L) (hj : y + 1 < L) {p : ℕ × ℕ}
    (hp : p ∈ frame) (hpcoord : p = (x, y)) :
    clockPeierlsVerticalEdgeAt (L := L) x y hi hj ∉ S := by
  apply clockPeierlsFrameEdge_not_mem S frame hdisj _ hp
  · simp [clockPeierlsEdgeAnchor, clockPeierlsVerticalEdgeAt, hpcoord]

/-- A bad-edge component that carries nonzero flux across the straight endpoint path must have
size at least the explicit frame-detour margin at every path edge it meets. -/
theorem clockPeierlsComponent_minContourSize_le {R M n : ℕ} [NeZero n]
    (hRM : R ≤ M) (σ : Lattice2D.SquareFreeVertex (M + 1) → Fin n)
    (i : Fin R)
    (c : (clockPeierlsBadGraph (clockPeierlsAdjacencyGraph (M + 1))
      (clockConfigurationField σ)).ConnectedComponent)
    (hflux : clockPeierlsComponentFlux (clockPeierlsAdjacencyGraph (M + 1))
      (clockConfigurationField σ) (clockPeierlsPathEdge hRM) c ≠ 0)
    (hroot : clockPeierlsPathEdge hRM i ∈ clockPeierlsComponentSupport
      (clockPeierlsAdjacencyGraph (M + 1)) (clockConfigurationField σ) c) :
    clockPeierlsMinContourSize R M (i.val + 1) ≤
      (clockPeierlsComponentSupport (clockPeierlsAdjacencyGraph (M + 1))
        (clockConfigurationField σ) c).card := by
  classical
  let S := clockPeierlsComponentSupport (clockPeierlsAdjacencyGraph (M + 1))
    (clockConfigurationField σ) c
  let j := i.val + 1
  let k := S.card
  have hj : j ≤ R := by dsimp [j]; exact Nat.succ_le_of_lt i.isLt
  have hjpos : 1 ≤ j := by dsimp [j]; omega
  have hsize : 0 < S.card := Finset.card_pos.mpr ⟨clockPeierlsPathEdge hRM i, hroot⟩
  have hnotMargins : ¬ (k + 3 < j ∧ k + 3 < R - j ∧ k + 3 < M) := by
    intro hmargins
    rcases hmargins with ⟨hleft, hright, hheight⟩
    have hcross : j - (k + 3) + 2 * (k + 3) = j + (k + 3) := by omega
    have hJ : j + (k + 3) < R := by omega
    have hconn :
        ((clockPeierlsAdjacencyGraph (M + 1)).induce
          (S : Set (Lattice2D.SquareFreeEdge (M + 1)))).Connected := by
      exact clockPeierlsComponentSupport_connected _ _ c
    have hanchor : clockPeierlsEdgeAnchor (clockPeierlsPathEdge hRM i) = (j - 1, 0) := by
      simp [clockPeierlsPathEdge, clockPeierlsHorizontalEdgeAt, clockPeierlsEdgeAnchor, j]
    have hnear := clockPeierlsConnectedAnchors_near
      (Lattice2D.SquareFreeEdge (M + 1)) j k (clockPeierlsAdjacencyGraph (M + 1))
      clockPeierlsEdgeAnchor clockPeierlsAdjacencyGraph_anchor_step S hconn hroot hanchor
      (by rfl)
    have hdetour := clockPeierlsFrameDetour_avoids_neighborhood R j k M hleft hright hheight
      (S.image clockPeierlsEdgeAnchor) hnear
    have hdisj := hdetour.1
    let frame := clockPeierlsFrameDetourAnchors R j k
    have hsplit := squareFreePlaquetteClosed_restrict_split
      (clockConfigurationField σ) S (clockConfigurationField_closed σ)
      (clockPeierlsComponentSupport_squareSaturated σ c)
    have hclosed : GenericGradient.squareFreePlaquetteClosed
        (restrictEdgeField S (clockConfigurationField σ)) := hsplit.1
    have hleft0 : squareFreeHorizontalSegmentSum
        (restrictEdgeField S (clockConfigurationField σ)) 0 0 (j - (k + 3)) = 0 := by
      apply horizontalSegmentSum_restrict_zero S (clockConfigurationField σ) 0 0 _
        (by omega) (by omega)
      intro t ht
      have hpframe : (t, 0) ∈ frame := by
        simp [frame, clockPeierlsFrameDetourAnchors,
          clockPeierlsHorizontalFrameSegment, clockPeierlsVerticalFrameSegment]
        omega
      apply clockPeierlsFrameEdge_not_mem S frame hdisj _ hpframe
      simp [clockPeierlsEdgeAnchor, GenericGradient.squareFreeHorizontalEdgeAt]
    have hleftV0 : squareFreeVerticalSegmentSum
        (restrictEdgeField S (clockConfigurationField σ)) (j - (k + 3)) 0 (k + 3) = 0 := by
      apply verticalSegmentSum_restrict_zero S (clockConfigurationField σ)
        (j - (k + 3)) 0 (k + 3) (by omega) (by omega)
      intro t ht
      have hpframe : (j - (k + 3), t) ∈ frame := by
        simp [frame, clockPeierlsFrameDetourAnchors,
          clockPeierlsHorizontalFrameSegment, clockPeierlsVerticalFrameSegment]
        omega
      apply clockPeierlsFrameEdge_not_mem S frame hdisj _ hpframe
      simp [clockPeierlsEdgeAnchor, GenericGradient.squareFreeVerticalEdgeAt]
    have htop0 : squareFreeHorizontalSegmentSum
        (restrictEdgeField S (clockConfigurationField σ)) (k + 3) (j - (k + 3))
          (2 * (k + 3)) = 0 := by
      apply horizontalSegmentSum_restrict_zero S (clockConfigurationField σ)
        (k + 3) (j - (k + 3)) (2 * (k + 3)) (by omega) (by omega)
      intro t ht
      have hxupper : j - (k + 3) + t < j + (k + 3) := by
        have hh := Nat.add_lt_add_left ht (j - (k + 3))
        rw [hcross] at hh
        exact hh
      have hpframe : (j - (k + 3) + t, k + 3) ∈ frame := by
        simp [frame, clockPeierlsFrameDetourAnchors,
          clockPeierlsHorizontalFrameSegment, clockPeierlsVerticalFrameSegment]
        omega
      apply clockPeierlsFrameEdge_not_mem S frame hdisj _ hpframe
      simp [clockPeierlsEdgeAnchor, GenericGradient.squareFreeHorizontalEdgeAt]
    have hrightV0 : squareFreeVerticalSegmentSum
        (restrictEdgeField S (clockConfigurationField σ)) (j + (k + 3)) 0 (k + 3) = 0 := by
      apply verticalSegmentSum_restrict_zero S (clockConfigurationField σ)
        (j + (k + 3)) 0 (k + 3) (by omega) (by omega)
      intro t ht
      have hpframe : (j + (k + 3), t) ∈ frame := by
        simp only [frame, clockPeierlsFrameDetourAnchors, Finset.mem_union,
          clockPeierlsHorizontalFrameSegment, clockPeierlsVerticalFrameSegment,
          Finset.mem_image]
        simp
        omega
      apply clockPeierlsFrameEdge_not_mem S frame hdisj _ hpframe
      simp [clockPeierlsEdgeAnchor, GenericGradient.squareFreeVerticalEdgeAt]
    have hright0 : squareFreeHorizontalSegmentSum
        (restrictEdgeField S (clockConfigurationField σ)) 0 (j + (k + 3))
          (R - (j + (k + 3))) = 0 := by
      apply horizontalSegmentSum_restrict_zero S (clockConfigurationField σ) 0
        (j + (k + 3)) (R - (j + (k + 3))) (by omega) (by omega)
      intro t ht
      have hsub : j + (k + 3) + (R - (j + (k + 3))) = R := by omega
      have hend : j + (k + 3) + t < R := by
        calc
          _ < j + (k + 3) + (R - (j + (k + 3))) := Nat.add_lt_add_left ht _
          _ = R := hsub
      have hpframe : (j + (k + 3) + t, 0) ∈ frame := by
        simp [frame, clockPeierlsFrameDetourAnchors,
          clockPeierlsHorizontalFrameSegment, clockPeierlsVerticalFrameSegment]
        omega
      apply clockPeierlsFrameEdge_not_mem S frame hdisj _ hpframe
      simp [clockPeierlsEdgeAnchor, GenericGradient.squareFreeHorizontalEdgeAt]
    have hdetourFlux : squareFreeFrameDetourFlux
        (restrictEdgeField S (clockConfigurationField σ)) R j k = 0 := by
      simp [squareFreeFrameDetourFlux, hleft0, hleftV0, htop0, hrightV0, hright0]
    have hstraightDetour := squareFreeHorizontalSegmentSum_eq_frameDetourFlux_of_closed
      (restrictEdgeField S (clockConfigurationField σ)) hclosed R j k
      (by omega) (by omega) (by omega) (by omega)
    have hcomponentFlux : clockPeierlsComponentFlux (clockPeierlsAdjacencyGraph (M + 1))
        (clockConfigurationField σ) (clockPeierlsPathEdge hRM) c =
        squareFreeHorizontalSegmentSum (restrictEdgeField S (clockConfigurationField σ))
          0 0 R := by
      calc
        _ = clockPeierlsPathFlux (restrictEdgeField S (clockConfigurationField σ))
              (clockPeierlsPathEdge hRM) := by
          unfold clockPeierlsComponentFlux clockPeierlsPathFlux
          rfl
        _ = _ := clockPeierlsPathFlux_eq_horizontalSegmentSum hRM _
    have hzero : clockPeierlsComponentFlux (clockPeierlsAdjacencyGraph (M + 1))
        (clockConfigurationField σ) (clockPeierlsPathEdge hRM) c = 0 := by
      rw [hcomponentFlux, hstraightDetour, hdetourFlux]
    exact hflux hzero
  have hmin : min j (min (R - j) M) ≤ k + 3 := by
    by_contra h
    have hgt : k + 3 < min j (min (R - j) M) := by omega
    have hleft : k + 3 < j := (lt_min_iff.mp hgt).1
    have hrest : k + 3 < min (R - j) M := (lt_min_iff.mp hgt).2
    have hright : k + 3 < R - j := (lt_min_iff.mp hrest).1
    have hheight : k + 3 < M := (lt_min_iff.mp hrest).2
    exact hnotMargins ⟨hleft, hright, hheight⟩
  unfold clockPeierlsMinContourSize
  change max 1 (min (i.val + 1) (min (R - (i.val + 1)) M) - 3) ≤ S.card
  have hmin' : min (i.val + 1) (min (R - (i.val + 1)) M) ≤ S.card + 3 := by
    simpa [j, k] using hmin
  omega

end FroehlichSpencer.BKT.Clock.Peierls

end
