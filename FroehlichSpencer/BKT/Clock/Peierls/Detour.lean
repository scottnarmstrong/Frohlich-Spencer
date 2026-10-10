/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

/-!
# Finite-coordinate localization and the frame detour

A connected finite set in a graph whose edges move coordinates by at most one has diameter at
most its cardinality.  For plaquette-adjacent square edges, this localizes a contour around a
straight-path edge.  The explicit frame route then avoids every edge statement in that coordinate
neighborhood whenever its three margins exceed the contour size plus three.
-/

@[expose] public section

namespace FroehlichSpencer.BKT.Clock.Peierls

open SimpleGraph
open Finset

/-- Coordinatewise `ℓ∞` distance at most `r`, written without absolute values. -/
def clockPeierlsCoordWithin (a b : ℕ × ℕ) (r : ℕ) : Prop :=
  a.1 ≤ b.1 + r ∧ b.1 ≤ a.1 + r ∧ a.2 ≤ b.2 + r ∧ b.2 ≤ a.2 + r

private theorem clockPeierlsWalk_coordWithin {V : Type*} (G : SimpleGraph V)
    (coord : V → ℕ × ℕ)
    (hstep : ∀ {a b : V}, G.Adj a b → clockPeierlsCoordWithin (coord a) (coord b) 1)
    {a b : V} (p : G.Walk a b) : clockPeierlsCoordWithin (coord a) (coord b) p.length := by
  induction p with
  | nil => simp [clockPeierlsCoordWithin]
  | @cons a b c hab p ih =>
      rcases hstep hab with ⟨h₁, h₂, h₃, h₄⟩
      rcases ih with ⟨h₅, h₆, h₇, h₈⟩
      simp only [Walk.length_cons]
      dsimp [clockPeierlsCoordWithin] at *
      exact ⟨by omega, by omega, by omega, by omega⟩

/-- A vertex in a finite connected induced set lies within its cardinality in coordinates of
any chosen root, provided graph adjacency moves each coordinate by at most one. -/
theorem clockPeierlsConnectedFinset_coordWithin {V : Type*} [Fintype V]
    (G : SimpleGraph V) (coord : V → ℕ × ℕ)
    (hstep : ∀ {a b : V}, G.Adj a b → clockPeierlsCoordWithin (coord a) (coord b) 1)
    (S : Finset V) (hconn : (G.induce (S : Set V)).Connected)
    {root x : V} (hroot : root ∈ S) (hx : x ∈ S) :
    clockPeierlsCoordWithin (coord x) (coord root) (S.card + 1) := by
  classical
  have hstep' : ∀ {a b : {x : V // x ∈ (S : Set V)}},
      (G.induce (S : Set V)).Adj a b →
        clockPeierlsCoordWithin (coord a.1) (coord b.1) 1 := by
    intro a b hab
    apply hstep
    exact hab
  obtain ⟨p, hp⟩ := hconn.exists_isPath ⟨x, hx⟩ ⟨root, hroot⟩
  have hpathLen : p.length < S.card := by
    simpa using hp.length_lt
  have hwalk := clockPeierlsWalk_coordWithin (G.induce (S : Set V))
    (fun z => coord z.1) hstep' p
  rcases hwalk with ⟨h₁, h₂, h₃, h₄⟩
  dsimp [clockPeierlsCoordWithin] at h₁ h₂ h₃ h₄ ⊢
  exact ⟨by omega, by omega, by omega, by omega⟩

/-- A connected finite set of edge statement of cardinality at most `k`, containing the straight
path edge at position `j`, lies in the coordinate neighborhood used by the frame-detour lemma.
The one-step coordinate bound is the only graph-specific input. -/
theorem clockPeierlsConnectedAnchors_near (V : Type*) [Fintype V] (j k : ℕ)
    (G : SimpleGraph V) (coord : V → ℕ × ℕ)
    (hstep : ∀ {a b : V}, G.Adj a b → clockPeierlsCoordWithin (coord a) (coord b) 1)
    (S : Finset V) (hconn : (G.induce (S : Set V)).Connected)
    {root : V} (hroot : root ∈ S) (hrootCoord : coord root = (j - 1, 0))
    (hcard : S.card ≤ k) :
    ∀ p ∈ S.image coord, clockPeierlsCoordWithin p (j - 1, 0) (k + 1) := by
  intro p hp
  rcases Finset.mem_image.mp hp with ⟨x, hx, rfl⟩
  have h := clockPeierlsConnectedFinset_coordWithin G coord hstep S hconn hroot hx
  rw [hrootCoord] at h
  dsimp [clockPeierlsCoordWithin] at h ⊢
  omega

/-- Horizontal edge statement on the half-open interval `[lo, hi)`, at height `y`. -/
def clockPeierlsHorizontalFrameSegment (y lo hi : ℕ) : Finset (ℕ × ℕ) :=
  (Ico lo hi).image fun x => (x, y)

/-- Vertical edge statement on the half-open interval `[lo, hi)`, at horizontal coordinate `x`. -/
def clockPeierlsVerticalFrameSegment (x lo hi : ℕ) : Finset (ℕ × ℕ) :=
  (Ico lo hi).image fun y => (x, y)

/-- Edge-statement set of the explicit path which leaves the axis, crosses above the contour, and
returns to the axis. The five segments are the left axis arm, left riser, upper crossbar, right
riser, and right axis arm. -/
def clockPeierlsFrameDetourAnchors (R j k : ℕ) : Finset (ℕ × ℕ) :=
  clockPeierlsHorizontalFrameSegment 0 0 (j - (k + 3)) ∪
    clockPeierlsVerticalFrameSegment (j - (k + 3)) 0 (k + 3) ∪
    clockPeierlsHorizontalFrameSegment (k + 3) (j - (k + 3)) (j + (k + 3)) ∪
    clockPeierlsVerticalFrameSegment (j + (k + 3)) 0 (k + 3) ∪
    clockPeierlsHorizontalFrameSegment 0 (j + (k + 3)) R

private theorem clockPeierlsFrameDetour_mem_cases {R j k : ℕ} {p : ℕ × ℕ}
    (hp : p ∈ clockPeierlsFrameDetourAnchors R j k) :
    (∃ x ∈ Ico 0 (j - (k + 3)), (x, 0) = p) ∨
    (∃ y ∈ Ico 0 (k + 3), (j - (k + 3), y) = p) ∨
    (∃ x ∈ Ico (j - (k + 3)) (j + (k + 3)), (x, k + 3) = p) ∨
    (∃ y ∈ Ico 0 (k + 3), (j + (k + 3), y) = p) ∨
    (∃ x ∈ Ico (j + (k + 3)) R, (x, 0) = p) := by
  simpa [clockPeierlsFrameDetourAnchors, clockPeierlsHorizontalFrameSegment,
    clockPeierlsVerticalFrameSegment] using hp

/-- Under the three margin assumptions, every frame edge statement lies inside the rectangle
`[0,R) × [0,M)`. -/
theorem clockPeierlsFrameDetour_inside_box (R j k M : ℕ)
    (hj : k + 3 < j) (hRj : k + 3 < R - j) (hM : k + 3 < M) :
    ∀ p ∈ clockPeierlsFrameDetourAnchors R j k, p.1 < R ∧ p.2 < M := by
  intro p hp
  rcases clockPeierlsFrameDetour_mem_cases hp with hleft | hleftV | htop | hrightV | hright
  · rcases hleft with ⟨x, hx, rfl⟩
    rcases mem_Ico.mp hx with ⟨hx0, hxL⟩
    constructor <;> omega
  · rcases hleftV with ⟨y, hy, rfl⟩
    rcases mem_Ico.mp hy with ⟨hy0, hyH⟩
    constructor <;> omega
  · rcases htop with ⟨x, hx, rfl⟩
    rcases mem_Ico.mp hx with ⟨hxL, hxR⟩
    constructor <;> omega
  · rcases hrightV with ⟨y, hy, rfl⟩
    rcases mem_Ico.mp hy with ⟨hy0, hyH⟩
    constructor <;> omega
  · rcases hright with ⟨x, hx, rfl⟩
    rcases mem_Ico.mp hx with ⟨hxR, hxEnd⟩
    constructor <;> omega

/-- The frame detour misses every set of edge statement contained in the radius `k + 1`
coordinate neighborhood of the straight-path edge at position `j`. -/
theorem clockPeierlsFrameDetour_avoids_neighborhood (R j k M : ℕ)
    (hj : k + 3 < j) (hRj : k + 3 < R - j) (hM : k + 3 < M)
    (Γ : Finset (ℕ × ℕ))
    (hnear : ∀ p ∈ Γ, clockPeierlsCoordWithin p (j - 1, 0) (k + 1)) :
    Disjoint Γ (clockPeierlsFrameDetourAnchors R j k) ∧
      (∀ p ∈ clockPeierlsFrameDetourAnchors R j k, p.1 < R ∧ p.2 < M) := by
  constructor
  · rw [Finset.disjoint_left]
    intro p hpΓ hpFrame
    rcases clockPeierlsFrameDetour_mem_cases hpFrame with
      hleft | hleftV | htop | hrightV | hright
    · rcases hleft with ⟨x, hx, rfl⟩
      rcases mem_Ico.mp hx with ⟨hx0, hxL⟩
      have hnear' := hnear (x, 0) hpΓ
      dsimp [clockPeierlsCoordWithin] at hnear'
      omega
    · rcases hleftV with ⟨y, hy, rfl⟩
      rcases mem_Ico.mp hy with ⟨hy0, hyH⟩
      have hnear' := hnear (j - (k + 3), y) hpΓ
      dsimp [clockPeierlsCoordWithin] at hnear'
      omega
    · rcases htop with ⟨x, hx, rfl⟩
      rcases mem_Ico.mp hx with ⟨hxL, hxR⟩
      have hnear' := hnear (x, k + 3) hpΓ
      dsimp [clockPeierlsCoordWithin] at hnear'
      omega
    · rcases hrightV with ⟨y, hy, rfl⟩
      rcases mem_Ico.mp hy with ⟨hy0, hyH⟩
      have hnear' := hnear (j + (k + 3), y) hpΓ
      dsimp [clockPeierlsCoordWithin] at hnear'
      omega
    · rcases hright with ⟨x, hx, rfl⟩
      rcases mem_Ico.mp hx with ⟨hxR, hxEnd⟩
      have hnear' := hnear (x, 0) hpΓ
      dsimp [clockPeierlsCoordWithin] at hnear'
      omega
  · exact clockPeierlsFrameDetour_inside_box R j k M hj hRj hM

end FroehlichSpencer.BKT.Clock.Peierls

end
