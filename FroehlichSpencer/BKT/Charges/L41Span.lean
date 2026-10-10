/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Charges.ParentGeometry
public import FroehlichSpencer.BKT.Charges.Geometry
public import FroehlichSpencer.BKT.Surface.SquarePeriodicConnected
public import FroehlichSpencer.BKT.Surface.SquareFreeConnected

/-!
# Coordinate span for lifted squares in L4.1

A pair or triple
of equal-side lifted squares is linked by witnesses whose successive
coordinate displacements are bounded.

The coordinate span is the difference
between the largest upper endpoint and smallest lower endpoint.
-/

@[expose] public section

namespace FroehlichSpencer.BKT

/-- Integer lattice points used for coordinate lifts. -/
abbrev LiftedPoint := ℤ × ℤ

/-- A side-`s` integer square with lower corner `a`, represented as a closed
integer rectangle so that its coordinate width is `s - 1`. -/
def liftedSquare (s : ℕ) (a : LiftedPoint) : Set LiftedPoint :=
  {p | a.1 ≤ p.1 ∧ p.1 ≤ a.1 + (s : ℤ) - 1 ∧
       a.2 ≤ p.2 ∧ p.2 ≤ a.2 + (s : ℤ) - 1}

/-- The coordinate span of two side-`s` intervals with lower endpoints `a`
and `b`. -/
def coordinateSpan₂ (w a b : ℤ) : ℤ :=
  max (a + w) (b + w) - min a b

/-- The coordinate span of three side-`s` intervals with lower endpoints
`a`, `b`, and `c`. -/
def coordinateSpan₃ (w a b c : ℤ) : ℤ :=
  max (a + w) (max (b + w) (c + w)) - min a (min b c)

private theorem max_sub_min_le₂ (u₁ u₂ l₁ l₂ B : ℤ)
    (h₁₁ : u₁ - l₁ ≤ B) (h₁₂ : u₁ - l₂ ≤ B)
    (h₂₁ : u₂ - l₁ ≤ B) (h₂₂ : u₂ - l₂ ≤ B) :
    max u₁ u₂ - min l₁ l₂ ≤ B := by
  by_cases h : l₁ ≤ l₂
  · rw [min_eq_left h]
    have h₁ : u₁ ≤ l₁ + B := by omega
    have h₂ : u₂ ≤ l₁ + B := by omega
    have hm : max u₁ u₂ ≤ l₁ + B := max_le h₁ h₂
    omega
  · have h' : l₂ ≤ l₁ := by omega
    rw [min_eq_right h']
    have h₁ : u₁ ≤ l₂ + B := by omega
    have h₂ : u₂ ≤ l₂ + B := by omega
    have hm : max u₁ u₂ ≤ l₂ + B := max_le h₁ h₂
    omega

private theorem max_sub_min_le₃ (u₁ u₂ u₃ l₁ l₂ l₃ B : ℤ)
    (h₁₁ : u₁ - l₁ ≤ B) (h₁₂ : u₁ - l₂ ≤ B) (h₁₃ : u₁ - l₃ ≤ B)
    (h₂₁ : u₂ - l₁ ≤ B) (h₂₂ : u₂ - l₂ ≤ B) (h₂₃ : u₂ - l₃ ≤ B)
    (h₃₁ : u₃ - l₁ ≤ B) (h₃₂ : u₃ - l₂ ≤ B) (h₃₃ : u₃ - l₃ ≤ B) :
    max u₁ (max u₂ u₃) - min l₁ (min l₂ l₃) ≤ B := by
  rcases min_choice l₁ (min l₂ l₃) with hlo | hlo
  · rw [hlo]
    have h₁ : u₁ ≤ l₁ + B := by omega
    have h₂ : u₂ ≤ l₁ + B := by omega
    have h₃ : u₃ ≤ l₁ + B := by omega
    have hm : max u₁ (max u₂ u₃) ≤ l₁ + B := by
      apply max_le h₁
      exact max_le h₂ h₃
    omega
  · rcases min_choice l₂ l₃ with hlo23 | hlo23
    · rw [hlo, hlo23]
      have h₁ : u₁ ≤ l₂ + B := by omega
      have h₂ : u₂ ≤ l₂ + B := by omega
      have h₃ : u₃ ≤ l₂ + B := by omega
      have hm : max u₁ (max u₂ u₃) ≤ l₂ + B := by
        apply max_le h₁
        exact max_le h₂ h₃
      omega
    · rw [hlo, hlo23]
      have h₁ : u₁ ≤ l₃ + B := by omega
      have h₂ : u₂ ≤ l₃ + B := by omega
      have h₃ : u₃ ≤ l₃ + B := by omega
      have hm : max u₁ (max u₂ u₃) ≤ l₃ + B := by
        apply max_le h₁
        exact max_le h₂ h₃
      omega

private theorem interval_endpoint_bound (a b x y w D : ℤ)
    (ha : a ≤ x) (hby : y ≤ b + w)
    (hxy : x - y ≤ D) :
    a + w - b ≤ D + 2 * w := by
  omega

/-- For two linked intervals of width `s - 1`, a witness displacement at most
`d` gives coordinate span at most `d + 2(s - 1)`. -/
theorem coordinateSpan₂_le (s d : ℕ) (a b x y : ℤ)
    (ha : a ≤ x) (hax : x ≤ a + ((s : ℤ) - 1))
    (hb : b ≤ y) (hby : y ≤ b + ((s : ℤ) - 1))
    (hxy₁ : -(d : ℤ) ≤ x - y) (hxy₂ : x - y ≤ d) :
    coordinateSpan₂ ((s : ℤ) - 1) a b ≤ (d : ℤ) + 2 * ((s : ℤ) - 1) := by
  let w : ℤ := (s : ℤ) - 1
  have hw₁₁ : a + w - a ≤ (d : ℤ) + 2 * w := by omega
  have hw₁₂ : a + w - b ≤ (d : ℤ) + 2 * w :=
    interval_endpoint_bound a b x y w d ha (by dsimp [w] at *; omega) hxy₂
  have hw₂₁ : b + w - a ≤ (d : ℤ) + 2 * w :=
    interval_endpoint_bound b a y x w d hb (by dsimp [w] at *; omega) (by omega)
  have hw₂₂ : b + w - b ≤ (d : ℤ) + 2 * w := by omega
  have hspan := max_sub_min_le₂ (a + w) (b + w) a b
    ((d : ℤ) + 2 * w) hw₁₁ hw₁₂ hw₂₁ hw₂₂
  simpa [coordinateSpan₂, w] using hspan

/-- If the pair link is strictly shorter than `R`, its coordinate span is
strictly below the corresponding threshold `R + 2(s - 1)`. -/
theorem coordinateSpan₂_lt_of_link_lt (s d R : ℕ) (a b x y : ℤ)
    (ha : a ≤ x) (hax : x ≤ a + ((s : ℤ) - 1))
    (hb : b ≤ y) (hby : y ≤ b + ((s : ℤ) - 1))
    (hxy₁ : -(d : ℤ) ≤ x - y) (hxy₂ : x - y ≤ d)
    (hdR : d < R) :
    coordinateSpan₂ ((s : ℤ) - 1) a b < (R : ℤ) + 2 * ((s : ℤ) - 1) := by
  have h := coordinateSpan₂_le s d a b x y ha hax hb hby hxy₁ hxy₂
  omega

/-- For three linked intervals of width `s - 1`, the coordinate span is at
most `d₁ + d₂ + 3(s - 1)`. -/
theorem coordinateSpan₃_le (s d₁ d₂ : ℕ) (a b c x y z : ℤ)
    (ha : a ≤ x) (hax : x ≤ a + ((s : ℤ) - 1))
    (hb : b ≤ y) (hby : y ≤ b + ((s : ℤ) - 1))
    (hc : c ≤ z) (hcz : z ≤ c + ((s : ℤ) - 1))
    (hxy₁ : -(d₁ : ℤ) ≤ x - y) (hxy₂ : x - y ≤ d₁)
    (hyz₁ : -(d₂ : ℤ) ≤ y - z) (hyz₂ : y - z ≤ d₂) :
    coordinateSpan₃ ((s : ℤ) - 1) a b c ≤
      (d₁ : ℤ) + d₂ + 3 * ((s : ℤ) - 1) := by
  let w : ℤ := (s : ℤ) - 1
  let B : ℤ := (d₁ : ℤ) + d₂ + 3 * w
  have hxz₁ : x - z ≤ (d₁ : ℤ) + d₂ := by omega
  have hzx₁ : z - x ≤ (d₁ : ℤ) + d₂ := by omega
  have hxy₃ : y - x ≤ (d₁ : ℤ) + d₂ := by omega
  have hyx₃ : x - y ≤ (d₁ : ℤ) + d₂ := by omega
  have hyz₃ : z - y ≤ (d₁ : ℤ) + d₂ := by omega
  have hzy₃ : y - z ≤ (d₁ : ℤ) + d₂ := by omega
  have h₁₁ : a + w - a ≤ B := by dsimp [B]; omega
  have h₁₂ : a + w - b ≤ B :=
    (interval_endpoint_bound a b x y w ((d₁ : ℤ) + d₂)
      ha (by dsimp [w] at *; omega) hyx₃).trans
        (by dsimp [B]; omega)
  have h₁₃ : a + w - c ≤ B :=
    (interval_endpoint_bound a c x z w ((d₁ : ℤ) + d₂)
      ha (by dsimp [w] at *; omega) hxz₁).trans
        (by dsimp [B]; omega)
  have h₂₁ : b + w - a ≤ B :=
    (interval_endpoint_bound b a y x w ((d₁ : ℤ) + d₂)
      hb (by dsimp [w] at *; omega) hxy₃).trans
        (by dsimp [B]; omega)
  have h₂₂ : b + w - b ≤ B := by dsimp [B]; omega
  have h₂₃ : b + w - c ≤ B :=
    (interval_endpoint_bound b c y z w ((d₁ : ℤ) + d₂)
      hb (by dsimp [w] at *; omega) hzy₃).trans
        (by dsimp [B]; omega)
  have h₃₁ : c + w - a ≤ B :=
    (interval_endpoint_bound c a z x w ((d₁ : ℤ) + d₂)
      hc (by dsimp [w] at *; omega) hzx₁).trans
        (by dsimp [B]; omega)
  have h₃₂ : c + w - b ≤ B :=
    (interval_endpoint_bound c b z y w ((d₁ : ℤ) + d₂)
      hc (by dsimp [w] at *; omega) hyz₃).trans
        (by dsimp [B]; omega)
  have h₃₃ : c + w - c ≤ B := by dsimp [B]; omega
  have hspan := max_sub_min_le₃ (a + w) (b + w) (c + w) a b c B
    h₁₁ h₁₂ h₁₃ h₂₁ h₂₂ h₂₃ h₃₁ h₃₂ h₃₃
  simpa [coordinateSpan₃, w, B] using hspan

/-- If both links of a triple path are shorter than `R`, its coordinate span
is strictly below `2R + 3(s - 1)`. -/
theorem coordinateSpan₃_lt_of_links_lt (s d₁ d₂ R : ℕ)
    (a b c x y z : ℤ)
    (ha : a ≤ x) (hax : x ≤ a + ((s : ℤ) - 1))
    (hb : b ≤ y) (hby : y ≤ b + ((s : ℤ) - 1))
    (hc : c ≤ z) (hcz : z ≤ c + ((s : ℤ) - 1))
    (hxy₁ : -(d₁ : ℤ) ≤ x - y) (hxy₂ : x - y ≤ d₁)
    (hyz₁ : -(d₂ : ℤ) ≤ y - z) (hyz₂ : y - z ≤ d₂)
    (hd₁R : d₁ < R) (hd₂R : d₂ < R) :
    coordinateSpan₃ ((s : ℤ) - 1) a b c <
      2 * (R : ℤ) + 3 * ((s : ℤ) - 1) := by
  have h := coordinateSpan₃_le s d₁ d₂ a b c x y z
    ha hax hb hby hc hcz hxy₁ hxy₂ hyz₁ hyz₂
  omega

private theorem pair_interval_cover (a b w N : ℤ)
    (hspan : coordinateSpan₂ w a b < N) :
    ∃ c : ℤ, ∀ x : ℤ,
      (a ≤ x ∧ x ≤ a + w) ∨ (b ≤ x ∧ x ≤ b + w) →
        c ≤ x ∧ x ≤ c + N - 1 := by
  let c := min a b
  have hspan' : max (a + w) (b + w) - c < N := by
    change max (a + w) (b + w) - min a b < N at hspan
    exact hspan
  have hca : c ≤ a := min_le_left a b
  have hcb : c ≤ b := min_le_right a b
  have hua : a + w ≤ c + N - 1 := by
    have hmax : max (a + w) (b + w) ≤ c + N - 1 := by omega
    exact (le_max_left _ _).trans hmax
  have hub : b + w ≤ c + N - 1 := by
    have hmax : max (a + w) (b + w) ≤ c + N - 1 := by omega
    exact (le_max_right _ _).trans hmax
  refine ⟨c, ?_⟩
  intro x hx
  rcases hx with hx | hx
  · exact ⟨hca.trans hx.1, hx.2.trans hua⟩
  · exact ⟨hcb.trans hx.1, hx.2.trans hub⟩

private theorem triple_interval_cover (a b c w N : ℤ)
    (hspan : coordinateSpan₃ w a b c < N) :
    ∃ d : ℤ, ∀ x : ℤ,
      (a ≤ x ∧ x ≤ a + w) ∨ (b ≤ x ∧ x ≤ b + w) ∨
        (c ≤ x ∧ x ≤ c + w) →
        d ≤ x ∧ x ≤ d + N - 1 := by
  let d := min a (min b c)
  have hspan' := hspan
  change max (a + w) (max (b + w) (c + w)) - d < N at hspan'
  have hda : d ≤ a := min_le_left a (min b c)
  have hdb : d ≤ b := (min_le_right a (min b c)).trans (min_le_left b c)
  have hdc : d ≤ c := (min_le_right a (min b c)).trans (min_le_right b c)
  have hspanA : a + w - d < N :=
    (sub_le_sub_right (le_max_left _ _) d).trans_lt hspan'
  have hspanB : b + w - d < N :=
    (sub_le_sub_right
      (le_trans (le_max_left _ _) (le_max_right _ _)) d).trans_lt hspan'
  have hspanC : c + w - d < N :=
    (sub_le_sub_right
      (le_trans (le_max_right _ _) (le_max_right _ _)) d).trans_lt hspan'
  have hua : a + w ≤ d + N - 1 := by omega
  have hub : b + w ≤ d + N - 1 := by omega
  have huc : c + w ≤ d + N - 1 := by omega
  refine ⟨d, ?_⟩
  intro x hx
  rcases hx with hx | hx | hx
  · exact ⟨hda.trans hx.1, hx.2.trans hua⟩
  · exact ⟨hdb.trans hx.1, hx.2.trans hub⟩
  · exact ⟨hdc.trans hx.1, hx.2.trans huc⟩

/-- A pair of side-`s` lifted squares linked by coordinate witnesses fits in
one side-`N` integer square whenever the pair span is less than `N`. -/
theorem pair_liftedSquares_fit (s N d : ℕ)
    (a b p q : LiftedPoint)
    (hp : p ∈ liftedSquare s a) (hq : q ∈ liftedSquare s b)
    (hx₁ : -(d : ℤ) ≤ p.1 - q.1) (hx₂ : p.1 - q.1 ≤ d)
    (hy₁ : -(d : ℤ) ≤ p.2 - q.2) (hy₂ : p.2 - q.2 ≤ d)
    (hbudget : (d : ℤ) + 2 * ((s : ℤ) - 1) < (N : ℤ)) :
    ∃ c : LiftedPoint,
      liftedSquare s a ∪ liftedSquare s b ⊆ liftedSquare N c := by
  change a.1 ≤ p.1 ∧ p.1 ≤ a.1 + (s : ℤ) - 1 ∧
      a.2 ≤ p.2 ∧ p.2 ≤ a.2 + (s : ℤ) - 1 at hp
  change b.1 ≤ q.1 ∧ q.1 ≤ b.1 + (s : ℤ) - 1 ∧
      b.2 ≤ q.2 ∧ q.2 ≤ b.2 + (s : ℤ) - 1 at hq
  have hpx : p.1 ≤ a.1 + ((s : ℤ) - 1) := by omega
  have hpy : p.2 ≤ a.2 + ((s : ℤ) - 1) := by omega
  have hqx : q.1 ≤ b.1 + ((s : ℤ) - 1) := by omega
  have hqy : q.2 ≤ b.2 + ((s : ℤ) - 1) := by omega
  have hspanX := coordinateSpan₂_le s d a.1 b.1 p.1 q.1
    hp.1 hpx hq.1 hqx hx₁ hx₂
  have hspanY := coordinateSpan₂_le s d a.2 b.2 p.2 q.2
    hp.2.2.1 hpy hq.2.2.1 hqy hy₁ hy₂
  have hspanX' : coordinateSpan₂ ((s : ℤ) - 1) a.1 b.1 < (N : ℤ) := by
    omega
  have hspanY' : coordinateSpan₂ ((s : ℤ) - 1) a.2 b.2 < (N : ℤ) := by
    omega
  obtain ⟨cx, hcx⟩ := pair_interval_cover a.1 b.1 ((s : ℤ) - 1) N hspanX'
  obtain ⟨cy, hcy⟩ := pair_interval_cover a.2 b.2 ((s : ℤ) - 1) N hspanY'
  refine ⟨(cx, cy), ?_⟩
  intro z hz
  rcases hz with hz | hz
  · change a.1 ≤ z.1 ∧ z.1 ≤ a.1 + (s : ℤ) - 1 ∧
      a.2 ≤ z.2 ∧ z.2 ≤ a.2 + (s : ℤ) - 1 at hz
    have hzx : z.1 ≤ a.1 + ((s : ℤ) - 1) := by omega
    have hzy : z.2 ≤ a.2 + ((s : ℤ) - 1) := by omega
    have hx := hcx z.1 (Or.inl ⟨hz.1, hzx⟩)
    have hy := hcy z.2 (Or.inl ⟨hz.2.2.1, hzy⟩)
    change cx ≤ z.1 ∧ z.1 ≤ cx + (N : ℤ) - 1 ∧
      cy ≤ z.2 ∧ z.2 ≤ cy + (N : ℤ) - 1
    exact ⟨hx.1, hx.2, hy.1, hy.2⟩
  · change b.1 ≤ z.1 ∧ z.1 ≤ b.1 + (s : ℤ) - 1 ∧
      b.2 ≤ z.2 ∧ z.2 ≤ b.2 + (s : ℤ) - 1 at hz
    have hzx : z.1 ≤ b.1 + ((s : ℤ) - 1) := by omega
    have hzy : z.2 ≤ b.2 + ((s : ℤ) - 1) := by omega
    have hx := hcx z.1 (Or.inr ⟨hz.1, hzx⟩)
    have hy := hcy z.2 (Or.inr ⟨hz.2.2.1, hzy⟩)
    change cx ≤ z.1 ∧ z.1 ≤ cx + (N : ℤ) - 1 ∧
      cy ≤ z.2 ∧ z.2 ≤ cy + (N : ℤ) - 1
    exact ⟨hx.1, hx.2, hy.1, hy.2⟩

/-- A three-box lifted path fits in one side-`N` integer square under the
corresponding three-width span budget. -/
theorem triple_liftedSquares_fit (s N d₁ d₂ : ℕ)
    (a b c p q r : LiftedPoint)
    (hp : p ∈ liftedSquare s a) (hq : q ∈ liftedSquare s b)
    (hr : r ∈ liftedSquare s c)
    (hx₁ : -(d₁ : ℤ) ≤ p.1 - q.1) (hx₂ : p.1 - q.1 ≤ d₁)
    (hx₃ : -(d₂ : ℤ) ≤ q.1 - r.1) (hx₄ : q.1 - r.1 ≤ d₂)
    (hy₁ : -(d₁ : ℤ) ≤ p.2 - q.2) (hy₂ : p.2 - q.2 ≤ d₁)
    (hy₃ : -(d₂ : ℤ) ≤ q.2 - r.2) (hy₄ : q.2 - r.2 ≤ d₂)
    (hbudget : (d₁ : ℤ) + d₂ + 3 * ((s : ℤ) - 1) < (N : ℤ)) :
    ∃ d : LiftedPoint,
      liftedSquare s a ∪ liftedSquare s b ∪ liftedSquare s c ⊆ liftedSquare N d := by
  change a.1 ≤ p.1 ∧ p.1 ≤ a.1 + (s : ℤ) - 1 ∧
      a.2 ≤ p.2 ∧ p.2 ≤ a.2 + (s : ℤ) - 1 at hp
  change b.1 ≤ q.1 ∧ q.1 ≤ b.1 + (s : ℤ) - 1 ∧
      b.2 ≤ q.2 ∧ q.2 ≤ b.2 + (s : ℤ) - 1 at hq
  change c.1 ≤ r.1 ∧ r.1 ≤ c.1 + (s : ℤ) - 1 ∧
      c.2 ≤ r.2 ∧ r.2 ≤ c.2 + (s : ℤ) - 1 at hr
  have hpx : p.1 ≤ a.1 + ((s : ℤ) - 1) := by omega
  have hpy : p.2 ≤ a.2 + ((s : ℤ) - 1) := by omega
  have hqx : q.1 ≤ b.1 + ((s : ℤ) - 1) := by omega
  have hqy : q.2 ≤ b.2 + ((s : ℤ) - 1) := by omega
  have hrx : r.1 ≤ c.1 + ((s : ℤ) - 1) := by omega
  have hry : r.2 ≤ c.2 + ((s : ℤ) - 1) := by omega
  have hspanX := coordinateSpan₃_le s d₁ d₂ a.1 b.1 c.1 p.1 q.1 r.1
    hp.1 hpx hq.1 hqx hr.1 hrx hx₁ hx₂ hx₃ hx₄
  have hspanY := coordinateSpan₃_le s d₁ d₂ a.2 b.2 c.2 p.2 q.2 r.2
    hp.2.2.1 hpy hq.2.2.1 hqy hr.2.2.1 hry hy₁ hy₂ hy₃ hy₄
  have hspanX' : coordinateSpan₃ ((s : ℤ) - 1) a.1 b.1 c.1 < (N : ℤ) := by
    omega
  have hspanY' : coordinateSpan₃ ((s : ℤ) - 1) a.2 b.2 c.2 < (N : ℤ) := by
    omega
  obtain ⟨dx, hdx⟩ := triple_interval_cover a.1 b.1 c.1
    ((s : ℤ) - 1) N hspanX'
  obtain ⟨dy, hdy⟩ := triple_interval_cover a.2 b.2 c.2
    ((s : ℤ) - 1) N hspanY'
  refine ⟨(dx, dy), ?_⟩
  intro z hz
  rcases hz with (hz | hz) | hz
  · change a.1 ≤ z.1 ∧ z.1 ≤ a.1 + (s : ℤ) - 1 ∧
      a.2 ≤ z.2 ∧ z.2 ≤ a.2 + (s : ℤ) - 1 at hz
    have hzx : z.1 ≤ a.1 + ((s : ℤ) - 1) := by omega
    have hzy : z.2 ≤ a.2 + ((s : ℤ) - 1) := by omega
    have hx := hdx z.1 (Or.inl ⟨hz.1, hzx⟩)
    have hy := hdy z.2 (Or.inl ⟨hz.2.2.1, hzy⟩)
    change dx ≤ z.1 ∧ z.1 ≤ dx + (N : ℤ) - 1 ∧
      dy ≤ z.2 ∧ z.2 ≤ dy + (N : ℤ) - 1
    exact ⟨hx.1, hx.2, hy.1, hy.2⟩
  · change b.1 ≤ z.1 ∧ z.1 ≤ b.1 + (s : ℤ) - 1 ∧
      b.2 ≤ z.2 ∧ z.2 ≤ b.2 + (s : ℤ) - 1 at hz
    have hzx : z.1 ≤ b.1 + ((s : ℤ) - 1) := by omega
    have hzy : z.2 ≤ b.2 + ((s : ℤ) - 1) := by omega
    have hx := hdx z.1 (Or.inr (Or.inl ⟨hz.1, hzx⟩))
    have hy := hdy z.2 (Or.inr (Or.inl ⟨hz.2.2.1, hzy⟩))
    change dx ≤ z.1 ∧ z.1 ≤ dx + (N : ℤ) - 1 ∧
      dy ≤ z.2 ∧ z.2 ≤ dy + (N : ℤ) - 1
    exact ⟨hx.1, hx.2, hy.1, hy.2⟩
  · change c.1 ≤ z.1 ∧ z.1 ≤ c.1 + (s : ℤ) - 1 ∧
      c.2 ≤ z.2 ∧ z.2 ≤ c.2 + (s : ℤ) - 1 at hz
    have hzx : z.1 ≤ c.1 + ((s : ℤ) - 1) := by omega
    have hzy : z.2 ≤ c.2 + ((s : ℤ) - 1) := by omega
    have hx := hdx z.1 (Or.inr (Or.inr ⟨hz.1, hzx⟩))
    have hy := hdy z.2 (Or.inr (Or.inr ⟨hz.2.2.1, hzy⟩))
    change dx ≤ z.1 ∧ z.1 ≤ dx + (N : ℤ) - 1 ∧
      dy ≤ z.2 ∧ z.2 ≤ dy + (N : ℤ) - 1
    exact ⟨hx.1, hx.2, hy.1, hy.2⟩

/-- The quotient coordinate of an integer modulo the period. -/
def periodicCoordinate (L : ℕ) (hL : 0 < L) (x : ℤ) : Fin L :=
  ⟨(x % (L : ℤ)).toNat, by
    rw [Int.toNat_lt_of_ne_zero (Nat.ne_of_gt hL)]
    exact Int.emod_lt_of_pos _ (by exact_mod_cast hL)⟩

/-- Coordinatewise projection from the lifted lattice to the periodic square. -/
def periodicProjection (L : ℕ) (hL : 0 < L) (p : LiftedPoint) : Fin L × Fin L :=
  (periodicCoordinate L hL p.1, periodicCoordinate L hL p.2)

/-- Translating a lifted coordinate by a natural offset adds that offset
modulo the period after projection. -/
theorem periodicCoordinate_add_nat (L : ℕ) (hL : 0 < L) (a : ℤ) (i : ℕ) :
    (periodicCoordinate L hL (a + (i : ℤ))).val =
      ((periodicCoordinate L hL a).val + i) % L := by
  apply Nat.cast_injective (R := ℤ)
  simp only [Int.natCast_mod, Nat.cast_add]
  have hLz : (L : ℤ) ≠ 0 := by exact_mod_cast hL.ne'
  simp only [periodicCoordinate, Int.natCast_toNat_eq_self.mpr
    (Int.emod_nonneg (a + (i : ℤ)) hLz)]
  have haNat : (((a % (L : ℤ)).toNat : ℕ) : ℤ) = a % (L : ℤ) :=
    Int.natCast_toNat_eq_self.mpr (Int.emod_nonneg a hLz)
  rw [haNat]
  exact Int.ModEq.eq ((Int.ModEq.symm (Int.mod_modEq a (L : ℤ))).add_right _)

/-- The lifted coordinate and its quotient representative are congruent modulo
the period. -/
theorem periodicCoordinate_modEq (L : ℕ) (hL : 0 < L) (x : ℤ) :
    x ≡ (periodicCoordinate L hL x).val [ZMOD L] := by
  have hLz : (L : ℤ) ≠ 0 := by exact_mod_cast hL.ne'
  have hval : ((periodicCoordinate L hL x).val : ℤ) = x % (L : ℤ) := by
    simp [periodicCoordinate, Int.natCast_toNat_eq_self.mpr
      (Int.emod_nonneg x hLz)]
  calc
    x ≡ x % (L : ℤ) [ZMOD L] := Int.ModEq.symm (Int.mod_modEq x (L : ℤ))
    _ ≡ (periodicCoordinate L hL x).val [ZMOD L] := by
      rw [hval]

/-- Congruent lifted coordinates project to the same torus coordinate. -/
theorem periodicCoordinate_eq_of_modEq (L : ℕ) (hL : 0 < L) (x y : ℤ)
    (hxy : x ≡ y [ZMOD L]) :
    periodicCoordinate L hL x = periodicCoordinate L hL y := by
  apply Fin.ext
  change (x % (L : ℤ)).toNat = (y % (L : ℤ)).toNat
  exact congrArg Int.toNat hxy.eq

/-- Adding an integer period does not change the projected coordinate. -/
theorem periodicCoordinate_add_period (L : ℕ) (hL : 0 < L) (a t : ℤ) :
    periodicCoordinate L hL (a + (L : ℤ) * t) = periodicCoordinate L hL a := by
  apply periodicCoordinate_eq_of_modEq
  exact (Int.modEq_iff_dvd).2 ⟨-t, by ring⟩

/-- A natural representative already in the fundamental period projects to
itself. -/
theorem periodicCoordinate_finVal (L : ℕ) (hL : 0 < L) (x : Fin L) :
    periodicCoordinate L hL (x.val : ℤ) = x := by
  apply Fin.ext
  simp only [periodicCoordinate]
  rw [Int.emod_eq_of_lt (by exact_mod_cast Nat.zero_le x.val)
    (by exact_mod_cast x.isLt)]
  simp

/-- Equality of quotient coordinates is equivalent to congruence of their
integer representatives modulo the period. -/
theorem periodicCoordinate_eq_implies_modEq (L : ℕ) (hL : 0 < L)
    (x y : ℤ) (hxy : periodicCoordinate L hL x = periodicCoordinate L hL y) :
    x ≡ y [ZMOD L] := by
  have hx := periodicCoordinate_modEq L hL x
  have hy := periodicCoordinate_modEq L hL y
  have hval : ((periodicCoordinate L hL x).val : ℤ) =
      (periodicCoordinate L hL y).val := by
    exact_mod_cast congrArg Fin.val hxy
  calc
    x ≡ (periodicCoordinate L hL x).val [ZMOD L] := hx
    _ ≡ (periodicCoordinate L hL y).val [ZMOD L] := by
      rw [hval]
    _ ≡ y [ZMOD L] := hy.symm

/-- Two lifted integer coordinates with the same quotient representative
differ by an integer multiple of the period. -/
theorem periodicCoordinate_exists_period_translation
    (L : ℕ) (hL : 0 < L) (x y : ℤ)
    (hxy : periodicCoordinate L hL x = periodicCoordinate L hL y) :
    ∃ t : ℤ, y = x + (L : ℤ) * t := by
  have hmod := periodicCoordinate_eq_implies_modEq L hL x y hxy
  rcases (Int.modEq_iff_dvd).mp hmod with ⟨t, ht⟩
  refine ⟨t, ?_⟩
  calc
    y = x + (y - x) := by omega
    _ = x + (L : ℤ) * t := by rw [ht]

/-- Coordinatewise version of the period-translation alignment. -/
theorem periodicProjection_exists_period_translation
    (L : ℕ) (hL : 0 < L) (p q : LiftedPoint)
    (hpq : periodicProjection L hL p = periodicProjection L hL q) :
    ∃ t : LiftedPoint,
      q = (p.1 + (L : ℤ) * t.1, p.2 + (L : ℤ) * t.2) := by
  obtain ⟨tx, hx⟩ := periodicCoordinate_exists_period_translation L hL p.1 q.1
    (congrArg Prod.fst hpq)
  obtain ⟨ty, hy⟩ := periodicCoordinate_exists_period_translation L hL p.2 q.2
    (congrArg Prod.snd hpq)
  exact ⟨(tx, ty), Prod.ext hx hy⟩

/-- Every point in a periodic square has a lift in the corresponding lifted
integer square. -/
theorem periodicSquare_exists_lifted_witness
    (L k : ℕ) (hL : 0 < L) (hside : squareSide k < L)
    (a : LiftedPoint) (x : Fin L × Fin L)
    (hx : x ∈ kpSquare .periodic L k (periodicProjection L hL a)) :
    ∃ p : LiftedPoint, p ∈ liftedSquare (squareSide k) a ∧
      periodicProjection L hL p = x := by
  obtain ⟨i, hi, j, hj, hxi, hxj⟩ :=
    (mem_kpSquare_periodic_iff L k hside
      (periodicProjection L hL a) x).1 hx
  let p : LiftedPoint := (a.1 + (i : ℤ), a.2 + (j : ℤ))
  have hiZ : (i : ℤ) ≤ (squareSide k : ℤ) - 1 := by
    have hlt : (i : ℤ) < squareSide k := by exact_mod_cast Finset.mem_range.mp hi
    omega
  have hjZ : (j : ℤ) ≤ (squareSide k : ℤ) - 1 := by
    have hlt : (j : ℤ) < squareSide k := by exact_mod_cast Finset.mem_range.mp hj
    omega
  refine ⟨p, ?_, ?_⟩
  · change a.1 ≤ p.1 ∧ p.1 ≤ a.1 + (squareSide k : ℤ) - 1 ∧
      a.2 ≤ p.2 ∧ p.2 ≤ a.2 + (squareSide k : ℤ) - 1
    dsimp [p]
    exact ⟨by omega, by omega, by omega, by omega⟩
  · apply Prod.ext
    · apply Fin.ext
      change (periodicCoordinate L hL (a.1 + (i : ℤ))).val = x.1.val
      rw [periodicCoordinate_add_nat]
      exact hxi.symm
    · apply Fin.ext
      change (periodicCoordinate L hL (a.2 + (j : ℤ))).val = x.2.val
      rw [periodicCoordinate_add_nat]
      exact hxj.symm

/-- Translate a lifted periodic square so that a chosen lift of one of its
quotient vertices is exactly represented inside the translated square. -/
theorem periodicSquare_align_lifted_witness
    (L k : ℕ) (hL : 0 < L) (hside : squareSide k < L)
    (a p : LiftedPoint)
    (hp : periodicProjection L hL p ∈
      kpSquare .periodic L k (periodicProjection L hL a)) :
    ∃ a' : LiftedPoint,
      periodicProjection L hL a' = periodicProjection L hL a ∧
      p ∈ liftedSquare (squareSide k) a' := by
  obtain ⟨i, hi, j, hj, hpx, hpy⟩ :=
    (mem_kpSquare_periodic_iff L k hside
      (periodicProjection L hL a) (periodicProjection L hL p)).1 hp
  let b : LiftedPoint := (a.1 + (i : ℤ), a.2 + (j : ℤ))
  have hbp : periodicProjection L hL b = periodicProjection L hL p := by
    apply Prod.ext
    · apply Fin.ext
      change (periodicCoordinate L hL (a.1 + (i : ℤ))).val =
        (periodicCoordinate L hL p.1).val
      rw [periodicCoordinate_add_nat]
      exact hpx.symm
    · apply Fin.ext
      change (periodicCoordinate L hL (a.2 + (j : ℤ))).val =
        (periodicCoordinate L hL p.2).val
      rw [periodicCoordinate_add_nat]
      exact hpy.symm
  obtain ⟨t, ht⟩ := periodicProjection_exists_period_translation L hL b p hbp
  let a' : LiftedPoint := (a.1 + (L : ℤ) * t.1, a.2 + (L : ℤ) * t.2)
  have hanchor : periodicProjection L hL a' = periodicProjection L hL a := by
    apply Prod.ext
    · change periodicCoordinate L hL (a.1 + (L : ℤ) * t.1) =
        periodicCoordinate L hL a.1
      exact periodicCoordinate_add_period L hL a.1 t.1
    · change periodicCoordinate L hL (a.2 + (L : ℤ) * t.2) =
        periodicCoordinate L hL a.2
      exact periodicCoordinate_add_period L hL a.2 t.2
  have hpx' : p.1 = a'.1 + (i : ℤ) := by
    have h := congrArg Prod.fst ht
    dsimp [b] at h
    dsimp [a']
    rw [h]
    ring
  have hpy' : p.2 = a'.2 + (j : ℤ) := by
    have h := congrArg Prod.snd ht
    dsimp [b] at h
    dsimp [a']
    rw [h]
    ring
  have hiZ : (i : ℤ) ≤ (squareSide k : ℤ) - 1 := by
    have hlt : (i : ℤ) < squareSide k := by exact_mod_cast Finset.mem_range.mp hi
    omega
  have hjZ : (j : ℤ) ≤ (squareSide k : ℤ) - 1 := by
    have hlt : (j : ℤ) < squareSide k := by exact_mod_cast Finset.mem_range.mp hj
    omega
  refine ⟨a', hanchor, ?_⟩
  change a'.1 ≤ p.1 ∧ p.1 ≤ a'.1 + (squareSide k : ℤ) - 1 ∧
    a'.2 ≤ p.2 ∧ p.2 ≤ a'.2 + (squareSide k : ℤ) - 1
  rw [hpx', hpy']
  exact ⟨by omega, by omega, by omega, by omega⟩

/--
The edge relation used to define the periodic multigraph, with its
orientation forgotten.
-/
def periodicEdgeRelation (L : ℕ) (x y : Fin L × Fin L) : Prop :=
  ∃ e : SquarePeriodicEdge L,
    (e.1.1 = x ∧ e.1.2 = y) ∨ (e.1.1 = y ∧ e.1.2 = x)

/--
Adjacency in the periodic graph is exactly the unoriented
`SquarePeriodicEdge` relation.
-/
theorem periodicAdj_iff_edgeRelation (L : ℕ) (x y : Fin L × Fin L) :
    (squarePeriodic L).toSimpleGraph.Adj x y ↔
      x ≠ y ∧ periodicEdgeRelation L x y := by
  rw [Multigraph.toSimpleGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hne, (⟨e, he | he⟩ | ⟨e, he | he⟩)⟩
    · exact ⟨hne, ⟨e, Or.inl he⟩⟩
    · exact ⟨hne, ⟨e, Or.inr he⟩⟩
    · exact ⟨hne, ⟨e, Or.inr he⟩⟩
    · exact ⟨hne, ⟨e, Or.inl he⟩⟩
  · rintro ⟨hne, ⟨e, he | he⟩⟩
    · exact ⟨hne, Or.inl ⟨e, Or.inl he⟩⟩
    · exact ⟨hne, Or.inl ⟨e, Or.inr he⟩⟩

/--
The edge relation used to define the free multigraph, with its
orientation forgotten.
-/
def freeEdgeRelation (L : ℕ) (x y : Fin L × Fin L) : Prop :=
  ∃ e : SquareFreeEdge L,
    (e.1.1 = x ∧ e.1.2 = y) ∨ (e.1.1 = y ∧ e.1.2 = x)

/--
Adjacency in the free graph is the unoriented
`SquareFreeEdge` relation.
-/
theorem freeAdj_iff_edgeRelation (L : ℕ) (x y : Fin L × Fin L) :
    (squareFree L).toSimpleGraph.Adj x y ↔ x ≠ y ∧ freeEdgeRelation L x y := by
  rw [Multigraph.toSimpleGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hne, (⟨e, he | he⟩ | ⟨e, he | he⟩)⟩
    · exact ⟨hne, ⟨e, Or.inl he⟩⟩
    · exact ⟨hne, ⟨e, Or.inr he⟩⟩
    · exact ⟨hne, ⟨e, Or.inr he⟩⟩
    · exact ⟨hne, ⟨e, Or.inl he⟩⟩
  · rintro ⟨hne, ⟨e, he | he⟩⟩
    · exact ⟨hne, Or.inl ⟨e, Or.inl he⟩⟩
    · exact ⟨hne, Or.inl ⟨e, Or.inr he⟩⟩

/-- Every free graph edge changes each integer coordinate by at most one. -/
private theorem freeEdge_coordinate_abs_bound (L : ℕ) (e : SquareFreeEdge L) :
    |(e.1.1.1.val : ℤ) - e.1.2.1.val| ≤ 1 ∧
    |(e.1.1.2.val : ℤ) - e.1.2.2.val| ≤ 1 := by
  have hshape := e.property.2
  let dx := |(e.1.1.1.val : ℤ) - e.1.2.1.val|
  let dy := |(e.1.1.2.val : ℤ) - e.1.2.2.val|
  have hshape' : ({dx, dy} : Finset ℤ) = {0, 1} := by
    simpa [dx, dy] using hshape
  have hmem₁ : |(e.1.1.1.val : ℤ) - e.1.2.1.val| ∈
      ({0, 1} : Finset ℤ) := by
    change dx ∈ ({0, 1} : Finset ℤ)
    rw [← hshape']
    simp [dx]
  have hmem₂ : |(e.1.1.2.val : ℤ) - e.1.2.2.val| ∈
      ({0, 1} : Finset ℤ) := by
    change dy ∈ ({0, 1} : Finset ℤ)
    rw [← hshape']
    simp [dy]
  have h₁ : |(e.1.1.1.val : ℤ) - e.1.2.1.val| = 0 ∨
      |(e.1.1.1.val : ℤ) - e.1.2.1.val| = 1 := by simpa using hmem₁
  have h₂ : |(e.1.1.2.val : ℤ) - e.1.2.2.val| = 0 ∨
      |(e.1.1.2.val : ℤ) - e.1.2.2.val| = 1 := by simpa using hmem₂
  constructor
  · rcases h₁ with h | h
    · simp [h]
    · simp [h]
  · rcases h₂ with h | h
    · simp [h]
    · simp [h]

theorem freeAdj_coordinate_bound (L : ℕ) (x y : Fin L × Fin L)
    (hxy : (squareFree L).toSimpleGraph.Adj x y) :
    |(x.1.val : ℤ) - y.1.val| ≤ 1 ∧ |(x.2.val : ℤ) - y.2.val| ≤ 1 := by
  have hedge := ((freeAdj_iff_edgeRelation L x y).mp hxy).2
  rcases hedge with ⟨e, he | he⟩
  · rw [← he.1, ← he.2]
    exact freeEdge_coordinate_abs_bound L e
  · rw [← he.1, ← he.2]
    have hbound := freeEdge_coordinate_abs_bound L e
    exact ⟨by simpa [abs_sub_comm] using hbound.1,
      by simpa [abs_sub_comm] using hbound.2⟩

/-- A free graph walk changes either integer coordinate by at most its
length. -/
theorem freeWalk_coordinate_bound {L : ℕ} {x y : Fin L × Fin L}
    (w : (squareFree L).toSimpleGraph.Walk x y) :
    -((w.length : ℕ) : ℤ) ≤ (y.1.val : ℤ) - x.1.val ∧
      (y.1.val : ℤ) - x.1.val ≤ w.length ∧
      -((w.length : ℕ) : ℤ) ≤ (y.2.val : ℤ) - x.2.val ∧
      (y.2.val : ℤ) - x.2.val ≤ w.length := by
  induction w with
  | nil => simp
  | @cons a b c habc tail ih =>
      have hstep := freeAdj_coordinate_bound L a b habc
      have hstepX : -(1 : ℤ) ≤ (b.1.val : ℤ) - a.1.val ∧
          (b.1.val : ℤ) - a.1.val ≤ 1 := by
        have hab := abs_le.mp hstep.1
        constructor <;> omega
      have hstepY : -(1 : ℤ) ≤ (b.2.val : ℤ) - a.2.val ∧
          (b.2.val : ℤ) - a.2.val ≤ 1 := by
        have hab := abs_le.mp hstep.2
        constructor <;> omega
      rcases ih with ⟨ihXlo, ihXhi, ihYlo, ihYhi⟩
      rcases hstepX with ⟨hXlo, hXhi⟩
      rcases hstepY with ⟨hYlo, hYhi⟩
      simp only [SimpleGraph.Walk.length_cons, Nat.cast_add, Nat.cast_one]
      constructor <;> omega

/-- The free graph distance bounds each coordinate displacement. -/
theorem freeDistance_coordinate_bound (L : ℕ) (hL : 1 < L)
    (x y : Fin L × Fin L) :
    -((latticeDistance .free L x y : ℕ) : ℤ) ≤ (y.1.val : ℤ) - x.1.val ∧
      (y.1.val : ℤ) - x.1.val ≤ latticeDistance .free L x y ∧
      -((latticeDistance .free L x y : ℕ) : ℤ) ≤ (y.2.val : ℤ) - x.2.val ∧
      (y.2.val : ℤ) - x.2.val ≤ latticeDistance .free L x y := by
  let G := (squareFree L).toSimpleGraph
  have hconn : G.Connected := squareFree_connected L hL
  obtain ⟨w, hw⟩ := hconn x y |>.exists_walk_length_eq_dist
  have hw' : w.length = latticeDistance .free L x y := by
    simpa [G, latticeDistance] using hw
  have hwalk := freeWalk_coordinate_bound w
  have hlen : (w.length : ℤ) = (latticeDistance .free L x y : ℤ) := by
    exact_mod_cast hw'
  rcases hwalk with ⟨hxlo, hxhi, hylo, hyhi⟩
  exact ⟨by omega, by omega, by omega, by omega⟩

/-- The coordinate form of a single periodic nearest-neighbor edge. -/
def periodicUnitRelation (L : ℕ) (x y : Fin L × Fin L) : Prop :=
  (x.1 = y.1 ∧
    (((x.2.val : ℤ) ≡ (y.2.val : ℤ) + 1 [ZMOD L]) ∨
      ((y.2.val : ℤ) ≡ (x.2.val : ℤ) + 1 [ZMOD L]))) ∨
  (x.2 = y.2 ∧
    (((x.1.val : ℤ) ≡ (y.1.val : ℤ) + 1 [ZMOD L]) ∨
      ((y.1.val : ℤ) ≡ (x.1.val : ℤ) + 1 [ZMOD L])))

private theorem periodicUnitRelation_symm (L : ℕ) {x y : Fin L × Fin L}
    (h : periodicUnitRelation L x y) : periodicUnitRelation L y x := by
  rcases h with (⟨heq, h | h⟩) | (⟨heq, h | h⟩)
  · exact Or.inl ⟨heq.symm, Or.inr h⟩
  · exact Or.inl ⟨heq.symm, Or.inl h⟩
  · exact Or.inr ⟨heq.symm, Or.inr h⟩
  · exact Or.inr ⟨heq.symm, Or.inl h⟩

/--
The endpoint condition on a  periodic edge gives the coordinate
unit-step relation, independent of its chosen lexicographic orientation.
-/
theorem periodicEdgeRelation_unit (L : ℕ) {x y : Fin L × Fin L}
    (h : periodicEdgeRelation L x y) : periodicUnitRelation L x y := by
  rcases h with ⟨e, he | he⟩
  · rw [← he.1, ← he.2]
    exact e.property.2
  · rw [← he.1, ← he.2]
    exact periodicUnitRelation_symm L e.property.2

/-- Lift one periodic graph edge from a chosen lift of its initial vertex.
The endpoint changes by at most one in each coordinate. -/
theorem periodicAdj_lift_step (L : ℕ) (hL : 0 < L)
    (x y : Fin L × Fin L)
    (hxy : (squarePeriodic L).toSimpleGraph.Adj x y)
    (p : LiftedPoint) (hp : periodicProjection L hL p = x) :
    ∃ q : LiftedPoint, periodicProjection L hL q = y ∧
      -(1 : ℤ) ≤ q.1 - p.1 ∧ q.1 - p.1 ≤ 1 ∧
      -(1 : ℤ) ≤ q.2 - p.2 ∧ q.2 - p.2 ≤ 1 := by
  have hunit : periodicUnitRelation L x y :=
    periodicEdgeRelation_unit L ((periodicAdj_iff_edgeRelation L x y).mp hxy).2
  have hpx : p.1 ≡ (x.1.val : ℤ) [ZMOD L] := by
    have h := periodicCoordinate_modEq L hL p.1
    rw [show periodicCoordinate L hL p.1 = x.1 by
      simpa [periodicProjection] using congrArg Prod.fst hp] at h
    exact h
  have hpy : p.2 ≡ (x.2.val : ℤ) [ZMOD L] := by
    have h := periodicCoordinate_modEq L hL p.2
    rw [show periodicCoordinate L hL p.2 = x.2 by
      simpa [periodicProjection] using congrArg Prod.snd hp] at h
    exact h
  have hpxCoord : periodicCoordinate L hL p.1 = x.1 := by
    simpa [periodicProjection] using congrArg Prod.fst hp
  have hpyCoord : periodicCoordinate L hL p.2 = x.2 := by
    simpa [periodicProjection] using congrArg Prod.snd hp
  rcases hunit with (⟨heq, hstep | hstep⟩) | (⟨heq, hstep | hstep⟩)
  · have hq : p.2 - 1 ≡ (y.2.val : ℤ) [ZMOD L] := by
      have hpxy := hpy.trans hstep
      have h := hpxy.add_right (-1)
      simpa [sub_eq_add_neg] using h
    refine ⟨(p.1, p.2 - 1), ?_, ?_, ?_, ?_, ?_⟩
    · simp only [periodicProjection]
      apply Prod.ext
      · exact hpxCoord.trans heq
      · exact (periodicCoordinate_eq_of_modEq L hL _ _ hq).trans
          (periodicCoordinate_finVal L hL y.2)
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · have hq : p.2 + 1 ≡ (y.2.val : ℤ) [ZMOD L] := by
      have hxy := hstep.symm
      exact (hpy.add_right 1).trans (by simpa using hxy)
    refine ⟨(p.1, p.2 + 1), ?_, ?_, ?_, ?_, ?_⟩
    · simp only [periodicProjection]
      apply Prod.ext
      · exact hpxCoord.trans heq
      · exact (periodicCoordinate_eq_of_modEq L hL _ _ hq).trans
          (periodicCoordinate_finVal L hL y.2)
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · have hq : p.1 - 1 ≡ (y.1.val : ℤ) [ZMOD L] := by
      have hpxy := hpx.trans hstep
      have h := hpxy.add_right (-1)
      simpa [sub_eq_add_neg] using h
    refine ⟨(p.1 - 1, p.2), ?_, ?_, ?_, ?_, ?_⟩
    · simp only [periodicProjection]
      apply Prod.ext
      · exact (periodicCoordinate_eq_of_modEq L hL _ _ hq).trans
          (periodicCoordinate_finVal L hL y.1)
      · exact hpyCoord.trans heq
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · have hq : p.1 + 1 ≡ (y.1.val : ℤ) [ZMOD L] := by
      have hxy := hstep.symm
      exact (hpx.add_right 1).trans (by simpa using hxy)
    refine ⟨(p.1 + 1, p.2), ?_, ?_, ?_, ?_, ?_⟩
    · simp only [periodicProjection]
      apply Prod.ext
      · exact (periodicCoordinate_eq_of_modEq L hL _ _ hq).trans
          (periodicCoordinate_finVal L hL y.1)
      · exact hpyCoord.trans heq
    · norm_num
    · norm_num
    · norm_num
    · norm_num

/-- Any walk in the periodic graph lifts from a chosen initial representative.
Its endpoint displacement in each coordinate is bounded by the walk length. -/
theorem periodicWalk_exists_lift (L : ℕ) (hL : 0 < L)
    {x y : Fin L × Fin L}
    (w : (squarePeriodic L).toSimpleGraph.Walk x y) :
    ∀ p : LiftedPoint, periodicProjection L hL p = x →
      ∃ q : LiftedPoint, periodicProjection L hL q = y ∧
        -((w.length : ℕ) : ℤ) ≤ q.1 - p.1 ∧
        q.1 - p.1 ≤ (w.length : ℕ) ∧
        -((w.length : ℕ) : ℤ) ≤ q.2 - p.2 ∧
        q.2 - p.2 ≤ (w.length : ℕ) := by
  induction w with
  | nil =>
    intro p hp
    refine ⟨p, ?_, ?_, ?_, ?_, ?_⟩
    · simpa using hp
    · simp
    · simp
    · simp
    · simp
  | @cons a b c hadj tail ih =>
    intro p hp
    obtain ⟨q, hq, hx₁, hx₂, hy₁, hy₂⟩ :=
      periodicAdj_lift_step L hL a b hadj p hp
    obtain ⟨r, hr, hx₃, hx₄, hy₃, hy₄⟩ := ih q hq
    refine ⟨r, hr, ?_, ?_, ?_, ?_⟩ <;>
      simp only [SimpleGraph.Walk.length_cons, Nat.cast_add, Nat.cast_one] <;> omega

/-- For distinct-or-equal periodic vertices in the connected regime `L > 1`,
a graph-distance minimizer lifts with coordinate displacement bounded by the
periodic graph distance. -/
theorem periodicDistance_exists_lift (L R : ℕ) (hL : 1 < L)
    (x y : Fin L × Fin L) (p : LiftedPoint)
    (hp : periodicProjection L (by omega) p = x)
    (hR : latticeDistance .periodic L x y < R) :
    ∃ q : LiftedPoint, periodicProjection L (by omega) q = y ∧
      -((latticeDistance .periodic L x y : ℕ) : ℤ) ≤ q.1 - p.1 ∧
      q.1 - p.1 ≤ latticeDistance .periodic L x y ∧
      -((latticeDistance .periodic L x y : ℕ) : ℤ) ≤ q.2 - p.2 ∧
      q.2 - p.2 ≤ latticeDistance .periodic L x y ∧
      -(R : ℤ) < q.1 - p.1 ∧ q.1 - p.1 < R ∧
      -(R : ℤ) < q.2 - p.2 ∧ q.2 - p.2 < R := by
  let G := (squarePeriodic L).toSimpleGraph
  have hconn : G.Connected := squarePeriodic_connected L hL
  obtain ⟨w, hw⟩ := hconn x y |>.exists_walk_length_eq_dist
  obtain ⟨q, hq, hx₁, hx₂, hy₁, hy₂⟩ :=
    periodicWalk_exists_lift L (by omega) w p hp
  have hw' : w.length = latticeDistance .periodic L x y := by
    simpa [G, latticeDistance] using hw
  have hlen : (w.length : ℤ) = (latticeDistance .periodic L x y : ℤ) := by
    exact_mod_cast hw'
  have hRZ : (latticeDistance .periodic L x y : ℤ) < (R : ℤ) := by
    exact_mod_cast hR
  refine ⟨q, hq, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

/-- Projecting a lifted side-`2^k` integer square gives a subset of the
periodic quotient square with the projected lower statement, when that side is
strictly below the period. -/
theorem periodicProjection_mem_kpSquare_of_mem_liftedSquare
    (L k : ℕ) (hL : 0 < L) (hside : squareSide k < L)
    (a p : LiftedPoint) (hp : p ∈ liftedSquare (squareSide k) a) :
    periodicProjection L hL p ∈
      kpSquare .periodic L k (periodicProjection L hL a) := by
  change a.1 ≤ p.1 ∧ p.1 ≤ a.1 + (squareSide k : ℤ) - 1 ∧
      a.2 ≤ p.2 ∧ p.2 ≤ a.2 + (squareSide k : ℤ) - 1 at hp
  have hsidePos : 0 < squareSide k := Nat.pow_pos (by decide)
  let i := (p.1 - a.1).toNat
  let j := (p.2 - a.2).toNat
  have hi0 : 0 ≤ p.1 - a.1 := by omega
  have hj0 : 0 ≤ p.2 - a.2 := by omega
  have hiLtZ : p.1 - a.1 < (squareSide k : ℤ) := by omega
  have hjLtZ : p.2 - a.2 < (squareSide k : ℤ) := by omega
  have hiLt : i < squareSide k := by
    dsimp [i]
    exact (Int.toNat_lt_of_ne_zero (Nat.ne_of_gt hsidePos)).2 hiLtZ
  have hjLt : j < squareSide k := by
    dsimp [j]
    exact (Int.toNat_lt_of_ne_zero (Nat.ne_of_gt hsidePos)).2 hjLtZ
  have hiCast : (i : ℤ) = p.1 - a.1 := by
    dsimp [i]
    exact Int.natCast_toNat_eq_self.mpr hi0
  have hjCast : (j : ℤ) = p.2 - a.2 := by
    dsimp [j]
    exact Int.natCast_toNat_eq_self.mpr hj0
  have hpx : p.1 = a.1 + (i : ℤ) := by omega
  have hpy : p.2 = a.2 + (j : ℤ) := by omega
  apply (mem_kpSquare_periodic_iff L k hside
    (periodicProjection L hL a) (periodicProjection L hL p)).2
  refine ⟨i, Finset.mem_range.mpr hiLt, j, Finset.mem_range.mpr hjLt, ?_⟩
  constructor
  · change (periodicCoordinate L hL p.1).val =
      ((periodicCoordinate L hL a.1).val + i) % L
    rw [hpx]
    exact periodicCoordinate_add_nat L hL a.1 i
  · change (periodicCoordinate L hL p.2).val =
      ((periodicCoordinate L hL a.2).val + j) % L
    rw [hpy]
    exact periodicCoordinate_add_nat L hL a.2 j

/-- Two periodic side-`2^k` squares whose chosen witnesses are at graph
distance `d` fit inside one periodic side-`2^K` square whenever the pair span
budget is below the target side. The proof lifts a distance-realizing walk,
aligns both square representatives by period translations, encloses the
integer boxes, then projects the enclosing box. -/
theorem periodicPairSquares_fit (L k K : ℕ) (hL : 1 < L)
    (hsourceSide : squareSide k < L) (htargetSide : squareSide K < L)
    (a b : Fin L × Fin L) (x y : Fin L × Fin L)
    (hx : x ∈ kpSquare .periodic L k a)
    (hy : y ∈ kpSquare .periodic L k b)
    (hbudget : (latticeDistance .periodic L x y : ℤ) +
        2 * ((squareSide k : ℤ) - 1) < (squareSide K : ℤ)) :
    ∃ c : LiftedPoint,
      kpSquare .periodic L k a ∪ kpSquare .periodic L k b ⊆
        kpSquare .periodic L K (periodicProjection L (by omega) c) := by
  let hLpos : 0 < L := by omega
  let aLift : LiftedPoint := (a.1.val, a.2.val)
  let bLift : LiftedPoint := (b.1.val, b.2.val)
  have haProj : periodicProjection L hLpos aLift = a := by
    apply Prod.ext
    · exact periodicCoordinate_finVal L hLpos a.1
    · exact periodicCoordinate_finVal L hLpos a.2
  have hbProj : periodicProjection L hLpos bLift = b := by
    apply Prod.ext
    · exact periodicCoordinate_finVal L hLpos b.1
    · exact periodicCoordinate_finVal L hLpos b.2
  have hx' : x ∈ kpSquare .periodic L k (periodicProjection L hLpos aLift) := by
    rw [haProj]
    exact hx
  have hy' : y ∈ kpSquare .periodic L k (periodicProjection L hLpos bLift) := by
    rw [hbProj]
    exact hy
  obtain ⟨p, hpBox, hpProj⟩ := periodicSquare_exists_lifted_witness
    L k hLpos hsourceSide aLift x hx'
  obtain ⟨q, hqProj, hdx₁, hdx₂, hdy₁, hdy₂, _, _, _, _⟩ :=
    periodicDistance_exists_lift L (latticeDistance .periodic L x y + 1)
      hL x y p hpProj (by omega)
  have hyq : periodicProjection L hLpos q ∈
      kpSquare .periodic L k (periodicProjection L hLpos bLift) := by
    rw [hqProj, hbProj]
    exact hy
  let a' : LiftedPoint := aLift
  have ha' : periodicProjection L hLpos a' = a := by
    exact haProj
  have hpa : p ∈ liftedSquare (squareSide k) a' := by
    simpa [a'] using hpBox
  obtain ⟨b', hb', hqb⟩ := periodicSquare_align_lifted_witness
    L k hLpos hsourceSide bLift q hyq
  have hbDomain : periodicProjection L hLpos b' = b := hb'.trans hbProj
  obtain ⟨c, hcontain⟩ := pair_liftedSquares_fit
    (squareSide k) (squareSide K) (latticeDistance .periodic L x y)
    a' b' p q hpa hqb (by omega) (by omega) (by omega) (by omega) hbudget
  refine ⟨c, ?_⟩
  intro z hz
  rcases Finset.mem_union.mp hz with hz | hz
  · have hz' : z ∈ kpSquare .periodic L k (periodicProjection L hLpos a') := by
      rw [ha']
      exact hz
    obtain ⟨zLift, hzLift, hzProj⟩ := periodicSquare_exists_lifted_witness
      L k hLpos hsourceSide a' z hz'
    have hbig : zLift ∈ liftedSquare (squareSide K) c := hcontain (Or.inl hzLift)
    have hzTarget := periodicProjection_mem_kpSquare_of_mem_liftedSquare
      L K hLpos htargetSide c zLift hbig
    simpa [hzProj] using hzTarget
  · have hz' : z ∈ kpSquare .periodic L k (periodicProjection L hLpos b') := by
      rw [hbDomain]
      exact hz
    obtain ⟨zLift, hzLift, hzProj⟩ := periodicSquare_exists_lifted_witness
      L k hLpos hsourceSide b' z hz'
    have hbig : zLift ∈ liftedSquare (squareSide K) c := hcontain (Or.inr hzLift)
    have hzTarget := periodicProjection_mem_kpSquare_of_mem_liftedSquare
      L K hLpos htargetSide c zLift hbig
    simpa [hzProj] using hzTarget

/-- A connected three-square chain on the torus fits in one periodic target
square under the three-box span budget. Each successive graph-distance path
is lifted, and the second and third square representatives are translated by
periods to match the lifted path endpoints. -/
theorem periodicTripleSquares_fit (L k K : ℕ) (hL : 1 < L)
    (hsourceSide : squareSide k < L) (htargetSide : squareSide K < L)
    (a b c : Fin L × Fin L) (x y z : Fin L × Fin L)
    (hx : x ∈ kpSquare .periodic L k a)
    (hy : y ∈ kpSquare .periodic L k b)
    (hz : z ∈ kpSquare .periodic L k c)
    (hbudget : (latticeDistance .periodic L x y : ℤ) +
        (latticeDistance .periodic L y z : ℤ) +
        3 * ((squareSide k : ℤ) - 1) < (squareSide K : ℤ)) :
    ∃ d : LiftedPoint,
      kpSquare .periodic L k a ∪ kpSquare .periodic L k b ∪
        kpSquare .periodic L k c ⊆
        kpSquare .periodic L K (periodicProjection L (by omega) d) := by
  let hLpos : 0 < L := by omega
  let aLift : LiftedPoint := (a.1.val, a.2.val)
  let bLift : LiftedPoint := (b.1.val, b.2.val)
  let cLift : LiftedPoint := (c.1.val, c.2.val)
  have haProj : periodicProjection L hLpos aLift = a := by
    apply Prod.ext
    · exact periodicCoordinate_finVal L hLpos a.1
    · exact periodicCoordinate_finVal L hLpos a.2
  have hbProj : periodicProjection L hLpos bLift = b := by
    apply Prod.ext
    · exact periodicCoordinate_finVal L hLpos b.1
    · exact periodicCoordinate_finVal L hLpos b.2
  have hcProj : periodicProjection L hLpos cLift = c := by
    apply Prod.ext
    · exact periodicCoordinate_finVal L hLpos c.1
    · exact periodicCoordinate_finVal L hLpos c.2
  have hx' : x ∈ kpSquare .periodic L k (periodicProjection L hLpos aLift) := by
    rw [haProj]
    exact hx
  have hy' : y ∈ kpSquare .periodic L k (periodicProjection L hLpos bLift) := by
    rw [hbProj]
    exact hy
  have hz' : z ∈ kpSquare .periodic L k (periodicProjection L hLpos cLift) := by
    rw [hcProj]
    exact hz
  obtain ⟨p, hpBox, hpProj⟩ := periodicSquare_exists_lifted_witness
    L k hLpos hsourceSide aLift x hx'
  obtain ⟨q, hqProj, hdx₁, hdx₂, hdy₁, hdy₂, _, _, _, _⟩ :=
    periodicDistance_exists_lift L (latticeDistance .periodic L x y + 1)
      hL x y p hpProj (by omega)
  obtain ⟨r, hrProj, hdx₃, hdx₄, hdy₃, hdy₄, _, _, _, _⟩ :=
    periodicDistance_exists_lift L (latticeDistance .periodic L y z + 1)
      hL y z q hqProj (by omega)
  have hyq : periodicProjection L hLpos q ∈
      kpSquare .periodic L k (periodicProjection L hLpos bLift) := by
    rw [hqProj, hbProj]
    exact hy
  have hzr : periodicProjection L hLpos r ∈
      kpSquare .periodic L k (periodicProjection L hLpos cLift) := by
    rw [hrProj, hcProj]
    exact hz
  let a' : LiftedPoint := aLift
  let ha' : periodicProjection L hLpos a' = a := haProj
  have hpa : p ∈ liftedSquare (squareSide k) a' := by
    simpa [a'] using hpBox
  obtain ⟨b', hb', hqb⟩ := periodicSquare_align_lifted_witness
    L k hLpos hsourceSide bLift q hyq
  obtain ⟨c', hc', hrc⟩ := periodicSquare_align_lifted_witness
    L k hLpos hsourceSide cLift r hzr
  obtain ⟨d, hcontain⟩ := triple_liftedSquares_fit
    (squareSide k) (squareSide K)
    (latticeDistance .periodic L x y) (latticeDistance .periodic L y z)
    a' b' c' p q r hpa hqb hrc
    (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) hbudget
  have hbDomain : periodicProjection L hLpos b' = b := hb'.trans hbProj
  have hcDomain : periodicProjection L hLpos c' = c := hc'.trans hcProj
  refine ⟨d, ?_⟩
  intro u hu
  rcases Finset.mem_union.mp hu with hu | hu
  · rcases Finset.mem_union.mp hu with hu | hu
    · have hu' : u ∈ kpSquare .periodic L k (periodicProjection L hLpos a') := by
        rw [ha']
        exact hu
      obtain ⟨uLift, huLift, huProj⟩ := periodicSquare_exists_lifted_witness
        L k hLpos hsourceSide a' u hu'
      have hbig : uLift ∈ liftedSquare (squareSide K) d :=
        hcontain (Or.inl (Or.inl huLift))
      have huTarget := periodicProjection_mem_kpSquare_of_mem_liftedSquare
        L K hLpos htargetSide d uLift hbig
      simpa [huProj] using huTarget
    · have hu' : u ∈ kpSquare .periodic L k (periodicProjection L hLpos b') := by
        rw [hbDomain]
        exact hu
      obtain ⟨uLift, huLift, huProj⟩ := periodicSquare_exists_lifted_witness
        L k hLpos hsourceSide b' u hu'
      have hbig : uLift ∈ liftedSquare (squareSide K) d :=
        hcontain (Or.inl (Or.inr huLift))
      have huTarget := periodicProjection_mem_kpSquare_of_mem_liftedSquare
        L K hLpos htargetSide d uLift hbig
      simpa [huProj] using huTarget
  · have hu' : u ∈ kpSquare .periodic L k (periodicProjection L hLpos c') := by
      rw [hcDomain]
      exact hu
    obtain ⟨uLift, huLift, huProj⟩ := periodicSquare_exists_lifted_witness
      L k hLpos hsourceSide c' u hu'
    have hbig : uLift ∈ liftedSquare (squareSide K) d :=
      hcontain (Or.inr huLift)
    have huTarget := periodicProjection_mem_kpSquare_of_mem_liftedSquare
      L K hLpos htargetSide d uLift hbig
    simpa [huProj] using huTarget

end FroehlichSpencer.BKT

end
