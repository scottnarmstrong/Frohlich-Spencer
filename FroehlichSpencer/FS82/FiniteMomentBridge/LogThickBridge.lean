/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Surface.RectBox4
public import FroehlichSpencer.FS82.Surface.RectBox4ShortestSide
public import FroehlichSpencer.FS82.Surface.RectBox4LongestSide
public import FroehlichSpencer.FS82.Surface.IsLogThickRectBox4
public import FroehlichSpencer.FS82.Root.FiniteMomentComparison

/-!
# The literal log-thick class is the internal log-thick class

The internal box of a literal rectangle `R : RectBox4` is its side function `R.side`; the origin
does not enter the internal complex. `IsLogThickRectBox4 R` says `log(N(R) + 1) ≤ m(R)` for the
longest and shortest sides, and the internal `Root.IsLogThickBox` asks for some `N ≥ 1` and `m`
with `log(N + 1) ≤ m ≤ side i ≤ N`.
-/

@[expose] public section

open FroehlichSpencer.FS82.Surface

namespace FroehlichSpencer.FS82.FiniteMomentBridge

theorem shortestSide_le (R : RectBox4) (i : Fin 4) : R.shortestSide ≤ R.side i :=
  Finset.inf'_le _ (Finset.mem_univ i)

theorem le_longestSide (R : RectBox4) (i : Fin 4) : R.side i ≤ R.longestSide :=
  Finset.le_sup' _ (Finset.mem_univ i)

theorem one_le_longestSide (R : RectBox4) : 1 ≤ R.longestSide :=
  le_trans (R.side_pos 0) (le_longestSide R 0)

/-- **The log-thick bridge.** A literal rectangle is log-thick exactly when its internal box
`R.side` is. -/
theorem isLogThickRectBox4_iff (R : RectBox4) :
    IsLogThickRectBox4 R ↔ FroehlichSpencer.FS82.Root.IsLogThickBox R.side := by
  constructor
  · intro h
    refine ⟨R.longestSide, R.shortestSide, one_le_longestSide R, ?_,
      shortestSide_le R, le_longestSide R⟩
    have h' : Real.log ((R.longestSide + 1 : ℕ) : ℝ) ≤ (R.shortestSide : ℝ) := h
    push_cast at h'
    exact h'
  · rintro ⟨N, m, hN, hm, hmin, hBmax⟩
    have hlong : R.longestSide ≤ N := Finset.sup'_le _ _ fun i _ => hBmax i
    have hshort : m ≤ R.shortestSide := Finset.le_inf' _ _ fun i _ => hmin i
    change Real.log ((R.longestSide + 1 : ℕ) : ℝ) ≤ (R.shortestSide : ℝ)
    have hpos : (0 : ℝ) < ((R.longestSide + 1 : ℕ) : ℝ) := by positivity
    have hmono : Real.log ((R.longestSide + 1 : ℕ) : ℝ) ≤ Real.log (N + 1 : ℝ) := by
      apply Real.log_le_log hpos
      have : (R.longestSide : ℝ) ≤ (N : ℝ) := by exact_mod_cast hlong
      push_cast
      linarith
    have hmR : (m : ℝ) ≤ (R.shortestSide : ℝ) := by exact_mod_cast hshort
    linarith

end FroehlichSpencer.FS82.FiniteMomentBridge

end
