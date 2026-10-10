/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.FiniteGraph.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Integer currents for the finite Villain model

Currents are integer-valued functions on the oriented edge type. The orientation is only a sign
convention; parallel edges remain distinct, as in KP §1.4 and §6.1, pp. 4, 33–34.
-/

@[expose] public section

namespace FroehlichSpencer.BKT

namespace Villain

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]

/-- The divergence of an integer edge current, with outgoing edges counted positively and incoming
edges negatively. This is the oriented-edge convention used in the Fourier expansion of KP §6.1,
p. 33. -/
def currentDivergence (G : Multigraph V E) (q : E → ℤ) (j : V) : ℤ :=
  (∑ e, if G.src e = j then q e else 0) - (∑ e, if G.tgt e = j then q e else 0)

/-- A current is neutral away from the pinned vertex. -/
def neutralAwayFrom (G : Multigraph V E) (z : V) (q : E → ℤ) : Prop :=
  ∀ j, j ≠ z → currentDivergence G q j = 0

/-- The off-root current constraint obtained by inserting `exp (I * θ j)` and using the
reindexed `exp (-I * q * x)` Fourier series in the root-pinned Villain integral. With positive
divergence counted as outgoing, this imposes divergence `+1` at `j` and zero at every other
non-root vertex. Conservation gives divergence `-1` at the root when `j ≠ z`, so this character
is a source at `j` and a sink at the root. KP §6.1, p. 33. -/
def characterCurrent (G : Multigraph V E) (z j : V) (q : E → ℤ) : Prop :=
  ∀ k, k ≠ z → currentDivergence G q k = if k = j then 1 else 0

/-- The Gaussian weight of a current at inverse temperature `β`. -/
noncomputable def currentGaussianWeight (β : ℝ) (q : E → ℤ) : ℝ :=
  ∏ e, Real.exp (-((q e : ℝ) ^ 2) / (2 * β))

theorem sum_currentDivergence_eq_zero (G : Multigraph V E) (q : E → ℤ) :
    ∑ j, currentDivergence G q j = 0 := by
  classical
  simp [currentDivergence, Finset.sum_sub_distrib, Finset.sum_comm]

/-- For a non-root observable, the Fourier constraint fixes the compensating root charge to `-1`.
-/
theorem characterCurrent_root_divergence (G : Multigraph V E) (z j : V) (q : E → ℤ)
    (hcurrent : characterCurrent G z j q) (hj : j ≠ z) :
    currentDivergence G q z = -1 := by
  classical
  have hsum := sum_currentDivergence_eq_zero G q
  rw [← Finset.add_sum_erase (s := Finset.univ) (f := currentDivergence G q)
    (Finset.mem_univ z)] at hsum
  have hrest :
      ∑ k ∈ Finset.univ.erase z, currentDivergence G q k = 1 := by
    calc
      ∑ k ∈ Finset.univ.erase z, currentDivergence G q k =
          ∑ k ∈ Finset.univ.erase z, if k = j then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro k hk
        exact hcurrent k (Finset.ne_of_mem_erase hk)
      _ = 1 := by simp [hj]
  omega

end Villain

end FroehlichSpencer.BKT

end
