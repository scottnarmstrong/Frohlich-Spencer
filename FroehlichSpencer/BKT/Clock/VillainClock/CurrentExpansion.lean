/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Clock.VillainClock.EdgeFourier
import Mathlib.Tactic

/-!
# Finite residue-current expansion for the Villain clock

The finite-volume Villain-clock configuration weight expands exactly as a sum over one residue
current on each edge.

The edge activity is the sampled Gaussian alias coefficient, and the phase
is the usual divergence pairing with the clock field.

The current representation keeps all alias
classes and does not replace their sum by a principal-frequency term.
-/

@[expose] public section

open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Ginibre

noncomputable section

namespace FroehlichSpencer.BKT.Clock.VillainClock

/-- The integer divergence of a residue current on an oriented finite multigraph. -/
def residueCurrentDivergence {V E : Type*} [Fintype E] [DecidableEq V]
    (G : Multigraph V E) {N : ℕ} (j : E → Fin N) (v : V) : ℤ :=
  (∑ e : E, if G.src e = v then (j e : ℤ) else 0) -
    ∑ e : E, if G.tgt e = v then (j e : ℤ) else 0

/-- The edge phase of a residue current in a clock-spin configuration. -/
def residueCurrentEdgePhase {V E : Type*} [Fintype E]
    (G : Multigraph V E) (N : ℕ) (j : E → Fin N) (s : V → Fin N) : ℂ :=
  ∏ e : E, Complex.exp (Complex.I * (j e : ℂ) *
    ((angleField N s (G.src e) - angleField N s (G.tgt e) : ℝ) : ℂ))

/-- Exact Fourier expansion of a finite Villain-clock configuration weight into edge residues. -/
theorem configurationWeight_eq_residueCurrentSum {V E : Type*} [Fintype E] [DecidableEq E]
    (G : Multigraph V E) (β : ℝ) {N : ℕ} (hN : 0 < N) (hβ : 0 < β)
    (s : V → Fin N) :
    (configurationWeight G β N s : ℂ) =
      ∑ j : E → Fin N, ∏ e : E,
        gaussianAliasCoefficient β N (j e) *
          Complex.exp (Complex.I * (j e : ℂ) *
            ((angleField N s (G.src e) - angleField N s (G.tgt e) : ℝ) : ℂ)) := by
  classical
  unfold configurationWeight
  have hcast : ((∏ e : E, villainWeight β
      (angleField N s (G.src e) - angleField N s (G.tgt e)) : ℝ) : ℂ) =
      ∏ e : E, (villainWeight β
        (angleField N s (G.src e) - angleField N s (G.tgt e)) : ℂ) := by norm_cast
  rw [hcast]
  calc
    ∏ e : E, (villainWeight β
        (angleField N s (G.src e) - angleField N s (G.tgt e)) : ℂ) =
      ∏ e : E, ∑ q : Fin N, gaussianAliasCoefficient β N q *
        Complex.exp (Complex.I * (q : ℂ) *
          ((angleField N s (G.src e) - angleField N s (G.tgt e) : ℝ) : ℂ)) := by
            apply Finset.prod_congr rfl
            intro e _
            exact villainClock_edge_eq_residueFourier β hN hβ (s (G.src e)) (s (G.tgt e))
    _ = ∑ j : E → Fin N, ∏ e : E,
          gaussianAliasCoefficient β N (j e) * Complex.exp (Complex.I * (j e : ℂ) *
            ((angleField N s (G.src e) - angleField N s (G.tgt e) : ℝ) : ℂ)) := by
      rw [Finset.prod_univ_sum]
      simp

end FroehlichSpencer.BKT.Clock.VillainClock

end
