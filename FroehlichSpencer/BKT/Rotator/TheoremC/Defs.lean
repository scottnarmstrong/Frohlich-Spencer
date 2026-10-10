/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Rotator.FiniteComb
public import FroehlichSpencer.BKT.Rotator.Contour.Factor

/-!
# Definitions shared by the FS81 Theorem C assembly
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Rotator.TheoremC

open FroehlichSpencer.BKT.Rotator.BesselInterp
open FroehlichSpencer.BKT.Lattice2D

/-- The one-site Dirichlet comb `D_N(ψ) = 1 + 2 ∑_{q=1}^N cos(qψ) = ∑_{|q| ≤ N} e^{iqψ}`. -/
def dirichletComb (N : ℕ) (ψ : ℝ) : ℝ :=
  1 + 2 * ∑ q ∈ Finset.Icc 1 N, Real.cos (q * ψ)

/-- The site observables on the wired face carrier: the comb at the bounded faces, `1` at the
wired root `none`. -/
def pinnedCombLam (L N : ℕ) : RotatorDualFace L → ℝ → ℝ :=
  fun k => k.elim (fun _ => 1) (fun _ => dirichletComb N)

/-- The plane-rotator dual weight in the angle variable: `w_β(z) = I_β(z / 2π)`. -/
def besselWeightψ (β : ℝ) (z : ℂ) : ℂ :=
  besselInterp β (z / (2 * Real.pi))

/-- Its cost envelope in the angle variable: `c(u) = g_C(u / 2π) / β`. -/
def besselCostψ (C β u : ℝ) : ℝ :=
  Contour.cEnvelope C (u / (2 * Real.pi)) / β

/-- The pinned interpolated density with the integer source current `j` inserted (FS81 (1.36)). -/
def rotatorPinnedMarkedDensityCoords (L : ℕ) (β : ℝ) (j : RotatorInternalBond L → ℤ)
    (x : SquareFreeVertex L → ℝ) : ℂ :=
  ∏ e : RotatorInternalBond L,
    besselInterp β
      ((((rotatorPinnedRealFieldOfCoords x).1 ((rotatorDualGraph L).src e) -
        (rotatorPinnedRealFieldOfCoords x).1 ((rotatorDualGraph L).tgt e) + (j e : ℝ) : ℝ)) : ℂ)

/-- Its pairing with the box comb of cutoff `N`. -/
def rotatorPinnedMarkedCombCutoffPairing (L : ℕ) (β : ℝ) (j : RotatorInternalBond L → ℤ)
    (N : ℕ) : ℂ :=
  ∫ x : SquareFreeVertex L → ℝ,
    faceCombCutoff (ι := SquareFreeVertex L) N x * rotatorPinnedMarkedDensityCoords L β j x

end FroehlichSpencer.BKT.Rotator.TheoremC

end
