/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Analysis.Matrix.Spectrum
public import FroehlichSpencer.Surface.HamiltonianHermitian

/-! # Finite-volume eigenvalue counting function -/

public section

namespace FroehlichSpencer

/-- The number, counted with multiplicity, of eigenvalues of `H_Λ(v)` at most `E`. -/
@[expose] noncomputable def finiteEigenvalueCount (ν : ℕ) (Λ : Finset (Site ν))
    (E : ℝ) (v : Site ν → ℝ) : ℕ := by
  classical
  exact Finset.card (Finset.univ.filter fun x : {x : Site ν // x ∈ Λ} =>
    (hamiltonian_isHermitian ν Λ v).eigenvalues x ≤ E)

end FroehlichSpencer


end
