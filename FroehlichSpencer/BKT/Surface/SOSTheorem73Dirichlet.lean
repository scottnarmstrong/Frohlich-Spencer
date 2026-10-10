/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.Instances.Real.Lemmas
public import FroehlichSpencer.BKT.Surface.SOSDirichletLaw
import FroehlichSpencer.BKT.Provider.SOSTheorem73Dirichlet

/-! # FS81 Theorem 7.3 for the solid-on-solid model in a box with Dirichlet boundary conditions -/

open MeasureTheory Filter Topology

-- FROZEN_ANCHOR_PREFIX_BEGIN
public section

namespace FroehlichSpencer.BKT

/--
FS81 Theorem 7.3 (J p. 590, (7.17)) and (7.18) (J p. 590, Remark 1) for the
solid-on-solid model in the box `{0, …, L - 1}²` with Dirichlet boundary conditions (FS81: "The
results and proofs which follow could be extended to Dirichlet … b.c.").

For `β` sufficiently small
there is `β' = β'(β) > 0`, tending to `0` as `β → 0`, such that in every box from a fixed size on,
for all sites `u, v` and every real `ε`,
`⟨e^{ε[φ(u) - φ(v)]}⟩ ≥ e^{(ε²/β') ln (1 + r)}` and `⟨[φ(u) - φ(v)]²⟩ ≥ (1/β') ln (1 + r)`, the
latter finite.

Here `r` is the Euclidean distance `|u - v|`, capped by the distance from `u` to
the complement of the box (the Dirichlet boundary pins the heights); the expectations are in
`[0, ∞]`.
-/
theorem sos_theorem73_dirichlet :
    ∃ β₀ : ℝ, 0 < β₀ ∧ ∃ β' : ℝ → ℝ, Tendsto β' (𝓝[>] 0) (𝓝 0) ∧ ∃ L₀ : ℕ,
      ∀ (β : ℝ) (hβ : 0 < β), β ≤ β₀ → 0 < β' β ∧
        ∀ L : ℕ, L₀ ≤ L → ∀ u v : Fin L × Fin L,
          let r : ℝ := min
            (Real.sqrt ((((u.1 : ℕ) : ℝ) - v.1) ^ 2 + (((u.2 : ℕ) : ℝ) - v.2) ^ 2))
            ((min (min ((u.1 : ℕ) + 1) (L - u.1)) (min ((u.2 : ℕ) + 1) (L - u.2)) : ℕ) : ℝ)
          (∀ ε : ℝ, ENNReal.ofReal (Real.exp (ε ^ 2 / β' β * Real.log (1 + r))) ≤
            ∫⁻ n, ENNReal.ofReal (Real.exp (ε * ((n u : ℝ) - n v))) ∂sosDirichletLaw L β hβ) ∧
          ENNReal.ofReal (Real.log (1 + r) / β' β) ≤
            ∫⁻ n, ENNReal.ofReal (((n u : ℝ) - n v) ^ 2) ∂sosDirichletLaw L β hβ ∧
          ∫⁻ n, ENNReal.ofReal (((n u : ℝ) - n v) ^ 2) ∂sosDirichletLaw L β hβ < ⊤ :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact FroehlichSpencer.BKT.Provider.sos_theorem73_dirichlet
  -- FROZEN_ANCHOR_PROOF_END


-- FROZEN_ANCHOR_SUFFIX_BEGIN
end FroehlichSpencer.BKT

end
-- FROZEN_ANCHOR_SUFFIX_END
