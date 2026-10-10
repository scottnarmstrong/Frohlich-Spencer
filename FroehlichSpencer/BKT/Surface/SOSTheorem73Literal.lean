/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Probability.Notation
public import FroehlichSpencer.BKT.Surface.SOSLiteralLimit
import FroehlichSpencer.BKT.Provider.SOSTheorem73Literal

/-! # FS81 Theorem 7.3 in FS81's state (7.16), at every limit point as `Ω ↗ ℤ²` -/

open MeasureTheory Filter Topology

-- FROZEN_ANCHOR_PREFIX_BEGIN
public section

namespace FroehlichSpencer.BKT

/-- FS81 Theorem 7.3 (J p. 590, (7.17)) and (7.18) (Remark 1) in FS81's own state
(7.16), with the interpolation (C.1). For `β` sufficiently small there is
`β' = β'(β) > 0`, tending to `0` as `β → 0`, such that for every finite region `A ⊂ ℤ²` and base
point `w ∈ A`: a limit point of the laws of the height differences as `Ω ↗ ℤ²` exists, and every
limit point `ν` is a probability measure satisfying, for all `v, v' ∈ A` and every real `ε`,
`⟨e^{ε[φ(v) - φ(v')]}⟩ ≥ e^{(ε²/β') ln (1 + |v - v'|)}` (in `[0, ∞]`) and
`⟨[φ(v) - φ(v')]²⟩ ≥ (1/β') ln (1 + |v - v'|)`, the latter finite; `|·|` is the Euclidean norm.
FS81's `0, x` are `v, v'`. -/
theorem sos_theorem73_literal :
    ∃ β₀ : ℝ, 0 < β₀ ∧ ∃ β' : ℝ → ℝ, Tendsto β' (𝓝[>] 0) (𝓝 0) ∧
      ∀ (β : ℝ) (hβ : 0 < β) (hβ1 : β ≤ 1), β ≤ β₀ → 0 < β' β ∧
        ∀ (A : Finset (ℤ × ℤ)) (w : ℤ × ℤ) (hw : w ∈ A),
          (∃ ν : Measure (A → ℤ), IsSOSLiteralLimit β hβ hβ1 A w hw ν) ∧
          ∀ ν : Measure (A → ℤ), IsSOSLiteralLimit β hβ hβ1 A w hw ν →
            IsProbabilityMeasure ν ∧ ∀ (v v' : ℤ × ℤ) (hv : v ∈ A) (hv' : v' ∈ A),
              let r : ℝ := Real.sqrt (((v.1 - v'.1 : ℤ) : ℝ) ^ 2 + ((v.2 - v'.2 : ℤ) : ℝ) ^ 2)
              (∀ ε : ℝ, ENNReal.ofReal (Real.exp (ε ^ 2 / β' β * Real.log (1 + r))) ≤
                ∫⁻ d, ENNReal.ofReal (Real.exp (ε * ((d ⟨v, hv⟩ - d ⟨v', hv'⟩ : ℤ) : ℝ))) ∂ν) ∧
              ENNReal.ofReal (Real.log (1 + r) / β' β) ≤
                ∫⁻ d, ENNReal.ofReal (((d ⟨v, hv⟩ - d ⟨v', hv'⟩ : ℤ) : ℝ) ^ 2) ∂ν ∧
              ∫⁻ d, ENNReal.ofReal (((d ⟨v, hv⟩ - d ⟨v', hv'⟩ : ℤ) : ℝ) ^ 2) ∂ν < ⊤ :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by exact FroehlichSpencer.BKT.Provider.sos_theorem73_literal
  -- FROZEN_ANCHOR_PROOF_END


-- FROZEN_ANCHOR_SUFFIX_BEGIN
end FroehlichSpencer.BKT

end
-- FROZEN_ANCHOR_SUFFIX_END
