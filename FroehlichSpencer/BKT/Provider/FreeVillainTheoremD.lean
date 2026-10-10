/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Bridge.FreeVillainDisorderGauge
public import FroehlichSpencer.BKT.VillainDisorder.Dirichlet.MarkedGeometryAssembly
public import FroehlichSpencer.BKT.Surface.FreeVillainDisorderLimit

/-!
# Provider for `FroehlichSpencer.BKT.freeVillain_disorderLimit_upper_bound`

The route
consumes the gate statement `isProbabilityMeasure_freeVillainLaw`
(`Bridge/FreeVillainDisorder`).
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Provider

open Filter
open FroehlichSpencer.BKT.Bridge.FreeVillainDisorderGauge
  (freeVillain_disorderLimit_upper_bound_of_marked)

/-- **FS81 Theorem D (1.35)**, root R-VIL-D: the marked-extension route applied to the proved
clause. -/
theorem freeVillain_disorderLimit_upper_bound :
    ∀ ξ : ℝ, 0 < ξ → ξ < 1 → ∃ β₀ : ℝ, ∀ (β : ℝ) (hβ : 0 < β), β₀ < β →
      (∃ D : ℕ → ℝ, IsFreeVillainDisorderLimit β hβ ξ D) ∧
      ∃ β'' : ℝ, 0 < β'' ∧ ∃ A : ℝ, ∀ D : ℕ → ℝ, IsFreeVillainDisorderLimit β hβ ξ D →
        ∀ n : ℕ, D n ≤ A * (1 + (n : ℝ)) ^ (-(ξ ^ 2 * β'')) :=
  freeVillain_disorderLimit_upper_bound_of_marked
    VillainDisorder.Dirichlet.rootedFejerMarkedExtension_holds

end FroehlichSpencer.BKT.Provider

end
