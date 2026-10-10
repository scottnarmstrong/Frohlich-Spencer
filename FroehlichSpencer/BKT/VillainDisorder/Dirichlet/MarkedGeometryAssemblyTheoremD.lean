/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.VillainDisorder.Dirichlet.MarkedGeometryAssembly
public import FroehlichSpencer.BKT.VillainDisorder.Dirichlet.MarkedEstimate
public import FroehlichSpencer.BKT.VillainDisorder.Dirichlet.TheoremD

/-!
On the centered free primal boxes, the disorder expectations satisfy FS81's power bound on every
sufficiently large box, and at every cluster point of the exhaustion.
-/

@[expose] public section

open Filter Topology

noncomputable section

namespace FroehlichSpencer.BKT.VillainDisorder.Dirichlet

/-- **D3's Fejér input holds.** -/
theorem rootedDirichletFejerGlobalInput_holds : RootedDirichletFejerGlobalInput :=
  rootedDirichletFejerEstimate_of_markedExtension rootedFejerMarkedExtension_holds

/-- **FS81 Theorem D for the centered Dirichlet free-box exhaustion.** -/
theorem rootedDirichletTheoremD :
    ∃ c : ℝ, 0 < c ∧
      ∀ η : ℝ, 0 < η → η ≤ 1 / 2 →
        ∃ β₀ : ℝ, ∃ _hβ₀ : 0 < β₀,
          ∀ β : ℝ, ∀ hβ : 0 < β, ∀ _hβlarge : β₀ < β,
            ∀ ξ : ℝ, 0 < ξ → ξ < 1 → η ≤ ξ → η ≤ 1 - ξ →
              ∀ n : ℕ, ∀ _hnpos : 1 ≤ n,
                (∀ᶠ R in atTop, n ≤ R) ∧
                (∀ R : ℕ, dirichletCenteredDisorder R n β ξ hβ ∈ Set.Icc (-1) 1) ∧
                (∀ᶠ R in atTop,
                  dirichletCenteredDisorder R n β ξ hβ ∈ Set.Icc 0
                    (2 * Real.rpow ((n + 1 : ℕ) : ℝ) (-(c * η ^ 2 * β)))) ∧
                (∃ ℓ : ℝ, ∃ φ : ℕ → ℕ, StrictMono φ ∧
                  Tendsto (fun k => dirichletCenteredDisorder (φ k) n β ξ hβ)
                    atTop (𝓝 ℓ)) ∧
                ∀ ℓ : ℝ,
                  MapClusterPt ℓ atTop (fun R => dirichletCenteredDisorder R n β ξ hβ) →
                    ℓ ∈ Set.Icc 0
                      (2 * Real.rpow ((n + 1 : ℕ) : ℝ) (-(c * η ^ 2 * β))) :=
  rootedDirichletTheoremD_thermodynamicLimit rootedDirichletFejerGlobalInput_holds

end FroehlichSpencer.BKT.VillainDisorder.Dirichlet

end
