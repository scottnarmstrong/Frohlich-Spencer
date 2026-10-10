/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module
public import Mathlib
public import FroehlichSpencer.BKT.Surface.PlaneRotatorPowerLaw
public import FroehlichSpencer.BKT.Surface.PlaneRotatorTransition
public import FroehlichSpencer.BKT.Surface.ConditionLambdaGasTheoremA
public import FroehlichSpencer.BKT.Surface.ConditionLambdaGasTheoremB
public import FroehlichSpencer.BKT.Surface.ClockPhaseDiagram
public import FroehlichSpencer.BKT.Surface.ClockDisorderLowerBound
public import FroehlichSpencer.BKT.Surface.FreeVillainTheoremD
public import FroehlichSpencer.BKT.Surface.SOSTheorem73Dirichlet
public import FroehlichSpencer.BKT.Surface.SOSRoughening
public import FroehlichSpencer.BKT.Surface.VillainClock.VillainClockTheorem71One
public import FroehlichSpencer.BKT.Surface.VillainClock.VillainClockTheorem71Two
public import FroehlichSpencer.BKT.Surface.VillainClockDisorderLowerBound

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
open Filter
public section
namespace FroehlichSpencer.BKT
theorem _root_.FSComparator.FS81.planeRotator_powerLaw_lower_bound :
    ∃ β₀ : ℝ, ∃ β' : ℝ → ℝ, Tendsto β' atTop atTop ∧
      ∀ (β : ℝ) (hβ : 0 ≤ β), β₀ < β → 1 / (4 * Real.pi) < β' β ∧
        ∃ A : ℝ, 0 < A ∧ ∀ j ℓ : ℤ × ℤ,
          A * (1 + Real.sqrt (((j.1 - ℓ.1 : ℤ) : ℝ) ^ 2 + ((j.2 - ℓ.2 : ℤ) : ℝ) ^ 2)) ^
              (-(1 / (2 * Real.pi * β' β))) ≤
            planeRotatorCorrelation β hβ 1 j ℓ :=
  by exact FroehlichSpencer.BKT.planeRotator_powerLaw_lower_bound
end FroehlichSpencer.BKT
end

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
public section
namespace FroehlichSpencer.BKT
theorem _root_.FSComparator.FS81.planeRotator_kosterlitzThouless_transition :
    ∃ βc : ℝ, 0 < βc ∧
      (∀ (β : ℝ) (hβ : 0 ≤ β), β < βc →
        ∃ C m : ℝ, 0 < m ∧ ∀ j ℓ : ℤ × ℤ,
          planeRotatorCorrelation β hβ 1 j ℓ ≤
            C * Real.exp (-m * Real.sqrt (((j.1 - ℓ.1 : ℤ) : ℝ) ^ 2 + ((j.2 - ℓ.2 : ℤ) : ℝ) ^ 2))) ∧
      (∀ (β : ℝ) (hβ : 0 ≤ β), βc < β →
        (¬ ∃ C m : ℝ, 0 < m ∧ ∀ j ℓ : ℤ × ℤ,
          planeRotatorCorrelation β hβ 1 j ℓ ≤
            C * Real.exp (-m * Real.sqrt (((j.1 - ℓ.1 : ℤ) : ℝ) ^ 2 + ((j.2 - ℓ.2 : ℤ) : ℝ) ^ 2))) ∧
        ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ j ℓ : ℤ × ℤ,
          R ≤ Real.sqrt (((j.1 - ℓ.1 : ℤ) : ℝ) ^ 2 + ((j.2 - ℓ.2 : ℤ) : ℝ) ^ 2) →
            planeRotatorCorrelation β hβ 1 j ℓ ≤ ε) :=
  by exact FroehlichSpencer.BKT.planeRotator_kosterlitzThouless_transition
end FroehlichSpencer.BKT
end

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
public section
namespace FroehlichSpencer.BKT
theorem _root_.FSComparator.FS81.conditionLambdaGas_secondMomentLimit_lower_bound :
    ∀ δ : ℝ, 0 < δ → ∀ C α ε ν : ℝ, 0 < ν → ∃ β₀ : ℝ, ∀ (β : ℝ) (hβ : 0 < β), β₀ < β →
      ∀ lam : ℤ → ℝ, IsConditionLambda C α ε β lam →
      ∀ (hlam : ∀ q, 0 ≤ lam q) (hlam0 : 0 < lam 0), ν ≤ lam 0 →
      ∃ hS : IsCoulombGasSummable β lam,
        (∃ M : (ℤ × ℤ →₀ ℝ) → ℝ, IsConditionLambdaSecondMomentLimit β hβ lam hlam hlam0 hS M) ∧
        ∀ M : (ℤ × ℤ →₀ ℝ) → ℝ, IsConditionLambdaSecondMomentLimit β hβ lam hlam hlam0 hS M →
          ∀ g : ℤ × ℤ →₀ ℝ, (g.sum fun _ a => a) = 0 →
            (1 - δ) * β * (g.sum fun x a => g.sum fun y b => a * b * coulombPotential (x - y)) ≤
              M g :=
  by exact FroehlichSpencer.BKT.conditionLambdaGas_secondMomentLimit_lower_bound
end FroehlichSpencer.BKT
end

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
open Filter
public section
namespace FroehlichSpencer.BKT
theorem _root_.FSComparator.FS81.conditionLambdaGas_fracCorrelationLimit_upper_bound :
    ∀ ξ : ℝ, 0 < ξ → ξ < 1 → ∀ ε : ℝ, ∃ β' : ℝ → ℝ, Tendsto β' atTop atTop ∧
      ∀ C α ν : ℝ, 0 < ν → ∃ β₀ : ℝ, ∀ β : ℝ, β₀ < β → ∃ A : ℝ,
        ∀ lam : ℤ → ℝ, IsConditionLambda C α ε β lam →
        ∀ (hlam : ∀ q, 0 ≤ lam q) (hlam0 : 0 < lam 0), ν ≤ lam 0 →
        ∃ hS : IsCoulombGasSummable β lam,
          (∃ G : ℤ × ℤ → ℝ, IsConditionLambdaFracCorrelationLimit β lam hlam hlam0 hS ξ G) ∧
          ∀ G : ℤ × ℤ → ℝ, IsConditionLambdaFracCorrelationLimit β lam hlam hlam0 hS ξ G →
            ∀ x : ℤ × ℤ, x ≠ 0 →
              0 ≤ G x ∧ G x ≤ A * Real.sqrt ((x.1 : ℝ) ^ 2 + (x.2 : ℝ) ^ 2) ^ (-β' β) :=
  by exact FroehlichSpencer.BKT.conditionLambdaGas_fracCorrelationLimit_upper_bound
end FroehlichSpencer.BKT
end

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
open Filter
public section
namespace FroehlichSpencer.BKT
theorem _root_.FSComparator.FS81.clock_phase_diagram :
    ∃ βh β₀ : ℝ, 0 < βh ∧ βh ≤ β₀ ∧ ∃ β' : ℝ → ℝ, Tendsto β' atTop atTop ∧ ∃ βbar : ℕ → ℝ,
      (∀ (n : ℕ) (hn : 0 < n), 2 ≤ n → ∀ (β : ℝ) (hβ : 0 ≤ β), β < βh →
        IsClockExpDecay n hn β hβ 1) ∧
      (∀ (n : ℕ) (hn : 0 < n), 2 ≤ n → ∀ (β : ℝ) (hβ : 0 ≤ β), βbar n < β →
        ∀ ξ : ℤ, IsClockLongRangeOrder n hn β hβ ξ) ∧
      ∀ q : ℝ, 0 < q → q < 1 → ∃ β₁ : ℕ → ℝ, Tendsto β₁ atTop atTop ∧ ∃ n₁ : ℕ,
        ∀ (n : ℕ) (hn : 0 < n), n₁ ≤ n → β₀ < β₁ n ∧ β₁ n ≤ βbar n ∧
          ∀ (β : ℝ) (hβ : 0 ≤ β), β₀ ≤ β → β ≤ β₁ n →
            IsClockIntermediatePhase n hn β hβ q (β' β) :=
  by exact FroehlichSpencer.BKT.clock_phase_diagram
end FroehlichSpencer.BKT
end

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
open Filter
public section
namespace FroehlichSpencer.BKT
theorem _root_.FSComparator.FS81.clock_disorder_lowerBound :
    ∃ n₁ : ℝ → ℕ, Tendsto n₁ atTop atTop ∧
      ∀ β : ℝ, 0 ≤ β → ∀ (n : ℕ) (hn : 0 < n), n₁ β ≤ n →
        (∀ k : ℕ, 1 ≤ k → k < n → ∃ D : ℕ → ℝ, IsClockDisorderLimit n hn β ((k : ℝ) / n) D) ∧
        ∃ β''' : ℝ, 0 ≤ β''' ∧ ∃ C : ℝ, 0 < C ∧
          ∀ k : ℕ, 1 ≤ k → k < n → ∀ D : ℕ → ℝ, IsClockDisorderLimit n hn β ((k : ℝ) / n) D →
            ∀ r : ℕ, 0 < r →
              C * (1 + (r : ℝ)) ^ (-(((k : ℝ) / n) ^ 2 * β''' / (2 * Real.pi))) ≤ D r :=
  by exact FroehlichSpencer.BKT.clock_disorder_lowerBound
end FroehlichSpencer.BKT
end

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
public section
namespace FroehlichSpencer.BKT
theorem _root_.FSComparator.FS81.freeVillain_disorderLimit_upper_bound :
    ∀ ξ : ℝ, 0 < ξ → ξ < 1 → ∃ β₀ : ℝ, ∀ (β : ℝ) (hβ : 0 < β), β₀ < β →
      (∃ D : ℕ → ℝ, IsFreeVillainDisorderLimit β hβ ξ D) ∧
      ∃ β'' : ℝ, 0 < β'' ∧ ∃ A : ℝ, ∀ D : ℕ → ℝ, IsFreeVillainDisorderLimit β hβ ξ D →
        ∀ n : ℕ, D n ≤ A * (1 + (n : ℝ)) ^ (-(ξ ^ 2 * β'')) :=
  by exact FroehlichSpencer.BKT.freeVillain_disorderLimit_upper_bound
end FroehlichSpencer.BKT
end

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
open MeasureTheory Filter Topology
public section
namespace FroehlichSpencer.BKT
theorem _root_.FSComparator.FS81.sos_theorem73_dirichlet :
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
  by exact FroehlichSpencer.BKT.sos_theorem73_dirichlet
end FroehlichSpencer.BKT
end

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
open MeasureTheory
public section
namespace FroehlichSpencer.BKT
theorem _root_.FSComparator.FS81.sos_roughening_transition :
    ∃ β₀ β₁ : ℝ, 0 < β₀ ∧ β₀ < β₁ ∧
      (∀ (β : ℝ) (hβ : 0 < β), β ≤ β₀ → ∀ K : ℝ, ∃ (L : ℕ) (u v : Fin L × Fin L),
        ENNReal.ofReal K < ∫⁻ n, ENNReal.ofReal (((n u : ℝ) - n v) ^ 2) ∂sosDirichletLaw L β hβ) ∧
      ∃ C : ℝ, ∀ (β : ℝ) (hβ : 0 < β), β₁ ≤ β → ∀ (L : ℕ) (u v : Fin L × Fin L),
        ∫⁻ n, ENNReal.ofReal (((n u : ℝ) - n v) ^ 2) ∂sosDirichletLaw L β hβ ≤ ENNReal.ofReal C :=
  by exact FroehlichSpencer.BKT.sos_roughening_transition
end FroehlichSpencer.BKT
end

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
@[expose] public section
open Filter Topology MeasureTheory
namespace FroehlichSpencer.BKT.Surface.VillainClock
theorem _root_.FSComparator.FS81.villain_clock_theorem71_1 :
    ∀ (N : ℕ) (hN : 0 < N) (β : ℝ) (hβ : 0 < β),
      ∀ (ξ : ℕ), 1 ≤ ξ → ξ < N →
        (∀ (Λ : Finset (ℤ × ℤ)) (u v : ℤ × ℤ), u ∈ Λ → v ∈ Λ →
          VillainClock.villainContinuousCorrelation β hβ (ξ : ℤ) Λ u v ≤
            ∫ θ, Real.cos ((ξ : ℤ) *
              (VillainClock.latticeAngleLiteral θ u - VillainClock.latticeAngleLiteral θ v))
              ∂FroehlichSpencer.BKT.villainClockModel N hN β hβ Λ) ∧
        ∀ x : ℤ × ℤ,
          VillainClock.villainContinuousLimit β hβ (ξ : ℤ) (0, 0) x ≤
            Filter.limsup
              (fun L : ℕ => ∫ θ, Real.cos ((ξ : ℤ) *
                (VillainClock.latticeAngleLiteral θ (0, 0) - VillainClock.latticeAngleLiteral θ x))
                ∂FroehlichSpencer.BKT.villainClockModel N hN β hβ (VillainClock.freeBox L))
              atTop :=
  by exact FroehlichSpencer.BKT.Surface.VillainClock.villain_clock_theorem71_1
end FroehlichSpencer.BKT.Surface.VillainClock

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
@[expose] public section
open Filter Topology MeasureTheory
namespace FroehlichSpencer.BKT.Surface.VillainClock
theorem _root_.FSComparator.FS81.villain_clock_theorem71_2 :
    ∃ n₀ : ℝ → ℝ → ℕ, ∃ β'' : ℝ → ℕ → ℝ → ℝ,
      (∀ q : ℝ, 0 < q →
        Tendsto (fun β : ℝ => n₀ β q) atTop atTop) ∧
      (∀ β : ℝ, Tendsto (fun q : ℝ => n₀ β q) (𝓝[>] 0) atTop) ∧
      (∀ (β : ℝ) (N : ℕ) (q : ℝ), n₀ β q ≤ N →
        0 < β'' β N q) ∧
      ∀ q : ℝ, 0 < q →
        ∀ (β : ℝ) (hβ : 0 < β) (N : ℕ), n₀ β q ≤ N →
          ∀ (hN : 0 < N) (ξ : ℕ), 0 < ξ → ξ < N →
            q ≤ VillainClock.dipoleGap ((ξ : ℝ) / N) →
              ((∀ (L : ℕ) (a b : VillainClock.rotatorSpinSite L),
                  ∫ θ, Real.cos ((ξ : ℤ) *
                    (VillainClock.latticeAngleLiteral θ (VillainClock.siteToZ a) -
                      VillainClock.latticeAngleLiteral θ (VillainClock.siteToZ b)))
                    ∂FroehlichSpencer.BKT.villainClockModel N hN β hβ (VillainClock.squareBoxZ L) ≤
                    2 * ((↑(VillainClock.freeRadius a b) : ℝ) + 1) ^
                      (-((↑ξ : ℝ) ^ 2 / (2 * Real.pi * β'' β N q)))) ∧
                (∀ (L : ℕ) (u v : ℤ × ℤ),
                  VillainClock.boxRadius u ≤ L → VillainClock.boxRadius v ≤ L →
                    ∫ θ, Real.cos ((ξ : ℤ) *
                      (VillainClock.latticeAngleLiteral θ u - VillainClock.latticeAngleLiteral θ v))
                      ∂FroehlichSpencer.BKT.villainClockModel N hN β hβ (VillainClock.freeBox L) ≤
                      2 * ((↑(VillainClock.l1Dist u v) : ℝ) + 1) ^
                      (-((↑ξ : ℝ) ^ 2 / (2 * Real.pi * β'' β N q)))) ∧
              ∀ (u v : ℤ × ℤ),
                Filter.limsup
                    (fun L : ℕ => ∫ θ, Real.cos ((ξ : ℤ) *
                      (VillainClock.latticeAngleLiteral θ u - VillainClock.latticeAngleLiteral θ v))
                      ∂FroehlichSpencer.BKT.villainClockModel N hN β hβ (VillainClock.freeBox L))
                    atTop ≤
                  2 * ((↑(VillainClock.l1Dist u v) : ℝ) + 1) ^
                    (-((↑ξ : ℝ) ^ 2 / (2 * Real.pi * β'' β N q)))) :=
  by exact FroehlichSpencer.BKT.Surface.VillainClock.villain_clock_theorem71_2
end FroehlichSpencer.BKT.Surface.VillainClock

run_elab Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
@[expose] public section
open Filter
namespace FroehlichSpencer.BKT
theorem _root_.FSComparator.FS81.villainClock_disorder_lowerBound_grid_exhausting :
    ∃ n₁ : ℝ → ℕ, Tendsto n₁ atTop atTop ∧
      ∀ (β : ℝ) (hβ : 0 < β) (N : ℕ) (hN : 0 < N),
        n₁ β ≤ N →
          ∃ (β''' : ℝ), 0 ≤ β''' ∧
            ∃ C : ℝ, 0 < C ∧
              ∀ k : ℕ, 1 ≤ k → k < N →
                ∀ (r : ℕ) (hr : 0 < r) (c : ℝ),
                  IsVillainClockDisorderExhaustingLimitPoint
                    N r β ((k : ℝ) / N) c hβ hN hr →
                  C * (1 + (r : ℝ)) ^
                    (-(((k : ℝ) / N) ^ 2 * β''' / (2 * Real.pi))) ≤ c :=
  by exact FroehlichSpencer.BKT.villainClock_disorder_lowerBound_grid_exhausting
end FroehlichSpencer.BKT
end
