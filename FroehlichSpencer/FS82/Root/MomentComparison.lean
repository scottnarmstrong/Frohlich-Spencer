module

public import FroehlichSpencer.FS82.Root.SourceMoment
public import FroehlichSpencer.FS82.Moment.SourceAssembly
public import FroehlichSpencer.FS82.Currents.SourcePacking

/-!
# FS82 (2.93): the moment comparison on the source carrier

The observable is `sourceDualMoment β μ t = ⟨e^{tα(μ)}⟩_Λ`, the exponential
moment of the discrete dual law on source carrier
(`Root/SourceMoment.lean`).

Its Poisson factorization
`⟨e^{tα(μ)}⟩_Λ = exp(t²β/2 · (μ,V_Λμ)) · R(t)` and the upper half `R ≤ 1`
are proved there with no hypothesis.

* `SourceResidualJensenAggregate` records A0.1 for the actual residual `R`,
  as a countable outer mixture (outer Poisson index) of finite ensemble
  systems;
* each system carries an ensemble-indexed `PackingBudget` whose field is the
  source Hodge field `tβ · d₁ V_Λ μ` and whose coefficient is at most `c`.

`fs82_moment_comparison_of_packing` gives (2.93) with `β'' = β(1 − 2βc)`.

`fs82_moment_comparison_of_expansion` builds A0.1 from `SourceTestedExpansionInput` and `SourceEnsembleJensenData`, given that
the source dual moment is the outer mixture of their moments.

`fs82_moment_comparison_logThick` specializes `c` to SourcePacking's corrected
coefficient, for which `0 < β'' < β` for large `β` and `β'' → ∞`.
-/

@[expose] public section

open scoped BigOperators
open Filter

namespace FroehlichSpencer.FS82.Root

open FroehlichSpencer.FS82
open FroehlichSpencer.FS82.Moment
open FroehlichSpencer.FS82.Moment.SourceConstructor

noncomputable section

variable {B : Cubical.Box 4}

/-- The packing-budget carrier of the source ensembles. -/
abbrev SourcePackingBudget (B : Cubical.Box 4) (Ensemble : Type*) :=
  Comparison.PackingBudget Unit (SourceW B) Ensemble
    (Currents.IntegerCurrent B) (Gaussian.SourceDualTwoCells B)

/--
The corrected (2.101) aggregate A0.1 for the actual source residual, for a
countable outer mixture (outer Poisson branches `ω`) of finite ensemble
systems with budgets `P ω`.

Each inner system has a probability vector on its
ensembles whose weighted Jensen products lie below its residual, and the outer
mixture of the inner residuals is `R(t)`.

Only the test form `μ` at hand is
constrained, so a producer may restrict to interior-supported forms.
-/
structure SourceResidualJensenAggregate (β : ℝ) {Ω Ensemble : Type*}
    [Fintype Ensemble] (P : Ω → SourcePackingBudget B Ensemble)
    (μ : SourceW B) where
  outerWeight : Ω → ℝ
  outerWeight_nonneg : ∀ ω, 0 ≤ outerWeight ω
  outerWeight_hasSum : HasSum outerWeight 1
  innerWeight : Ω → Ensemble → ℝ
  innerWeight_nonneg : ∀ ω γ, 0 ≤ innerWeight ω γ
  innerWeight_sum : ∀ ω, ∑ γ, innerWeight ω γ = 1
  innerResidual : ℝ → Ω → ℝ
  inner_aggregate : ∀ t ω,
    (∑ γ, innerWeight ω γ *
      (∏ i ∈ (P ω).currents () μ γ, Real.exp (-(P ω).error () μ t γ i))) ≤
        innerResidual t ω
  outer_hasSum : ∀ t,
    HasSum (fun ω => outerWeight ω * innerResidual t ω)
      (sourceResidual β μ t)

/-- The packing budgets turn A0.1 into the residual lower bound
`R(t) ≥ exp(-c t²β² (μ, V_Λ μ))`. -/
theorem sourceResidual_lower_of_packing {β c : ℝ} {Ω Ensemble : Type*}
    [Fintype Ensemble] (P : Ω → SourcePackingBudget B Ensemble)
    (hCoef : ∀ ω, (P ω).coefficient ≤ c)
    (hField : ∀ ω μ s p, (P ω).field () μ s p =
      SourceAssembly.sourceHodgeField μ (s * β) p)
    {μ : SourceW B} (L : SourceResidualJensenAggregate β P μ) (t : ℝ) :
    Real.exp (-(c * (t ^ 2 * β ^ 2) *
      Gaussian.quotientCovarianceQuadratic (sourceLatticeComplex (B := B)) μ)) ≤
        sourceResidual β μ t := by
  classical
  set Q := Gaussian.quotientCovarianceQuadratic (sourceLatticeComplex (B := B)) μ
  set E := c * (t ^ 2 * β ^ 2) * Q
  have hQ : 0 ≤ Q := Gaussian.quotientCovarianceQuadratic_nonneg _ μ
  have hEnergy : ∀ ω γ,
      (∑ i ∈ (P ω).currents () μ γ, (P ω).error () μ t γ i) ≤ E := by
    intro ω γ
    have h := (P ω).budget () μ t γ
    simp only [hField] at h
    rw [SourceAssembly.sourceHodgeField_energy, mul_pow] at h
    calc _ ≤ (P ω).coefficient * (t ^ 2 * β ^ 2 * Q) := h
      _ ≤ c * (t ^ 2 * β ^ 2 * Q) :=
          mul_le_mul_of_nonneg_right (hCoef ω) (by positivity)
      _ = E := by ring
  have hInner : ∀ ω, Real.exp (-E) ≤ L.innerResidual t ω := by
    intro ω
    have hProd : ∀ γ, Real.exp (-E) ≤
        ∏ i ∈ (P ω).currents () μ γ, Real.exp (-(P ω).error () μ t γ i) := by
      intro γ
      rw [← Real.exp_sum, Finset.sum_neg_distrib]
      exact Real.exp_le_exp.mpr (neg_le_neg (hEnergy ω γ))
    calc Real.exp (-E) = ∑ γ, L.innerWeight ω γ * Real.exp (-E) := by
          rw [← Finset.sum_mul, L.innerWeight_sum, one_mul]
      _ ≤ ∑ γ, L.innerWeight ω γ *
          (∏ i ∈ (P ω).currents () μ γ, Real.exp (-(P ω).error () μ t γ i)) :=
          Finset.sum_le_sum fun γ _ =>
            mul_le_mul_of_nonneg_left (hProd γ) (L.innerWeight_nonneg ω γ)
      _ ≤ L.innerResidual t ω := L.inner_aggregate t ω
  have hConst : HasSum (fun ω => L.outerWeight ω * Real.exp (-E))
      (1 * Real.exp (-E)) := L.outerWeight_hasSum.mul_right _
  rw [one_mul] at hConst
  exact hasSum_le (fun ω => mul_le_mul_of_nonneg_left (hInner ω)
    (L.outerWeight_nonneg ω)) hConst (L.outer_hasSum t)

/--
**FS82 (2.93), algebraic interface.** For the source dual law at
`β > 0`, every co-closed test form `μ` and every `t`,
`exp(t²β''/2 · (μ,V_Λμ)) ≤ ⟨e^{tα(μ)}⟩_Λ ≤ exp(t²β/2 · (μ,V_Λμ))`
with `β'' = β(1 − 2β c)`.

The upper half uses no hypothesis.

The free-standing pair `(P, L)` is close to the lower bound itself: one
current with error `-log R(t)` satisfies both whenever the lower bound holds.

The source content of the lower half is in
`fs82_moment_comparison_of_expansion`, where the errors are Jensen
errors of the actual ensemble laws.
-/
theorem fs82_moment_comparison_of_packing {β c : ℝ} (hβ : 0 < β)
    {Ω Ensemble : Type*} [Fintype Ensemble]
    (P : Ω → SourcePackingBudget B Ensemble)
    (hCoef : ∀ ω, (P ω).coefficient ≤ c)
    (hField : ∀ ω μ s p, (P ω).field () μ s p =
      SourceAssembly.sourceHodgeField μ (s * β) p)
    {μ : SourceW B} (L : SourceResidualJensenAggregate β P μ) (t : ℝ) :
    Real.exp ((t ^ 2 * (β * (1 - 2 * β * c)) / 2) *
        Gaussian.quotientCovarianceQuadratic (sourceLatticeComplex (B := B)) μ) ≤
      sourceDualMoment β μ t ∧
    sourceDualMoment β μ t ≤
      Real.exp ((t ^ 2 * β / 2) *
        Gaussian.quotientCovarianceQuadratic (sourceLatticeComplex (B := B)) μ) := by
  refine ⟨?_, sourceDualMoment_le_gaussian hβ μ t⟩
  rw [sourceDualMoment_eq_gaussian_mul_residual hβ]
  set Q := Gaussian.quotientCovarianceQuadratic (sourceLatticeComplex (B := B)) μ
  have hlow := sourceResidual_lower_of_packing P hCoef hField L t
  calc Real.exp ((t ^ 2 * (β * (1 - 2 * β * c)) / 2) * Q)
      = Real.exp ((t ^ 2 * β / 2) * Q) *
          Real.exp (-(c * (t ^ 2 * β ^ 2) * Q)) := by
        rw [← Real.exp_add]
        congr 1
        ring
    _ ≤ Real.exp ((t ^ 2 * β / 2) * Q) * sourceResidual β μ t :=
        mul_le_mul_of_nonneg_left hlow (Real.exp_pos _).le


/-! ## The log-thick class and SourcePacking's corrected coefficient -/

/-- SourcePacking's corrected combined coefficient at Jensen constant
`Cθ = 50π·10⁴`. -/
abbrev sourceCoefficient (beta₁ : ℝ) (N m : ℕ) (beta : ℝ) : ℝ :=
  Currents.SourcePacking.sourcePackingCoefficient beta beta₁ (50 * Real.pi * 10000) N m


end

end FroehlichSpencer.FS82.Root
