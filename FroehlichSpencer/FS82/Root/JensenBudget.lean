module

public import FroehlichSpencer.FS82.Moment.SourceEnsembleConstructor
public import FroehlichSpencer.FS82.Moment.SourceAssembly
public import FroehlichSpencer.FS82.Gaussian.LatticePath

/-!
# FS82 (2.101)–(2.107): the source packing budget with Jensen errors

The A0.1 interface of `Root/MomentComparison.lean` needs budgets whose errors
are Jensen errors `γ(z_ρ) θ_ρ²` and whose field is the source Hodge
field `tβ · d₁ V_Λ μ`.

`sourceJensenPackingBudget` defines a budget with
exactly these errors and field, from an explicit current family, activities,
energies and the packing inequality itself.

Its error identity
(`SourceEnsembleJensenInput.sourceError_eq`) then holds by unfolding, and its
field identity by `rfl`; the only analytic content left is the inequality
`Σ_ρ γ(z_ρ) θ_ρ² ≤ c ‖tβ d₁ V_Λ μ‖²` of (2.103)–(2.107).

The activities and energies are inputs rather than fields of a
`SourceEnsembleJensenInput`, which itself depends on the budget.
-/

@[expose] public section

open scoped BigOperators

namespace FroehlichSpencer.FS82.Root

open FroehlichSpencer.FS82
open FroehlichSpencer.FS82.Moment
open FroehlichSpencer.FS82.Moment.SourceConstructor
open FroehlichSpencer.FS82.Moment.SourceEnsembleConstructor

noncomputable section

variable {B : Cubical.Box 4} {Ensemble : Type*}


/--
physical translated phase `⟨T(2πi), tβ V_Λ μ⟩` at an explicit `β`.
-/
def sourcePhysicalTheta (β : ℝ) (μ : SourceW B) (t : ℝ)
    (i : Currents.IntegerCurrent B) : ℝ :=
  inner ℝ (Gaussian.sourceDualTLinear (SourceCoercivity.sourcePhysicalCurrentVector i))
    (sourceGaussianTranslation (B := B) β t μ)


end

end FroehlichSpencer.FS82.Root
