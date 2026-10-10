module

public import FroehlichSpencer.FS82.SourceInterface.SourceTheorems
public import FroehlichSpencer.FS82.Root.SourceMoment

@[expose] public section

open FroehlichSpencer.FS82.Surface
open FroehlichSpencer.FS82.Gaussian
open FroehlichSpencer.FS82.Moment.SourceConstructor

namespace FroehlichSpencer.FS82.SourceInterfaceResults

/--
The literal selected inverse from the exact surface gate.

-/
noncomputable def finiteLatticeHodgeInverseChord (R : RectBox4) : W R →ₗ[ℝ] W R :=
  Classical.choose (existsUnique_finiteLatticeHodgeInverse_gate R).exists

theorem finiteLatticeHodgeInverseChord_spec (R : RectBox4) (mu : W R) :
    finiteLatticeHodgeOperatorOnCoClosed_internal R
      (finiteLatticeHodgeInverseChord R mu) = mu :=
  Classical.choose_spec (existsUnique_finiteLatticeHodgeInverse_gate R).exists mu

/-- The literal quadratic source used by source. -/
noncomputable def finiteLatticeCovarianceQuadraticChord
    (R : RectBox4) (mu : W R) : ℝ :=
  inner ℝ mu (finiteLatticeHodgeInverseChord R mu)

theorem literal_covariance_eq (R : RectBox4) (mu : W R) :
    finiteLatticeCovarianceQuadraticChord R mu =
      quotientCovarianceQuadratic
        (sourceLatticeComplex (B := R.side))
        (literalWEquivCoClosed R mu) := by
  classical
  let C := latticeExactOneComplex (B := R.side) R.origin
  let e := literalWEquivCoClosed R
  let V : W R →ₗ[ℝ] W R :=
    e.symm.toLinearMap.comp
      ((hodgeInverseOnCoClosed C).comp e.toLinearMap)
  have hV : ∀ x : W R,
      finiteLatticeHodgeOperatorOnCoClosed_internal R (V x) = x := by
    intro x
    dsimp [finiteLatticeHodgeOperatorOnCoClosed_internal]
    apply Subtype.ext
    change finiteLatticeHodgeOperator R
        ((e.symm (hodgeInverseOnCoClosed C (e x)) : W R) : RealDualField R) =
      (x : RealDualField R)
    rw [finiteLatticeHodgeOperator_bridge,
      ← latticeFormLaplacian_eq_stencil (B := R.side) R.origin]
    have h := congrArg Subtype.val (hodgeOnCoClosed_hodgeInverse C (e x))
    change formLaplacian C
        (hodgeInverseOnCoClosed C (e x) : EuclideanSpace ℝ (SourceDualOneCells R.side)) =
      (e x : EuclideanSpace ℝ (SourceDualOneCells R.side)) at h
    change formLaplacian C
        (((V x : W R) : RealDualField R) :
          EuclideanSpace ℝ (SourceDualOneCells R.side)) =
      (((x : W R) : RealDualField R) :
        EuclideanSpace ℝ (SourceDualOneCells R.side))
    simpa [e, V, literalWEquivCoClosed] using h
  have hinv : finiteLatticeHodgeInverseChord R = V := by
    have hchosen : ∀ x : W R,
        finiteLatticeHodgeOperatorOnCoClosed_internal R
          (finiteLatticeHodgeInverseChord R x) = x :=
      finiteLatticeHodgeInverseChord_spec R
    have huniq := (existsUnique_finiteLatticeHodgeInverse_gate R).unique hV hchosen
    exact huniq.symm
  rw [finiteLatticeCovarianceQuadraticChord, hinv]
  simp only [V, LinearMap.comp_apply]
  change inner ℝ (mu : RealDualField R)
      (e.symm (hodgeInverseOnCoClosed C (e mu))) =
    quotientCovarianceQuadratic C (e mu)
  rfl

end FroehlichSpencer.FS82.SourceInterfaceResults
