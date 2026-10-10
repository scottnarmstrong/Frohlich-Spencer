module

public import FroehlichSpencer.FS82.Root.JensenBudget
public import FroehlichSpencer.FS82.Root.MomentComparison
public import FroehlichSpencer.FS82.Currents.LongCurrentEstimate
public import FroehlichSpencer.FS82.Currents.SourcePacking

set_option autoImplicit false

@[expose] public section

open scoped BigOperators InnerProductSpace

namespace FroehlichSpencer.FS82.Root

open FroehlichSpencer.FS82
open FroehlichSpencer.FS82.Currents
open FroehlichSpencer.FS82.Gaussian
open FroehlichSpencer.FS82.Moment.Packing
open FroehlichSpencer.FS82.Moment.SourceConstructor
open FroehlichSpencer.FS82.Moment.SourceJensen
open FroehlichSpencer.FS82.Moment.SourceAssembly
open FroehlichSpencer.FS82.Currents.LongCurrentEstimate
open FroehlichSpencer.FS82.Currents.SourcePacking

noncomputable section

variable {B : Cubical.Box 4} {Ensemble : Type*}

/-- The decay rate of the renormalized source activity after the one-link
integration in Section 2.8. -/
def sourceRenormalizedRate (beta beta₁ : ℝ) : ℝ :=
  (beta / 216 - beta₁) / 2

/-- The source Jensen error with a generic per-current renormalized amplitude.
The phase is the unchanged C2-oriented physical phase from the source
ensemble interface. -/
def genericSourceJensenError (beta : ℝ)
    (z : SourceW B → Ensemble → IntegerCurrent B → ℝ)
    (μ : SourceW B) (t : ℝ) (γ : Ensemble) (i : IntegerCurrent B) : ℝ :=
  sourceJensenGamma (z μ γ i) * (Root.sourcePhysicalTheta beta μ t i)^2

/-- The log-thick SourcePacking short/long estimate for generic renormalized
per-current amplitudes. The short component estimate is an explicit aggregate
budget; LongCurrentPoincare supplies the long-current estimate from the generic exponential
envelope z ≤ exp(-a(‖ρ‖² + L)). -/
theorem sourcePacking_logThick
    [DecidableEq (IntegerCurrent B)]
    (beta beta₁ : ℝ) (N m : ℕ)
    (hN : 1 ≤ N) (hmLog : Real.log (N + 1 : ℝ) ≤ (m : ℝ))
    (hRate : 8 ≤ sourceRenormalizedRate beta beta₁)
    (shortCurrents : SourceW B → Ensemble → Finset (IntegerCurrent B))
    (z : SourceW B → Ensemble → IntegerCurrent B → ℝ)
    (hShort : ∀ μ t γ,
      (∑ i ∈ shortCurrents μ γ,
        genericSourceJensenError beta z μ t γ i) ≤
        81 * sourceComponentCpackPrime (sourceRenormalizedRate beta beta₁)
          (50 * Real.pi * 10000) *
          ∑ p, (sourceHodgeField μ (t * beta) p)^2)
    (T : SourceW B → Ensemble → Finset (ClosedIntegerCurrent B))
    (hLongDisjoint : ∀ μ γ,
      (↑(T μ γ) : Set (ClosedIntegerCurrent B)).PairwiseDisjoint
        (fun j => currentSupport (fun e : Link B => j.1 e)))
    (hLongLength : ∀ μ γ j, j ∈ T μ γ →
      m ≤ (currentSupport (fun e : Link B => j.1 e)).card)
    (hAmplitude : ∀ μ γ i,
      0 ≤ z μ γ i ∧
      z μ γ i ≤ Real.exp (-(sourceRenormalizedRate beta beta₁ *
        (integerCurrentNormSq (fun e : Link B => i e) +
          ((currentSupport (fun e : Link B => i e)).card : ℝ)))))
    (hBmax : ∀ i : Fin 4, B i ≤ N)
    (hShortLongDisjoint : ∀ μ γ,
      Disjoint (shortCurrents μ γ)
        ((T μ γ).image fun j => j.1)) :
    ∀ μ t γ,
      (∑ i ∈ shortCurrents μ γ ∪
          (T μ γ).image (fun j : ClosedIntegerCurrent B => j.1),
        genericSourceJensenError beta z μ t γ i) ≤
        Root.sourceCoefficient beta₁ N m beta *
          ∑ p, (sourceHodgeField μ (t * beta) p)^2 := by
  intro μ t γ
  let τ : SourceW B := (t * beta) •
    Gaussian.latticeVΛ (B := B) Cubical.originZero μ
  have hTheta (j : ClosedIntegerCurrent B) :
      Root.sourcePhysicalTheta beta μ t j.1 =
        latticeCurrentPhase Cubical.originZero j.1 j.2 τ := by
    rfl
  let Tμγ := T μ γ
  have hLongImage :
      (∑ i ∈ Tμγ.image (fun j : ClosedIntegerCurrent B => j.1),
        genericSourceJensenError beta z μ t γ i) =
      ∑ j ∈ Tμγ, Moment.Packing.jensenGamma (z μ γ j.1) *
        (latticeCurrentPhase Cubical.originZero j.1 j.2 τ)^2 := by
    classical
    have hinj : Set.InjOn (fun j : ClosedIntegerCurrent B => j.1)
        (↑Tμγ : Set (ClosedIntegerCurrent B)) := by
      intro j hj k hk heq
      exact Subtype.ext heq
    rw [Finset.sum_image
      (f := fun i : IntegerCurrent B => genericSourceJensenError beta z μ t γ i)
      (g := fun j : ClosedIntegerCurrent B => j.1) hinj]
    apply Finset.sum_congr rfl
    intro j hj
    change sourceJensenGamma (z μ γ j.1) *
        (Root.sourcePhysicalTheta beta μ t j.1)^2 = _
    rw [hTheta]
    rfl
  have hmOne : 1 ≤ m := by
    have hlog : 0 < Real.log (N + 1 : ℝ) := by
      apply Real.log_pos
      norm_num
      exact_mod_cast hN
    exact_mod_cast (lt_of_lt_of_le hlog hmLog)
  have hRateCurrent : sourceRenormalizedRate beta beta₁ = currentRate beta beta₁ := by
    rfl
  have hLongBound :
      (∑ i ∈ Tμγ.image (fun j : ClosedIntegerCurrent B => j.1),
        genericSourceJensenError beta z μ t γ i) ≤
        longCoefficient (sourceRenormalizedRate beta beta₁) N m *
          ∑ p, (sourceHodgeField μ (t * beta) p)^2 := by
    rw [hLongImage]
    have hLongCurrent := longCurrent_jensen_error_c1_sourceField
      N m (sourceRenormalizedRate beta beta₁) Tμγ τ
      (fun i => z μ γ i) hBmax hmOne (by simpa [hRateCurrent] using hRate)
      (hLongDisjoint μ γ)
      (fun j hj => hLongLength μ γ j hj)
      (fun j hj => (hAmplitude μ γ j.1).1)
      (fun j hj => by simpa [hRateCurrent] using (hAmplitude μ γ j.1).2)
    calc
      (∑ j ∈ Tμγ, Moment.Packing.jensenGamma (z μ γ j.1) *
          (latticeCurrentPhase Cubical.originZero j.1 j.2 τ)^2) ≤
        longCoefficient (sourceRenormalizedRate beta beta₁) N m *
          ∑ p : SourceDualTwoCells B,
            ((sourceLatticeComplex (B := B)).d₁
              (τ : EuclideanSpace ℝ (SourceDualOneCells B)) p)^2 := hLongCurrent
      _ = longCoefficient (currentRate beta beta₁) N m *
          ∑ p, (sourceHodgeField μ (t * beta) p)^2 := by
        congr 1
  let shortCoeff : ℝ := 81 * sourceComponentCpackPrime
      (sourceRenormalizedRate beta beta₁) (50 * Real.pi * 10000)
  have hShortBound :
      (∑ i ∈ shortCurrents μ γ,
        genericSourceJensenError beta z μ t γ i) ≤
        shortCoeff * ∑ p, (sourceHodgeField μ (t * beta) p)^2 := by
    simpa [shortCoeff] using hShort μ t γ
  rw [Finset.sum_union (hShortLongDisjoint μ γ)]
  calc
    (∑ i ∈ shortCurrents μ γ,
        genericSourceJensenError beta z μ t γ i) +
      ∑ i ∈ Tμγ.image (fun j : ClosedIntegerCurrent B => j.1),
        genericSourceJensenError beta z μ t γ i ≤
      shortCoeff * ∑ p, (sourceHodgeField μ (t * beta) p)^2 +
        longCoefficient (sourceRenormalizedRate beta beta₁) N m *
          ∑ p, (sourceHodgeField μ (t * beta) p)^2 := by
      exact add_le_add hShortBound hLongBound
    _ = (shortCoeff + longCoefficient (sourceRenormalizedRate beta beta₁) N m) *
        ∑ p, (sourceHodgeField μ (t * beta) p)^2 := by ring
    _ = Root.sourceCoefficient beta₁ N m beta *
        ∑ p, (sourceHodgeField μ (t * beta) p)^2 := by
      congr 1


end

end FroehlichSpencer.FS82.Root
