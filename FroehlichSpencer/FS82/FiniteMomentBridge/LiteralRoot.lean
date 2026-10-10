/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.CovarianceTransport.MomentBridge
public import FroehlichSpencer.FS82.FiniteMomentBridge.LogThickBridge
public import FroehlichSpencer.FS82.Root.FiniteMomentComparison
public import FroehlichSpencer.FS82.Surface.BetaDoublePrime
public import FroehlichSpencer.FS82.Surface.DiscreteDualMoment
public import FroehlichSpencer.FS82.Surface.SourceTestToW
public import FroehlichSpencer.FS82.Surface.FiniteLatticeCovarianceQuadratic

/-!
The statement is over the -surface definitions `Surface.discreteDualMoment`,
`Surface.finiteLatticeCovarianceQuadratic` and `Surface.sourceTestToW`.

Two definitional
bridges identify the first two with the source definitions used by CovarianceTransport and the chord covariance construction (the bodies agree
up to the proofs of the gates).

The proof then uses

* the internal first root `Root.fs82_moment_comparison_logThick_box` (MomentComparisonAssembly),
* CovarianceTransport's `literal_discreteDualMoment_eq_sourceDualMoment`,
* the chord covariance construction's `literal_covariance_eq`,
* the log-thick bridge `isLogThickRectBox4_iff`.

The literal root asks for `0 < β'' < β` at every `β ≥ β₀`, which is stronger than the eventual
statement of the internal root, so the threshold is enlarged until `2 β c_pack(β) < 1`.
-/

@[expose] public section

open scoped BigOperators
open Filter
open FroehlichSpencer.FS82.Surface
open FroehlichSpencer.FS82.Gaussian
open FroehlichSpencer.FS82.Root
open FroehlichSpencer.FS82.Moment.SourceConstructor
open FroehlichSpencer.FS82.SourceCovarianceBridge

namespace FroehlichSpencer.FS82.FiniteMomentBridge

local instance sourceRelationEquivalenceGateFiniteMoment :
    FroehlichSpencer.FS82.SourceModels.IntegerDualModel.SourceRelationEquivalenceGate :=
  ⟨FroehlichSpencer.FS82.SourceInterfaceResults.sourceIntegerGaugeRelation_isEquivalence_gate⟩
local instance integerWeightInvariantGateFiniteMoment :
    FroehlichSpencer.FS82.SourceModels.IntegerDualModel.IntegerWeightInvariantGate :=
  ⟨FroehlichSpencer.FS82.SourceInterfaceTheorems.integerDualFieldWeight_respectsGauge_gate⟩
local instance pairingInvariantGateFiniteMoment :
    FroehlichSpencer.FS82.SourceModels.IntegerDualModel.PairingInvariantGate :=
  ⟨FroehlichSpencer.FS82.SourceInterfaceTheorems.integerDualPairing_respectsGauge_gate⟩
local instance partitionUniqueGateFiniteMoment :
    FroehlichSpencer.FS82.SourceModels.IntegerDualModel.IntegerPartitionUniqueGate :=
  ⟨FroehlichSpencer.FS82.SourceInterface.existsUnique_integerDualPartitionFunction⟩

/-!
## Definitional bridges from the surface to the source definitions
-/

/--
The -surface moment is the source moment: the two definitions have the same body
and differ only in the proofs of the gates.
-/
theorem discreteDualMoment_eq_chordMoment (R : RectBox4) (β : ℝ) (hβ : 0 < β) (ε : ℝ)
    (μ : W R) :
    FroehlichSpencer.FS82.Surface.discreteDualMoment R β hβ ε μ =
      FroehlichSpencer.FS82.SourceModels.IntegerDualModel.discreteDualMoment R β hβ ε μ := rfl

/--
The -surface covariance is the chord covariance construction's source covariance.
-/
theorem finiteLatticeCovarianceQuadratic_eq_chord (R : RectBox4) (μ : W R) :
    finiteLatticeCovarianceQuadratic R μ =
      FroehlichSpencer.FS82.SourceInterfaceResults.finiteLatticeCovarianceQuadraticChord R μ := rfl

theorem literalSourceCoClosed_eq_literalWEquivCoClosed (R : RectBox4) (μ : W R) :
    literalSourceCoClosed R μ = literalWEquivCoClosed R μ := by
  apply Subtype.ext
  rfl

/-- **The literal covariance is the internal source covariance.** -/
theorem finiteLatticeCovarianceQuadratic_eq_source (R : RectBox4) (μ : W R) :
    finiteLatticeCovarianceQuadratic R μ =
      quotientCovarianceQuadratic (sourceLatticeComplex (B := R.side))
        (literalSourceCoClosed R μ) := by
  rw [finiteLatticeCovarianceQuadratic_eq_chord,
    FroehlichSpencer.FS82.SourceInterfaceResults.literal_covariance_eq,
    literalSourceCoClosed_eq_literalWEquivCoClosed]

/-- **The literal moment is the internal source moment.** -/
theorem discreteDualMoment_eq_source (R : RectBox4) (β : ℝ) (hβ : 0 < β) (ε : ℝ)
    (μ : W R) :
    FroehlichSpencer.FS82.Surface.discreteDualMoment R β hβ ε μ =
      ENNReal.ofReal (sourceDualMoment β (literalSourceCoClosed R μ) ε) := by
  rw [discreteDualMoment_eq_chordMoment]
  exact literal_discreteDualMoment_eq_sourceDualMoment R β hβ ε μ

/-- The literal and internal `β''` are the same function. -/
theorem betaDoublePrime_eq (cPack : ℝ → ℝ) :
    FroehlichSpencer.FS82.Surface.betaDoublePrime cPack =
      FroehlichSpencer.FS82.Moment.Comparison.betaDoublePrime cPack := rfl

/-! ## The coefficient conditions of the literal root -/

/-- `2 β c_pack(β) → 0` for the box-uniform coefficient of the internal root. -/
theorem tendsto_two_mul_rootPackingCoefficient :
    Tendsto (fun β : ℝ => 2 * β * rootPackingCoefficient β) atTop (nhds 0) := by
  have hscale : Tendsto (fun β : ℝ => β / 432) atTop atTop :=
    tendsto_id.atTop_div_const (by norm_num : (0 : ℝ) < 432)
  have hpoly := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hscale
  have h := hpoly.const_mul
    (2 * 432 * FroehlichSpencer.FS82.Currents.SourcePacking.sourcePackingTailConstant MomentComparisonAssembly.rootRate
      (50 * Real.pi * 10000))
  rw [mul_zero] at h
  refine h.congr fun β => ?_
  simp only [Function.comp_apply, rootPackingCoefficient, pow_one]
  ring

/-- A threshold above the internal one beyond which `2 β c_pack(β) < 1`. -/
theorem exists_literal_threshold :
    ∃ b : ℝ, 0 < b ∧ rootBetaThreshold ≤ b ∧
      ∀ β : ℝ, b ≤ β → 2 * β * rootPackingCoefficient β < 1 := by
  have hev : ∀ᶠ β : ℝ in atTop, 2 * β * rootPackingCoefficient β < 1 :=
    tendsto_two_mul_rootPackingCoefficient.eventually (gt_mem_nhds zero_lt_one)
  obtain ⟨b₁, hb₁⟩ := eventually_atTop.mp hev
  refine ⟨max rootBetaThreshold b₁, lt_of_lt_of_le rootBetaThreshold_pos (le_max_left _ _),
    le_max_left _ _, fun β hβ => hb₁ β (le_trans (le_max_right _ _) hβ)⟩

/-! ## The literal root -/


theorem fs82FiniteVillainDualMomentComparisonLogThick :
∃ β₀ : {b : ℝ // 0 < b}, ∃ cPack : ℝ → ℝ,
      (∀ β : ℝ, β₀.val ≤ β → 0 < cPack β) ∧
      Tendsto (fun β : ℝ => 2 * β * cPack β) atTop (nhds 0) ∧
      (∀ β : ℝ, β₀.val ≤ β →
        0 < betaDoublePrime cPack β ∧ betaDoublePrime cPack β < β) ∧
      Tendsto (betaDoublePrime cPack) atTop atTop ∧
      ∀ β : ℝ, (hβRange : β₀.val ≤ β) →
        ∀ R : RectBox4,
          IsLogThickRectBox4 R →
        ∀ μ : RealDualField R,
          ∀ hglobal : μ ∈ GlobalCoClosed R,
            ∀ hinterior : IsInteriorSupported R μ,
          ∀ ε : ℝ,
            ENNReal.ofReal
                (Real.exp (ε ^ 2 * betaDoublePrime cPack β / 2 *
                  finiteLatticeCovarianceQuadratic R
                    (sourceTestToW R μ hinterior hglobal))) ≤
              discreteDualMoment R β
                (by have := β₀.property; linarith [hβRange]) ε
                (sourceTestToW R μ hinterior hglobal) ∧
            discreteDualMoment R β
                (by have := β₀.property; linarith [hβRange]) ε
                (sourceTestToW R μ hinterior hglobal) ≤
              ENNReal.ofReal
                (Real.exp (ε ^ 2 * β / 2 *
                  finiteLatticeCovarianceQuadratic R
                    (sourceTestToW R μ hinterior hglobal))) := by
  obtain ⟨b, hbpos, hbthr, hb⟩ := exists_literal_threshold
  refine ⟨⟨b, hbpos⟩, rootPackingCoefficient, ?_, tendsto_two_mul_rootPackingCoefficient,
    ?_, ?_, ?_⟩
  · intro β _
    exact rootPackingCoefficient_pos β
  · intro β hβ
    have hβpos : 0 < β := lt_of_lt_of_le hbpos hβ
    have hc : 0 < 2 * β * rootPackingCoefficient β :=
      mul_pos (mul_pos two_pos hβpos) (rootPackingCoefficient_pos β)
    have h1 : 2 * β * rootPackingCoefficient β < 1 := hb β hβ
    unfold betaDoublePrime
    constructor
    · exact mul_pos hβpos (by linarith)
    · nlinarith
  · rw [betaDoublePrime_eq]
    exact rootBetaDoublePrime_behavior.1
  · intro β hβRange R hR μ hglobal hinterior ε
    have hβ : rootBetaThreshold ≤ β := le_trans hbthr hβRange
    obtain ⟨N, m, hN, hm, hmin, hBmax⟩ := (isLogThickRectBox4_iff R).mp hR
    have hroot := fs82_moment_comparison_logThick_box (B := R.side) N m hN hm hmin hBmax hβ
      (literalSourceCoClosed R (sourceTestToW R μ hinterior hglobal)) ε
    rw [discreteDualMoment_eq_source, finiteLatticeCovarianceQuadratic_eq_source,
      betaDoublePrime_eq]
    exact ⟨ENNReal.ofReal_le_ofReal hroot.1, ENNReal.ofReal_le_ofReal hroot.2⟩

end FroehlichSpencer.FS82.FiniteMomentBridge

end
