/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Root.BranchJensenEstimate
public import FroehlichSpencer.FS82.Currents.Padding

/-!
# the first root, (2.93) on log-thick boxes with no branch inputs

Every branch carries its
tested expansion `branchExpansion` and its renormalized Jensen package `branchJensen`; root
consumes them.

The packing coefficient is replaced by the box-uniform
`rootPackingCoefficient β = C · exp(−β/432)`, so that `β''(β) = β(1 − 2β c_pack(β))` does not
depend on the box.
-/

open MeasureTheory Filter
open scoped BigOperators InnerProductSpace
open FroehlichSpencer.FS82.Gaussian
open FroehlichSpencer.FS82.Currents
open FroehlichSpencer.FS82.Moment
open FroehlichSpencer.FS82.Moment.ExpansionIntegral
open FroehlichSpencer.FS82.Moment.SourceConstructor
open FroehlichSpencer.FS82.Moment.Comparison
open FroehlichSpencer.FS82.Poisson
open FroehlichSpencer.FS82.Root.RenormalizedInterface
open FroehlichSpencer.FS82.Root.MomentComparisonAssembly

@[expose] public section

namespace FroehlichSpencer.FS82.Root

variable {B : Cubical.Box 4}

/-! ## The outer layer at the root activity -/

theorem sourceAssignmentIntegerFrequency_ne_zero (q : SourcePoissonEdge B → ℕ) (e : Link B) :
    sourceAssignmentIntegerFrequency q e ≠ 0 := by
  unfold sourceAssignmentIntegerFrequency positiveMode
  exact_mod_cast Nat.succ_ne_zero (q e)

/--
The fixed-frequency separated expansion of each assignment at the root activity (/Expansion).
-/
noncomputable def rootTerms (q : SourcePoissonEdge B → ℕ) : List (CurrentExpansionTerm B) :=
  chooseFixedFrequencyExpansion (sourceAssignmentIntegerActivity rootActivity)
    rootIntegerActivity_nonneg (fun n _ => rootActivity_pos n.natAbs)
    (sourceAssignmentIntegerFrequency q) (sourceAssignmentIntegerFrequency_ne_zero q)

theorem rootTerms_spec (q : SourcePoissonEdge B → ℕ) :
    IsFixedFrequencyCurrentExpansion (sourceAssignmentIntegerFrequency q)
      (sourceAssignmentIntegerActivity rootActivity) (rootTerms q) :=
  (chooseFixedFrequencyExpansion_spec _ _ _ _ _).1

/-- The hypotheses of the branch construction hold on every terminal branch. -/
theorem rootBranchHyp {β : ℝ} (hβ : 0 < β)
    (hRate : 0 < sourceRenormalizedRate β rootRate)
    (ω : Σ q, SourceExpansionBranch (rootTerms (B := B)) q) :
    BranchHyp β rootRate (sourceAssignmentIntegerFrequency ω.1)
      (sourceAssignmentIntegerActivity rootActivity)
      (sourceExpansionBranchTerm rootTerms ω.1 ω.2).state := by
  obtain ⟨_, hsep, hvalid, _, _, _, hcoeff, _⟩ := rootTerms_spec ω.1
  have hb : sourceExpansionBranchTerm rootTerms ω.1 ω.2 ∈ rootTerms ω.1 := by
    simp [sourceExpansionBranchTerm]
  exact {
    beta_pos := hβ
    rate_pos := hRate
    separated := hsep _ hb
    valid := hvalid _ hb
    coeff_pos := hcoeff _ hb
    coeff_le := fun h hh =>
      lineageCoefficient_rootActivity_le _ h ((hvalid _ hb).1 h hh).1 ((hvalid _ hb).1 h hh).2 }

/-- the branch mixture's normalized branch moment is the moment of the branch expansion. -/
theorem sourceExpansionBranchMoment_eq_gaugeBranch {β : ℝ} (hβ : 0 ≤ β) (t : ℝ) (μ : SourceW B)
    (ω : Σ q, SourceExpansionBranch (rootTerms (B := B)) q) :
    sourceExpansionBranchMoment β t hβ μ rootActivity rootTerms ω =
      (gaugeBranchIntegral β hβ t μ
          (stateActivity (sourceAssignmentIntegerFrequency ω.1)
            (sourceAssignmentIntegerActivity rootActivity)
            (sourceExpansionBranchTerm rootTerms ω.1 ω.2).state)
          (stateCurrent (sourceAssignmentIntegerFrequency ω.1)
            (sourceExpansionBranchTerm rootTerms ω.1 ω.2).state)).re /
        (gaugeBranchIntegral β hβ 0 μ
          (stateActivity (sourceAssignmentIntegerFrequency ω.1)
            (sourceAssignmentIntegerActivity rootActivity)
            (sourceExpansionBranchTerm rootTerms ω.1 ω.2).state)
          (stateCurrent (sourceAssignmentIntegerFrequency ω.1)
            (sourceExpansionBranchTerm rootTerms ω.1 ω.2).state)).re := by
  obtain ⟨_, _, _, hweight, _, _, _, _⟩ := rootTerms_spec ω.1
  have hb : sourceExpansionBranchTerm rootTerms ω.1 ω.2 ∈ rootTerms ω.1 := by
    simp [sourceExpansionBranchTerm]
  have hw : 0 < (sourceExpansionBranchTerm rootTerms ω.1 ω.2).weight := hweight _ hb
  have hzero : sourceExpansionBranchZeroIntegral β hβ ω.1 rootActivity
      (sourceExpansionBranchTerm rootTerms ω.1 ω.2) =
      (sourceExpansionBranchIntegral β 0 hβ μ ω.1 rootActivity
        (sourceExpansionBranchTerm rootTerms ω.1 ω.2)).re := by
    simp [sourceExpansionBranchIntegral, sourceExpansionBranchZeroIntegral]
  unfold sourceExpansionBranchMoment sourceExpansionBranchRawMoment sourceExpansionBranchMass
  rw [hzero, sourceExpansionBranchIntegral_eq_gaugeBranchIntegral,
    sourceExpansionBranchIntegral_eq_gaugeBranchIntegral, mul_div_mul_left _ _ hw.ne']

/-! ## The box-uniform packing coefficient -/

/-- The box-uniform packing coefficient `c_pack(β) = C e^{−β/432}`. -/
noncomputable def rootPackingCoefficient (β : ℝ) : ℝ :=
  SourcePacking.sourcePackingTailConstant rootRate (50 * Real.pi * 10000) * Real.exp (-(β / 432))

/-- The threshold above which the renormalized rate is at least `8`. -/
noncomputable def rootBetaThreshold : ℝ := 216 * (16 + rootRate)

theorem rootBetaThreshold_pos : 0 < rootBetaThreshold := by
  unfold rootBetaThreshold
  have := rootRate_nonneg
  positivity

theorem rootRate_ge_eight {β : ℝ} (hβ : rootBetaThreshold ≤ β) :
    8 ≤ sourceRenormalizedRate β rootRate := by
  unfold rootBetaThreshold at hβ
  unfold sourceRenormalizedRate
  linarith

theorem rootPackingCoefficient_pos (β : ℝ) : 0 < rootPackingCoefficient β :=
  mul_pos (SourcePacking.sourcePackingTailConstant_pos _ _) (Real.exp_pos _)

/-- **Box uniformity.** On every log-thick class, SourcePacking's coefficient is at most the box-uniform
`c_pack(β)` once `β` is above the threshold. -/
theorem sourceCoefficient_le_rootPackingCoefficient (N m : ℕ) (hN : 1 ≤ N)
    (hm : Real.log (N + 1 : ℝ) ≤ (m : ℝ)) {β : ℝ} (hβ : rootBetaThreshold ≤ β) :
    sourceCoefficient rootRate N m β ≤ rootPackingCoefficient β := by
  have hRate : 8 ≤ Packing.currentRate β rootRate := rootRate_ge_eight hβ
  simpa [rootPackingCoefficient, SourcePacking.sourcePackingTailConstant] using
    SourcePacking.sourcePackingCoefficient_exp_bound β rootRate (50 * Real.pi * 10000) N m hN hm hRate

/-- `β''(β) = β(1 − 2β c_pack(β))` tends to infinity and satisfies `0 < β'' < β` for large
`β`. -/
theorem rootBetaDoublePrime_behavior :
    Tendsto (betaDoublePrime rootPackingCoefficient) atTop atTop ∧
      ∀ᶠ b : ℝ in atTop, 0 < betaDoublePrime rootPackingCoefficient b ∧
        betaDoublePrime rootPackingCoefficient b < b :=
  exponentialPacking_implies_comparison_behavior rootPackingCoefficient _
    (SourcePacking.sourcePackingTailConstant_pos rootRate (50 * Real.pi * 10000))
    (Eventually.of_forall rootPackingCoefficient_pos)
    (Eventually.of_forall fun _ => le_rfl)

/-! ## The root -/

/-- The log-thick class of boxes: `log(N + 1) ≤ m ≤ B i ≤ N` for some `N ≥ 1` and `m`. -/
def IsLogThickBox (B : Cubical.Box 4) : Prop :=
  ∃ N m : ℕ, 1 ≤ N ∧ Real.log (N + 1 : ℝ) ≤ (m : ℝ) ∧
    (∀ i : Fin 4, m ≤ B i) ∧ (∀ i : Fin 4, B i ≤ N)

/-- The outer index: an assignment and a terminal branch of its expansion. -/
abbrev RootBranch (B : Cubical.Box 4) :=
  Σ q : SourcePoissonEdge B → ℕ, SourceExpansionBranch (rootTerms (B := B)) q

/-- The integer frequency of a root branch. -/
noncomputable abbrev rootBranchFrequency (ω : RootBranch B) : Link B → ℤ :=
  sourceAssignmentIntegerFrequency ω.1

/-- The terminal state of a root branch. -/
noncomputable abbrev rootBranchState (ω : RootBranch B) : CurrentState B :=
  (sourceExpansionBranchTerm rootTerms ω.1 ω.2).state

/-- The lineages of a root branch: the Jensen index. -/
abbrev RootBranchIndex (ω : RootBranch B) := {h : ExpansionLineage B // h ∈ rootBranchState ω}

theorem rootBeta_pos {β : ℝ} (hβ : rootBetaThreshold ≤ β) : 0 < β :=
  lt_of_lt_of_le rootBetaThreshold_pos hβ

theorem rootRate_pos {β : ℝ} (hβ : rootBetaThreshold ≤ β) :
    0 < sourceRenormalizedRate β rootRate := by
  have := rootRate_ge_eight hβ
  linarith

/-- The branch hypotheses of a root branch above the threshold. -/
theorem rootHyp {β : ℝ} (hβ : rootBetaThreshold ≤ β) (ω : RootBranch B) :
    BranchHyp β rootRate (rootBranchFrequency ω)
      (sourceAssignmentIntegerActivity rootActivity) (rootBranchState ω) :=
  rootBranchHyp (rootBeta_pos hβ) (rootRate_pos hβ) ω


noncomputable def rootExpansion (N m : ℕ) (hN : 1 ≤ N)
    (hm : Real.log (N + 1 : ℝ) ≤ (m : ℝ))
    (hmin : ∀ i : Fin 4, m ≤ B i) (hBmax : ∀ i : Fin 4, B i ≤ N)
    {β : ℝ} (hβ : rootBetaThreshold ≤ β) (ω : RootBranch B) :=
  branchExpansion N m hN hm (rootRate_ge_eight hβ) hmin hBmax (rootHyp hβ ω)


noncomputable def rootJensen (N m : ℕ) (hN : 1 ≤ N)
    (hm : Real.log (N + 1 : ℝ) ≤ (m : ℝ))
    (hmin : ∀ i : Fin 4, m ≤ B i) (hBmax : ∀ i : Fin 4, B i ≤ N)
    {β : ℝ} (hβ : rootBetaThreshold ≤ β) (ω : RootBranch B) :=
  branchJensen N m hN hm (rootRate_ge_eight hβ) hmin hBmax (rootHyp hβ ω)

theorem rootExpansion_moment (N m : ℕ) (hN : 1 ≤ N)
    (hm : Real.log (N + 1 : ℝ) ≤ (m : ℝ))
    (hmin : ∀ i : Fin 4, m ≤ B i) (hBmax : ∀ i : Fin 4, B i ≤ N)
    {β : ℝ} (hβ : rootBetaThreshold ≤ β) (ω : RootBranch B) (μ : SourceW B) (t : ℝ) :
    (rootExpansion N m hN hm hmin hBmax hβ ω).moment μ t =
      sourceExpansionBranchMoment β t (rootBeta_pos hβ).le μ rootActivity rootTerms ω :=
  (sourceExpansionBranchMoment_eq_gaugeBranch (rootBeta_pos hβ).le t μ ω).symm


theorem rootOuter (N m : ℕ) (hN : 1 ≤ N)
    (hm : Real.log (N + 1 : ℝ) ≤ (m : ℝ))
    (hmin : ∀ i : Fin 4, m ≤ B i) (hBmax : ∀ i : Fin 4, B i ≤ N)
    {β : ℝ} (hβ : rootBetaThreshold ≤ β) (μ : SourceW B) :
    (∀ ω : RootBranch B,
      0 ≤ sourceExpansionBranchWeight β (rootBeta_pos hβ) rootActivity rootTerms ω) ∧
    HasSum (sourceExpansionBranchWeight (B := B) β (rootBeta_pos hβ) rootActivity rootTerms) 1 ∧
    ∀ t : ℝ, HasSum (fun ω : RootBranch B =>
      sourceExpansionBranchWeight β (rootBeta_pos hβ) rootActivity rootTerms ω *
        (rootExpansion N m hN hm hmin hBmax hβ ω).moment μ t) (sourceDualMoment β μ t) := by
  obtain ⟨hw0, hw1, hOuter⟩ := sourceDualMoment_hasSum_branch_of_positiveType (rootBeta_pos hβ)
    rootActivity hasSum_inactiveWeight_rootActivity inactiveWeight_rootActivity_nonneg
    (fun q => rootActivity_pos _) μ (rootTerms (B := B)) rootTerms_spec
  refine ⟨hw0, hw1, fun t => ?_⟩
  have h := hOuter t
  have hfun : (fun ω : RootBranch B =>
      sourceExpansionBranchWeight β (rootBeta_pos hβ) rootActivity rootTerms ω *
        (rootExpansion N m hN hm hmin hBmax hβ ω).moment μ t) =
      fun ω => sourceExpansionBranchWeight β (rootBeta_pos hβ) rootActivity rootTerms ω *
        sourceExpansionBranchMoment β t (rootBeta_pos hβ).le μ rootActivity rootTerms ω := by
    funext ω
    rw [rootExpansion_moment]
  rw [hfun]
  exact h

/-- **FS82 (2.93) on a log-thick box, with no branch inputs.** For `β` above the explicit
threshold, every test `μ ∈ W` and every real `t`,

`exp(t²β''/2 · ⟨μ, V_Λ μ⟩) ≤ ⟨e^{tα(μ)}⟩ ≤ exp(t²β/2 · ⟨μ, V_Λ μ⟩)`,

with the box-uniform `β'' = β(1 − 2β c_pack(β))`. -/
theorem fs82_moment_comparison_logThick_box (N m : ℕ) (hN : 1 ≤ N)
    (hm : Real.log (N + 1 : ℝ) ≤ (m : ℝ))
    (hmin : ∀ i : Fin 4, m ≤ B i) (hBmax : ∀ i : Fin 4, B i ≤ N)
    {β : ℝ} (hβ : rootBetaThreshold ≤ β) (μ : SourceW B) (t : ℝ) :
    Real.exp ((t ^ 2 * betaDoublePrime rootPackingCoefficient β / 2) *
        quotientCovarianceQuadratic (sourceLatticeComplex (B := B)) μ) ≤
      sourceDualMoment β μ t ∧
    sourceDualMoment β μ t ≤
      Real.exp ((t ^ 2 * β / 2) *
        quotientCovarianceQuadratic (sourceLatticeComplex (B := B)) μ) := by
  obtain ⟨hw0, hw1, hOuter⟩ := rootOuter N m hN hm hmin hBmax hβ μ
  exact fs82_moment_comparison_logThick_of_renormalizedInputs (B := B) rootRate N m hN hm
    hmin hBmax (rootBeta_pos hβ) (rootRate_ge_eight hβ)
    (Ω := RootBranch B) (Ensemble := Unit)
    (Mode := fun ω => RootBranchIndex ω → RenormalizedFamily.RenormalizedCharacters.Sign)
    (I := fun ω => RootBranchIndex ω)
    (V := fun ω => BranchRetained (rootHyp hβ ω))
    (fun ω _ _ => branchFamily (rootBranchFrequency ω) (rootBranchState ω))
    (fun ω _ _ => branchZ β (rootBranchFrequency ω)
      (sourceAssignmentIntegerActivity rootActivity) (rootBranchState ω))
    (fun ω _ _ => branchFamily_pairwiseDisjoint (rootHyp hβ ω))
    (fun ω _ _ j => branchZ_envelope (rootHyp hβ ω) j)
    (rootExpansion N m hN hm hmin hBmax hβ)
    (rootJensen N m hN hm hmin hBmax hβ)
    (fun ω => branchExpansion_beta N m hN hm (rootRate_ge_eight hβ) hmin hBmax (rootHyp hβ ω))
    μ (sourceExpansionBranchWeight β (rootBeta_pos hβ) rootActivity rootTerms) hw0 hw1 hOuter
    (rootPackingCoefficient β) (sourceCoefficient_le_rootPackingCoefficient N m hN hm hβ) t

/-- **The first root.** There are `β₀` and a box-independent `c_pack` with
`β''(β) = β(1 − 2β c_pack(β)) → ∞` and `0 < β'' < β` for large `β`, such that for every log-thick
box, every `β ≥ β₀`, every test `μ ∈ W` and every real `t`, both inequalities of (2.93) hold
with the source covariance. -/
theorem fs82_moment_comparison_root :
    ∃ β₀ : ℝ, ∃ cPack : ℝ → ℝ,
      (Tendsto (betaDoublePrime cPack) atTop atTop ∧
        ∀ᶠ b : ℝ in atTop, 0 < betaDoublePrime cPack b ∧ betaDoublePrime cPack b < b) ∧
      ∀ B : Cubical.Box 4, IsLogThickBox B → ∀ β : ℝ, β₀ ≤ β →
        ∀ (μ : SourceW B) (t : ℝ),
          Real.exp ((t ^ 2 * betaDoublePrime cPack β / 2) *
              quotientCovarianceQuadratic (sourceLatticeComplex (B := B)) μ) ≤
            sourceDualMoment β μ t ∧
          sourceDualMoment β μ t ≤
            Real.exp ((t ^ 2 * β / 2) *
              quotientCovarianceQuadratic (sourceLatticeComplex (B := B)) μ) := by
  refine ⟨rootBetaThreshold, rootPackingCoefficient, rootBetaDoublePrime_behavior, ?_⟩
  rintro B ⟨N, m, hN, hm, hmin, hBmax⟩ β hβ μ t
  exact fs82_moment_comparison_logThick_box N m hN hm hmin hBmax hβ μ t

end FroehlichSpencer.FS82.Root

end
