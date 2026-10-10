/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Wilson.PerimeterJensen
public import FroehlichSpencer.FS82.Wilson.PerimeterLoopPhase
public import FroehlichSpencer.FS82.Wilson.PerimeterChordBridge
public import FroehlichSpencer.FS82.Wilson.GaussianShift
public import FroehlichSpencer.FS82.Root.ShortAggregateEstimate

/-!
# the finite-volume perimeter law (2.8) on cubes

For `β ≥ β₀` there is `d_β ≥ 0` such that for all `L, T ≥ 1` and every cube of half-side
`N ≥ max(L,T) + 1`,

`exp(−d_β (L + T)) ≤ ⟨W(ℒ_{L×T})⟩_{β, cube N}`,

The assembly follows FS82 §2.7–§2.9:

1.

The chord bridge: that ratio is the source dual moment at the test `δσ = d₁†σ` and tilt
   `t = −1/β`.
3.

The first root's outer mixture and branch identities, with Jensen applied to phase
   representatives modulo `2π` (`sourceDualMoment_lower_of_phaseRepresentatives`).
4.

The representatives: by (2.51) the curvature of the Gaussian translation is the integer sheet
   minus the loop field `ε` on every plaquette, so each short component has the representative
   `2π⟨ε, relative filling⟩` and each long component one in `[−π, π]`
   (`relative_filling_wilson_bound`).
5.

The constant is `d_β = 6/(2β) + 486 c'_pack(a) + 40π²/a²` with `a = (β/216 − β₁)/2`, and
`β₀ = 216 (22 + β₁)`, which makes `a ≥ 11`.
-/

open scoped BigOperators
open FroehlichSpencer.FS82.Gaussian
open FroehlichSpencer.FS82.Currents
open FroehlichSpencer.FS82.Currents.SourcePacking
open FroehlichSpencer.FS82.Currents.PlaquetteCarrierPacking
open FroehlichSpencer.FS82.Currents.ShortPhaseAggregate
open FroehlichSpencer.FS82.Currents.ShortComponentPhase
open FroehlichSpencer.FS82.Moment
open FroehlichSpencer.FS82.Moment.Packing
open FroehlichSpencer.FS82.Moment.ExpansionIntegral
open FroehlichSpencer.FS82.Moment.SourceConstructor
open FroehlichSpencer.FS82.Infinite
open FroehlichSpencer.FS82.Root
open FroehlichSpencer.FS82.Root.MomentComparisonAssembly

@[expose] public section

namespace FroehlichSpencer.FS82.Wilson

noncomputable section

variable {B : Cubical.Box 4}

/-! ### The Wilson phases on a root branch -/

/-- The two Jensen weights have the same formula. -/
theorem sourceJensenGamma_eq_jensenGamma (z : ℝ) :
    SourceJensen.sourceJensenGamma z = jensenGamma z := by
  unfold SourceJensen.sourceJensenGamma jensenGamma
  rfl

/-- The Gaussian translation of the sheet test at tilt `−1/β` is minus the Wilson shift. -/
theorem sourceGaussianTranslation_sheetTest {β : ℝ} (hβ : 0 < β)
    (σ : EuclideanSpace ℝ (SourceDualTwoCells B)) :
    sourceGaussianTranslation (B := B) β (-1 / β) (sheetTest σ) =
      -wilsonGaussianShift (sourceLatticeComplex (B := B)) σ := by
  have hc : (-1 / β) * β = -1 := by field_simp
  unfold sourceGaussianTranslation
  rw [hc, neg_one_smul]
  rfl

/-- **The Wilson phase representatives on a root branch.** For the test `d₁†σ` of an integer
sheet `σ` at tilt `−1/β`, the translated phases of a root branch have representatives modulo
`2π` whose Jensen budget is bounded by the loop field `ε = σ − Π_{range d₁} σ` and a term that is
exponentially small in the box size. -/
theorem rootBranch_wilsonPhases {β : ℝ} (hβ : rootBetaThreshold ≤ β)
    (ha : 7 ≤ sourceRenormalizedRate β rootRate)
    (m N : ℕ) (hmin : ∀ i, m ≤ B i) (hBmax : ∀ i : Fin 4, B i ≤ N)
    (σ : EuclideanSpace ℝ (SourceDualTwoCells B)) (sheet : SourceDualTwoCells B → ℤ)
    (hsheet : ∀ f, ((sheet f : ℤ) : ℝ) = σ f) (ω : RootBranch B) :
    ∃ θ' : RootBranchIndex ω → ℝ,
      (∀ i, branchAmp β (rootBranchFrequency ω) (sourceAssignmentIntegerActivity rootActivity)
          (rootBranchState ω) i ≠ 0 → ∃ n : ℤ,
        sourcePhysicalTheta β (sheetTest σ) (-1 / β)
            (stateCurrent (rootBranchFrequency ω) (rootBranchState ω) i) + θ' i =
          2 * Real.pi * (n : ℝ)) ∧
      ∑ i, SourceJensen.sourceJensenGamma
          (branchAmp β (rootBranchFrequency ω) (sourceAssignmentIntegerActivity rootActivity)
            (rootBranchState ω) i) * θ' i ^ 2 ≤
        81 * sourceComponentCpackPrime (sourceRenormalizedRate β rootRate)
              relativeFillingConstant *
            ‖loopFieldResidual (sourceLatticeComplex (B := B)) σ‖ ^ 2 +
          (20 * Real.pi ^ 2 / (sourceRenormalizedRate β rootRate) ^ 2) *
            ((4 * (N + 1) ^ 4 : ℕ) : ℝ) *
            Real.exp (-((sourceRenormalizedRate β rootRate - 7) * (m : ℝ))) := by
  classical
  have H := rootHyp hβ ω
  have hβpos := rootBeta_pos hβ
  let C := sourceLatticeComplex (B := B)
  let ε := loopFieldResidual C σ
  let tau := sourceGaussianTranslation (B := B) β (-1 / β) (sheetTest σ)
  have hshift : C.d₁ tau = -σ - (-ε) := by
    change C.d₁ (sourceGaussianTranslation (B := B) β (-1 / β) (sheetTest σ)) = _
    rw [sourceGaussianTranslation_sheetTest hβpos, map_neg, wilsonGaussianShift_curl]
    abel
  have hdecomp := loopField_plaquette_decomposition tau (-σ) (-ε) (fun f => -sheet f)
    (fun f => by simp [hsheet f]) hshift
  let S : Finset (IntegerCurrent B) :=
    (Finset.univ.filter fun i : RootBranchIndex ω =>
      currentDivergence (stateCurrent (rootBranchFrequency ω) (rootBranchState ω) i) = 0).image
        (stateCurrent (rootBranchFrequency ω) (rootBranchState ω))
  have hclosed : ∀ j ∈ S, currentDivergence j = 0 := by
    intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    exact (Finset.mem_filter.mp hi).2
  have hdisj : (↑S : Set (IntegerCurrent B)).PairwiseDisjoint fun j => j.support := by
    intro j hj j' hj' hne
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hj)
    obtain ⟨i', _, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hj')
    exact state_hdisjoint H.separated i i' (fun h => hne (by rw [h]))
  have hz : ∀ j ∈ S,
      0 ≤ branchZ β (rootBranchFrequency ω) (sourceAssignmentIntegerActivity rootActivity)
          (rootBranchState ω) j ∧
        branchZ β (rootBranchFrequency ω) (sourceAssignmentIntegerActivity rootActivity)
          (rootBranchState ω) j ≤
          Real.exp (-(sourceRenormalizedRate β rootRate *
            (currentEnergy j + currentLength j))) := by
    intro j _
    have h := branchZ_envelope H j
    rw [currentEnergy_eq_integerCurrentNormSq, currentLength_eq_currentSupport_card]
    exact h
  obtain ⟨θ, hθ, hsum⟩ := relative_filling_wilson_bound S hclosed hdisj m N hmin hBmax
    (sourceRenormalizedRate β rootRate) ha
    (branchZ β (rootBranchFrequency ω) (sourceAssignmentIntegerActivity rootActivity)
      (rootBranchState ω)) hz tau
    (controlledOrientedDualFieldOnPlaquettes (-ε))
    (orientedSheetOnPlaquettes fun f => -sheet f) hdecomp
  refine ⟨fun i => θ (stateCurrent (rootBranchFrequency ω) (rootBranchState ω) i), ?_, ?_⟩
  · intro i hi
    have hcl : currentDivergence
        (stateCurrent (rootBranchFrequency ω) (rootBranchState ω) i) = 0 := by
      by_contra hne
      exact hi (branchAmplitude_of_not_closed _ _ _ _ hne)
    have hmem : stateCurrent (rootBranchFrequency ω) (rootBranchState ω) i ∈ S :=
      Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hcl⟩, rfl⟩
    rw [sourcePhysicalTheta_eq_sourceCurrentPhase]
    exact hθ _ hmem
  · have hsumEq : (∑ i, SourceJensen.sourceJensenGamma
          (branchAmp β (rootBranchFrequency ω) (sourceAssignmentIntegerActivity rootActivity)
            (rootBranchState ω) i) *
          θ (stateCurrent (rootBranchFrequency ω) (rootBranchState ω) i) ^ 2) =
        ∑ j ∈ S, jensenGamma
          (branchZ β (rootBranchFrequency ω) (sourceAssignmentIntegerActivity rootActivity)
            (rootBranchState ω) j) * θ j ^ 2 := by
      rw [Finset.sum_image (fun i _ i' _ h => stateCurrent_injective H.separated H.valid h),
        Finset.sum_filter]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [branchZ_stateCurrent H, sourceJensenGamma_eq_jensenGamma]
      by_cases hdiv : currentDivergence
          (stateCurrent (rootBranchFrequency ω) (rootBranchState ω) i) = 0
      · simp [hdiv]
      · have h0 : branchAmp β (rootBranchFrequency ω)
            (sourceAssignmentIntegerActivity rootActivity) (rootBranchState ω) i = 0 :=
          branchAmplitude_of_not_closed _ _ _ _ hdiv
        simp [hdiv, h0, jensenGamma]
    rw [hsumEq]
    refine hsum.trans (le_of_eq ?_)
    rw [sum_controlledOrientedDualField_sq]
    have hnorm : (∑ f : SourceDualTwoCells B, (ε f) ^ 2) = ‖ε‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      refine Finset.sum_congr rfl fun f _ => ?_
      rw [Real.norm_eq_abs, sq_abs]
    simp only [Pi.neg_apply, neg_sq]
    rw [hnorm]

/-! ### The sheet of the cube -/

/-- An integer dual two-form, as a dual chain, is supported on dual two-cells. -/
theorem sourceIntegerDualTwoChain_homogeneousSupport (q : SourceIntegerDualTwoField B) :
    dualIntegerHomogeneousSupport (sourceIntegerDualTwoChain q) 2 := by
  rw [dualIntegerHomogeneousSupport_iff]
  intro c hc
  have hc' : c ∈ (Finsupp.embDomain sourceDualTwoEmbedding q).support := hc
  rw [Finsupp.support_embDomain] at hc'
  obtain ⟨f, _, rfl⟩ := Finset.mem_map.mp hc'
  exact f.2

/-- The primal sheet of the `L × T` loop is a chain of plaquettes. -/
theorem cubePrimalSheet_homogeneousSupport (L T N : ℕ) :
    Cubical.homogeneousSupport (cubePrimalSheet L T N) 2 :=
  integerStarMapInverse_homogeneousSupport _ 2
    (sourceIntegerDualTwoChain_homogeneousSupport (sourceIntegerCubeSheet L T N))

/-- The squared norm of an integer dual two-form as a dual chain is the Euclidean one. -/
theorem integerDualNormSq_sourceIntegerDualTwoChain (q : SourceIntegerDualTwoField B) :
    integerDualNormSq (sourceIntegerDualTwoChain q) =
      ‖finsuppToEuclidean (castIntegerFinsupp q)‖ ^ 2 := by
  classical
  unfold integerDualNormSq integerDualPairing
  have hval : ∀ f : SourceDualTwoCells B, sourceIntegerDualTwoChain q f.1 = q f := by
    intro f
    change Finsupp.embDomain sourceDualTwoEmbedding q (sourceDualTwoEmbedding f) = q f
    exact Finsupp.embDomain_apply_self _ _ _
  have hx0 : ∀ c : Cubical.DualCell 4 B, Cubical.dualCellDegree c ≠ 2 →
      sourceIntegerDualTwoChain q c = 0 := by
    intro c hc
    by_contra hne
    exact hc ((dualIntegerHomogeneousSupport_iff _ 2).mp
      (sourceIntegerDualTwoChain_homogeneousSupport q) c (Finsupp.mem_support_iff.mpr hne))
  rw [← Finset.sum_subset (Finset.subset_univ
      (Finset.univ.filter fun c : Cubical.DualCell 4 B => Cubical.dualCellDegree c = 2))
    (fun c _ hc => by
      have hdeg : Cubical.dualCellDegree c ≠ 2 := fun h =>
        hc (Finset.mem_filter.mpr ⟨Finset.mem_univ c, h⟩)
      rw [hx0 c hdeg]
      simp)]
  rw [Finset.sum_subtype (p := fun c : Cubical.DualCell 4 B => Cubical.dualCellDegree c = 2)
    (Finset.univ.filter fun c : Cubical.DualCell 4 B => Cubical.dualCellDegree c = 2)
    (fun c => by simp)
    (fun c => ((sourceIntegerDualTwoChain q c : ℤ) : ℝ) * ((sourceIntegerDualTwoChain q c : ℤ) : ℝ)),
    EuclideanSpace.norm_sq_eq]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [hval f, Real.norm_eq_abs, sq_abs, finsuppToEuclidean_apply]
  simp [castIntegerFinsupp, pow_two]


theorem primalWilsonExpectation_cube_eq_sourceDualMoment {β : ℝ} (hβ : 0 < β) (L T N : ℕ) :
    primalWilsonExpectation β (cubePrimalSheet L T N) =
      ((Real.exp (-‖cubeSheet L T N‖ ^ 2 / (2 * β)) *
        sourceDualMoment β (sheetTest (cubeSheet L T N)) (-1 / β) : ℝ) : ℂ) := by
  rw [primalWilsonExpectation_eq_sourceDiscreteDualMoment β hβ (cubePrimalSheet L T N)
      (cubePrimalSheet_homogeneousSupport L T N), cubePrimalSheet_star,
    sourceDiscreteDualExpectation_eq_sourceDualMoment hβ,
    integerDualNormSq_sourceIntegerDualTwoChain, sourceIntegerCubeSheet_cast_eq_cubeSheet]
  push_cast
  ring

/-! ### The constants -/

/-- The threshold of the perimeter law: `β₀ = 216 (22 + β₁)`, so that the renormalized rate is at
least `11`. -/
def wilsonBetaThreshold : ℝ := 216 * (22 + rootRate)

/-- The perimeter constant `d_β = 6/(2β) + 486 c'_pack(a) + 40π²/a²`, `a = (β/216 − β₁)/2`. -/
def wilsonPerimeterConstant (β : ℝ) : ℝ :=
  6 / (2 * β) +
    486 * sourceComponentCpackPrime (sourceRenormalizedRate β rootRate) relativeFillingConstant +
    40 * Real.pi ^ 2 / (sourceRenormalizedRate β rootRate) ^ 2

theorem wilsonBetaThreshold_pos : 0 < wilsonBetaThreshold := by
  unfold wilsonBetaThreshold
  have := rootRate_nonneg
  positivity

theorem rootBetaThreshold_le_wilsonBetaThreshold : rootBetaThreshold ≤ wilsonBetaThreshold := by
  unfold rootBetaThreshold wilsonBetaThreshold
  linarith

theorem wilsonRate_ge_eleven {β : ℝ} (hβ : wilsonBetaThreshold ≤ β) :
    11 ≤ sourceRenormalizedRate β rootRate := by
  unfold wilsonBetaThreshold at hβ
  unfold sourceRenormalizedRate
  linarith

theorem wilsonPerimeterConstant_nonneg {β : ℝ} (hβ : wilsonBetaThreshold ≤ β) :
    0 ≤ wilsonPerimeterConstant β := by
  have hβpos : 0 < β := lt_of_lt_of_le wilsonBetaThreshold_pos hβ
  have ha : 0 < sourceRenormalizedRate β rootRate := by
    linarith [wilsonRate_ge_eleven hβ]
  have hc := sourceComponentCpackPrime_nonneg (sourceRenormalizedRate β rootRate)
    relativeFillingConstant ha
  unfold wilsonPerimeterConstant
  positivity

/-- On the cube of side `2N` the long-component term is at most `4` once the rate is at least
`11`. -/
theorem cube_longTerm_le {a : ℝ} (ha : 11 ≤ a) (N : ℕ) :
    ((4 * (2 * N + 1) ^ 4 : ℕ) : ℝ) * Real.exp (-((a - 7) * ((2 * N : ℕ) : ℝ))) ≤ 4 := by
  have hx : (0 : ℝ) ≤ ((2 * N : ℕ) : ℝ) := Nat.cast_nonneg _
  have h1 : ((2 * N : ℕ) : ℝ) + 1 ≤ Real.exp ((2 * N : ℕ) : ℝ) := Real.add_one_le_exp _
  have h4 : (((2 * N : ℕ) : ℝ) + 1) ^ 4 ≤ Real.exp (4 * ((2 * N : ℕ) : ℝ)) := by
    calc (((2 * N : ℕ) : ℝ) + 1) ^ 4 ≤ Real.exp ((2 * N : ℕ) : ℝ) ^ 4 :=
          pow_le_pow_left₀ (by positivity) h1 4
      _ = Real.exp (4 * ((2 * N : ℕ) : ℝ)) := by
          rw [← Real.exp_nat_mul]
          norm_num
  have hexp : Real.exp (4 * ((2 * N : ℕ) : ℝ)) * Real.exp (-((a - 7) * ((2 * N : ℕ) : ℝ))) ≤ 1 := by
    rw [← Real.exp_add, ← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hcast : ((4 * (2 * N + 1) ^ 4 : ℕ) : ℝ) = 4 * (((2 * N : ℕ) : ℝ) + 1) ^ 4 := by
    push_cast
    ring
  rw [hcast]
  calc 4 * (((2 * N : ℕ) : ℝ) + 1) ^ 4 * Real.exp (-((a - 7) * ((2 * N : ℕ) : ℝ)))
      ≤ 4 * (Real.exp (4 * ((2 * N : ℕ) : ℝ)) * Real.exp (-((a - 7) * ((2 * N : ℕ) : ℝ)))) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right h4 (Real.exp_pos _).le) (by norm_num)
    _ ≤ 4 * 1 := mul_le_mul_of_nonneg_left hexp (by norm_num)
    _ = 4 := by norm_num

/-! ### The perimeter law -/

/-- The moment of the sheet test with the area factor is bounded below by the perimeter
exponential. -/
theorem cube_wilson_sourceDualMoment_lower {β : ℝ} (hβ : wilsonBetaThreshold ≤ β) {L T N : ℕ}
    (hL : 1 ≤ L) (hT : 1 ≤ T) (hN : max L T + 1 ≤ N) :
    Real.exp (-(wilsonPerimeterConstant β * ((L : ℝ) + T))) ≤
      Real.exp (-‖cubeSheet L T N‖ ^ 2 / (2 * β)) *
        sourceDualMoment β (sheetTest (cubeSheet L T N)) (-1 / β) := by
  have hroot : rootBetaThreshold ≤ β := rootBetaThreshold_le_wilsonBetaThreshold.trans hβ
  have hβpos : 0 < β := rootBeta_pos hroot
  have ha11 := wilsonRate_ge_eleven hβ
  set a := sourceRenormalizedRate β rootRate with ha
  have ha0 : 0 < a := by linarith
  set σ := cubeSheet L T N with hσ
  set C := sourceLatticeComplex (B := cube N) with hC
  set ε := loopFieldResidual C σ with hε
  set cp := sourceComponentCpackPrime a relativeFillingConstant with hcp
  have hcp0 : 0 ≤ cp := sourceComponentCpackPrime_nonneg a relativeFillingConstant ha0
  have hsheet : ∀ f : SourceDualTwoCells (cube N),
      ((sourceIntegerCubeSheet L T N f : ℤ) : ℝ) = σ f := by
    intro f
    have h := congrArg (fun y : EuclideanSpace ℝ (SourceDualTwoCells (cube N)) => y.ofLp f)
      (sourceIntegerCubeSheet_cast_eq_cubeSheet L T N)
    simpa [castIntegerFinsupp, finsuppToEuclidean_apply] using h
  set E := 81 * cp * ‖ε‖ ^ 2 +
    (20 * Real.pi ^ 2 / a ^ 2) * ((4 * (2 * N + 1) ^ 4 : ℕ) : ℝ) *
      Real.exp (-((a - 7) * ((2 * N : ℕ) : ℝ))) with hE
  have hJ := sourceDualMoment_lower_of_phaseRepresentatives (B := cube N) hroot (sheetTest σ)
    (-1 / β) E (fun ω => rootBranch_wilsonPhases hroot (by linarith) (2 * N) (2 * N)
      (fun _ => le_rfl) (fun _ => le_rfl) σ (fun f => sourceIntegerCubeSheet L T N f) hsheet ω)
  have hQ : quotientCovarianceQuadratic C (sheetTest σ) = ‖σ‖ ^ 2 - ‖ε‖ ^ 2 := by
    have h1 : quotientCovarianceQuadratic C (sheetTest σ) =
        inner ℝ (C.d₁.adjoint σ) (wilsonGaussianShift C σ) := rfl
    rw [h1, wilsonGaussianShift_hodge_pairing, wilsonGaussianShift_norm_decomposition C σ]
    ring
  have hεle : ‖ε‖ ^ 2 ≤ 6 * ((L : ℝ) + T) := cube_loopField_normSq_le hN
  have hlong : (20 * Real.pi ^ 2 / a ^ 2) * ((4 * (2 * N + 1) ^ 4 : ℕ) : ℝ) *
      Real.exp (-((a - 7) * ((2 * N : ℕ) : ℝ))) ≤ 80 * Real.pi ^ 2 / a ^ 2 := by
    have h := cube_longTerm_le ha11 N
    have hcoef : 0 ≤ 20 * Real.pi ^ 2 / a ^ 2 := by positivity
    calc (20 * Real.pi ^ 2 / a ^ 2) * ((4 * (2 * N + 1) ^ 4 : ℕ) : ℝ) *
          Real.exp (-((a - 7) * ((2 * N : ℕ) : ℝ)))
        = (20 * Real.pi ^ 2 / a ^ 2) * (((4 * (2 * N + 1) ^ 4 : ℕ) : ℝ) *
          Real.exp (-((a - 7) * ((2 * N : ℕ) : ℝ)))) := by ring
      _ ≤ (20 * Real.pi ^ 2 / a ^ 2) * 4 := mul_le_mul_of_nonneg_left h hcoef
      _ = 80 * Real.pi ^ 2 / a ^ 2 := by ring
  have hLT : (2 : ℝ) ≤ (L : ℝ) + T := by
    have h1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
    have h2 : (1 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT
    linarith
  have hEle : ‖ε‖ ^ 2 / (2 * β) + E ≤ wilsonPerimeterConstant β * ((L : ℝ) + T) := by
    have h1 : ‖ε‖ ^ 2 / (2 * β) ≤ 6 / (2 * β) * ((L : ℝ) + T) := by
      rw [div_mul_eq_mul_div]
      exact div_le_div_of_nonneg_right hεle (by positivity)
    have h2 : 81 * cp * ‖ε‖ ^ 2 ≤ 486 * cp * ((L : ℝ) + T) := by nlinarith
    have h3 : 80 * Real.pi ^ 2 / a ^ 2 ≤ 40 * Real.pi ^ 2 / a ^ 2 * ((L : ℝ) + T) := by
      have hpos : 0 ≤ 40 * Real.pi ^ 2 / a ^ 2 := by positivity
      calc 80 * Real.pi ^ 2 / a ^ 2 = 40 * Real.pi ^ 2 / a ^ 2 * 2 := by ring
        _ ≤ 40 * Real.pi ^ 2 / a ^ 2 * ((L : ℝ) + T) := mul_le_mul_of_nonneg_left hLT hpos
    unfold wilsonPerimeterConstant
    rw [← ha, ← hcp]
    linarith
  have hexp : Real.exp (-‖σ‖ ^ 2 / (2 * β)) *
      (Real.exp (((-1 / β) ^ 2 * β / 2) * quotientCovarianceQuadratic C (sheetTest σ)) *
        Real.exp (-E)) = Real.exp (-(‖ε‖ ^ 2 / (2 * β) + E)) := by
    rw [← Real.exp_add, ← Real.exp_add, hQ]
    congr 1
    field_simp
    ring
  calc Real.exp (-(wilsonPerimeterConstant β * ((L : ℝ) + T)))
      ≤ Real.exp (-(‖ε‖ ^ 2 / (2 * β) + E)) := Real.exp_le_exp.mpr (neg_le_neg hEle)
    _ = Real.exp (-‖σ‖ ^ 2 / (2 * β)) *
        (Real.exp (((-1 / β) ^ 2 * β / 2) * quotientCovarianceQuadratic C (sheetTest σ)) *
          Real.exp (-E)) := hexp.symm
    _ ≤ Real.exp (-‖σ‖ ^ 2 / (2 * β)) * sourceDualMoment β (sheetTest σ) (-1 / β) :=
        mul_le_mul_of_nonneg_left hJ (Real.exp_pos _).le

/-- **FS82 (2.8) in finite volume, on cubes, with explicit constants.** For
`β ≥ 216 (22 + β₁)`, all `L, T ≥ 1` and every cube of half-side `N ≥ max(L,T) + 1`, the primal
Villain Wilson expectation of the `L × T` loop is real and at least `exp(−d_β (L + T))`. -/
theorem fs82_wilson_perimeter_cube {β : ℝ} (hβ : wilsonBetaThreshold ≤ β) {L T N : ℕ}
    (hL : 1 ≤ L) (hT : 1 ≤ T) (hN : max L T + 1 ≤ N) :
    ∃ w : ℝ, primalWilsonExpectation β (cubePrimalSheet L T N) = (w : ℂ) ∧
      Real.exp (-(wilsonPerimeterConstant β * ((L : ℝ) + T))) ≤ w :=
  ⟨_, primalWilsonExpectation_cube_eq_sourceDualMoment
      (lt_of_lt_of_le wilsonBetaThreshold_pos hβ) L T N,
    cube_wilson_sourceDualMoment_lower hβ hL hT hN⟩

/--
**The finite-volume perimeter root (2.8) on cubes.** There is `β₀ > 0` such that for every
`β ≥ β₀` there is `d_β ≥ 0` with

`exp(−d_β (L + T)) ≤ ⟨W(ℒ_{L×T})⟩_{β, cube N}`

for all `L, T ≥ 1` and all `N ≥ max(L,T) + 1`.
-/
theorem fs82_wilson_perimeter_root :
    ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ β : ℝ, β₀ ≤ β → ∃ d : ℝ, 0 ≤ d ∧
      ∀ L T : ℕ, 1 ≤ L → 1 ≤ T → ∀ N : ℕ, max L T + 1 ≤ N →
        ∃ w : ℝ, primalWilsonExpectation β (cubePrimalSheet L T N) = (w : ℂ) ∧
          Real.exp (-(d * ((L : ℝ) + T))) ≤ w :=
  ⟨wilsonBetaThreshold, wilsonBetaThreshold_pos, fun β hβ =>
    ⟨wilsonPerimeterConstant β, wilsonPerimeterConstant_nonneg hβ, fun _ _ hL hT _ hN =>
      fs82_wilson_perimeter_cube hβ hL hT hN⟩⟩

/-- The perimeter root stated with the real part of the expectation. -/
theorem fs82_wilson_perimeter_root_re :
    ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ β : ℝ, β₀ ≤ β → ∃ d : ℝ, 0 ≤ d ∧
      ∀ L T : ℕ, 1 ≤ L → 1 ≤ T → ∀ N : ℕ, max L T + 1 ≤ N →
        (primalWilsonExpectation β (cubePrimalSheet L T N)).im = 0 ∧
          Real.exp (-(d * ((L : ℝ) + T))) ≤
            (primalWilsonExpectation β (cubePrimalSheet L T N)).re := by
  obtain ⟨β₀, hβ₀, h⟩ := fs82_wilson_perimeter_root
  refine ⟨β₀, hβ₀, fun β hβ => ?_⟩
  obtain ⟨d, hd, hd'⟩ := h β hβ
  refine ⟨d, hd, fun L T hL hT N hN => ?_⟩
  obtain ⟨w, hw, hle⟩ := hd' L T hL hT N hN
  rw [hw]
  exact ⟨Complex.ofReal_im w, by simpa using hle⟩

end

end FroehlichSpencer.FS82.Wilson

end
