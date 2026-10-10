/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Infinite.NonsummabilityPrimal

open Filter Topology MeasureTheory
open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Infinite.Fourier
open FroehlichSpencer.FS82.Infinite.Nonsummability
open FroehlichSpencer.FS82.Wilson
open FroehlichSpencer.FS82.Root
open FroehlichSpencer.FS82.Moment.Comparison

/-!
At coincident plaquettes the exact finite identity carries
the contact term from the logarithmic-derivative insertion.

This is the
finite-to-limit passage used for FS82 (2.11); the contact term is confined to
the diagonal and does not enter the nonsummability conclusion.
-/

@[expose] public section

namespace FroehlichSpencer.FS82.Infinite.Nonsummability

/-- Every pair of primal plaquettes in the `n`th Følner translate box is
contained in the finite cube of side parameter `N`. -/
def primalFølnerValidCube (N n : ℕ) (d : LatticePoint) : Prop :=
  ∀ a ∈ latticeShiftBox n,
    ∀ p ∈ spectralPairPlaquettes (latticeShiftPoint a) (d + latticeShiftPoint a),
      PlaquetteInCube N p

/-- The real part of the spatial average of the actual finite-volume primal
Villain field-strength correlations on `cube N`. The containment proof is
part of the domain, so every summand is an actual finite-volume observable. -/
noncomputable def primalActualPrimalFølnerCorrelation
    (N n : ℕ) (β : ℝ) (_hβ : 0 < β) (d : LatticePoint)
    (hvalid : primalFølnerValidCube N n d) : ℝ :=
  (Fintype.card {a : LatticeShift // a ∈ latticeShiftBox n} : ℝ)⁻¹ *
    ∑ a : {a : LatticeShift // a ∈ latticeShiftBox n},
      (primalFieldStrengthCorrelation β
        (primalPlaquetteOfGlobal N (spectralPlaquetteAt (latticeShiftPoint a.val))
          (hvalid a.val a.property
            (spectralPlaquetteAt (latticeShiftPoint a.val)) (by simp [spectralPairPlaquettes])))
        (primalPlaquetteOfGlobal N (spectralPlaquetteAt (d + latticeShiftPoint a.val))
          (hvalid a.val a.property
            (spectralPlaquetteAt (d + latticeShiftPoint a.val)) (by simp [spectralPairPlaquettes])))).re


theorem primalActualPrimalFølnerCorrelation_eq_cube
    (N n : ℕ) (β : ℝ) (hβ : 0 < β) (d : LatticePoint) (hd : d ≠ 0)
    (hvalid : primalFølnerValidCube N n d) :
    primalActualPrimalFølnerCorrelation N n β hβ d hvalid =
      primalFiniteCubeFølnerCorrelation N n β hβ d := by
  classical
  unfold primalActualPrimalFølnerCorrelation primalFiniteCubeFølnerCorrelation
  congr 1
  rw [← Finset.sum_coe_sort (s := latticeShiftBox n)
    (f := fun a => primalCubePrimalCorrelation N β hβ
      (latticeShiftPoint a) (d + latticeShiftPoint a))]
  apply Fintype.sum_congr
  intro a
  have hxy : latticeShiftPoint a.val ≠ d + latticeShiftPoint a.val := by
    intro heq
    apply hd
    have := congrArg (fun z : LatticePoint => z - latticeShiftPoint a.val) heq
    simpa using this.symm
  have hP : ∀ p ∈ spectralPairPlaquettes (latticeShiftPoint a.val)
      (d + latticeShiftPoint a.val), PlaquetteInCube N p := hvalid a.val a.property
  have h := primalCubePrimalCorrelation_eq_primalFieldStrength N β hβ
    (latticeShiftPoint a.val) (d + latticeShiftPoint a.val) hxy hP
  exact h.symm


private theorem primal_exists_primalFølnerCubeThreshold (n : ℕ) (d : LatticePoint) :
    ∃ N₀, ∀ N ≥ N₀, primalFølnerValidCube N n d := by
  classical
  let P : Finset GlobalIntegerPlaquette :=
    (latticeShiftBox n).biUnion fun a =>
      spectralPairPlaquettes (latticeShiftPoint a) (d + latticeShiftPoint a)
  obtain ⟨N₀, hN₀⟩ := exists_cube_threshold_for_plaquettes P
  refine ⟨N₀, ?_⟩
  intro N hN a ha p hp
  apply hN₀ N hN p
  exact Finset.mem_biUnion.mpr ⟨a, ha, hp⟩

/-- For fixed Følner size and nonzero displacement, the actual finite primal
correlation converges along a tail of the selected cube subsequence to the
first-stage cube-limit average. -/
theorem primalActualPrimalFølnerCorrelation_tendsto_firstStage
    {β : ℝ} (hβ : rootBetaThreshold ≤ β)
    (L : CubeCurvatureLimitState β (rootBeta_pos hβ))
    (n : ℕ) (d : LatticePoint) (hd : d ≠ 0) :
    ∃ j₀, ∃ hvalid : ∀ j,
      primalFølnerValidCube (L.subsequence (j₀ + j)) n d,
      Tendsto (fun j => primalActualPrimalFølnerCorrelation
        (L.subsequence (j₀ + j)) n β (rootBeta_pos hβ) d (hvalid j))
        atTop (𝓝 (primalFølnerPrimalCorrelation hβ L (fun k => k) n d)) := by
  obtain ⟨N₀, hN₀⟩ := primal_exists_primalFølnerCubeThreshold n d
  have hsubseqTop := Filter.tendsto_atTop.1
    L.strictMono_subsequence.tendsto_atTop N₀
  obtain ⟨j₀, hj₀⟩ := Filter.eventually_atTop.1 hsubseqTop
  have hvalid : ∀ j,
      primalFølnerValidCube (L.subsequence (j₀ + j)) n d := by
    intro j
    apply hN₀ (L.subsequence (j₀ + j))
    have hj : j₀ ≤ j₀ + j := by omega
    exact hj₀ (j₀ + j) hj
  refine ⟨j₀, hvalid, ?_⟩
  have hshift : Tendsto (fun j : ℕ => j₀ + j) atTop atTop := by
    apply Filter.tendsto_atTop.2
    intro b
    filter_upwards [Filter.eventually_ge_atTop b] with j hj
    omega
  have hcube := primalFiniteCubeFølnerCorrelation_tendsto hβ L n d hd
  have hcube' := hcube.comp hshift
  have heq : (fun j => primalActualPrimalFølnerCorrelation
      (L.subsequence (j₀ + j)) n β (rootBeta_pos hβ) d (hvalid j)) =
      fun j => primalFiniteCubeFølnerCorrelation
        (L.subsequence (j₀ + j)) n β (rootBeta_pos hβ) d := by
    funext j
    exact primalActualPrimalFølnerCorrelation_eq_cube
      (L.subsequence (j₀ + j)) n β (rootBeta_pos hβ) d hd (hvalid j)
  rw [heq]
  exact hcube'


/-- A finite exhausting family of lattice displacements, used to choose one
subsubsequence that works for every fixed off-diagonal pair. -/
noncomputable def primalFølnerDisplacementBox (k : ℕ) : Finset LatticePoint :=
  (Finset.range (k + 1)).image (fun j =>
    (Encodable.decode j).getD (0 : LatticePoint))

/-- Every fixed displacement belongs to all sufficiently large finite
exhaustion sets. -/
theorem primal_mem_FølnerDisplacementBox_eventually (d : LatticePoint) :
    ∀ k ≥ Encodable.encode d, d ∈ primalFølnerDisplacementBox k := by
  intro k hk
  apply Finset.mem_image.mpr
  refine ⟨Encodable.encode d, Finset.mem_range.mpr ?_, ?_⟩
  · omega
  · rw [Encodable.encodek]
    rfl

/--
Because only finitely many
displacements must be controlled at each stage, the cube index can be chosen
after both the first-stage and second-stage errors.
-/
theorem primal_selectedActualPrimalFølnerCorrelation_eventually_close
    {β : ℝ} (hβ : rootBetaThreshold ≤ β)
    (L : CubeCurvatureLimitState β (rootBeta_pos hβ))
    (s : ℕ → ℕ) (S : CurvatureCylinderState)
    (hpoint : ∀ P x, Tendsto
      (fun k => (averagedCylinderLaw (cubeStateToCylinderState L) (s k) P x).toReal)
      atTop (𝓝 ((S.law P x).toReal)))
    (hinv : ∀ a P, translateCylinderLaw S a P = S.law P) :
    ∃ m : ℕ → ℕ, StrictMono m ∧
      ∀ d : LatticePoint, d ≠ 0 → ∀ ε : ℝ, 0 < ε →
        ∃ k₀, ∀ k ≥ k₀,
          ∃ hvalid : primalFølnerValidCube (L.subsequence (m k)) (s k) d,
            dist (primalActualPrimalFølnerCorrelation
              (L.subsequence (m k)) (s k) β (rootBeta_pos hβ) d hvalid)
              (spectralFieldStrengthCorrelation S d) < ε := by
  classical
  have hfirst : ∀ k d (hd : d ≠ 0), ∃ j₀, ∃ hv : ∀ j,
      primalFølnerValidCube (L.subsequence (j₀ + j)) (s k) d,
      Tendsto (fun j => primalActualPrimalFølnerCorrelation
        (L.subsequence (j₀ + j)) (s k) β (rootBeta_pos hβ) d (hv j))
        atTop (𝓝 (primalFølnerPrimalCorrelation hβ L (fun j => j) (s k) d)) := by
    intro k d hd
    exact primalActualPrimalFølnerCorrelation_tendsto_firstStage hβ L (s k) d hd
  choose j₀ hv hconv using hfirst
  let B : ℕ → LatticePoint → ℝ := fun k d =>
    primalFølnerPrimalCorrelation hβ L (fun j => j) (s k) d
  have htol : ∀ k d (hd : d ≠ 0), ∃ q₀, ∀ q ≥ q₀,
      dist (primalActualPrimalFølnerCorrelation
        (L.subsequence (j₀ k d hd + q)) (s k) β (rootBeta_pos hβ) d
        (hv k d hd q)) (B k d) < 1 / (k + 1 : ℝ) := by
    intro k d hd
    have hε : 0 < (1 / (k + 1 : ℝ)) := by positivity
    have ht := Metric.tendsto_atTop.mp (hconv k d hd) (1 / (k + 1 : ℝ)) hε
    refine ⟨ht.choose, ?_⟩
    intro q hq
    have h := ht.choose_spec q hq
    simpa [B] using h
  choose q₀ hq₀ using htol
  let T : ℕ → LatticePoint → ℕ := fun k d =>
    if hd : d ≠ 0 then j₀ k d hd + q₀ k d hd else 0
  let M : ℕ → ℕ := fun k =>
    ∑ d ∈ primalFølnerDisplacementBox k, T k d
  let m : ℕ → ℕ := Nat.rec (M 0)
    (fun k prev => max (M (k + 1)) (prev + 1))
  have hM : ∀ k, M k ≤ m k := by
    intro k
    cases k with
    | zero => simp [m]
    | succ k => simp [m]
  have hm : StrictMono m := by
    apply strictMono_nat_of_lt_succ
    intro k
    cases k with
    | zero => simp [m]
    | succ k => simp [m]
  have hthreshold (k : ℕ) (d : LatticePoint) (hd : d ≠ 0)
      (hdk : d ∈ primalFølnerDisplacementBox k) :
      j₀ k d hd + q₀ k d hd ≤ m k := by
    have hsingle : T k d ≤ M k := by
      apply Finset.single_le_sum (s := primalFølnerDisplacementBox k)
        (f := T k)
      · intro x hx
        exact Nat.zero_le _
      · exact hdk
    have hT : T k d = j₀ k d hd + q₀ k d hd := by simp [T, hd]
    rw [← hT]
    exact le_trans hsingle (hM k)
  refine ⟨m, hm, ?_⟩
  intro d hd ε hε
  obtain ⟨kouter, houter⟩ := Metric.tendsto_atTop.mp
    (primalFølnerPrimalCorrelation_tendsto hβ L s S hpoint hinv d hd)
    (ε / 2) (by linarith)
  obtain ⟨ksmall, hsmall⟩ := Metric.tendsto_atTop.mp
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)) (ε / 2) (by linarith)
  let kbase := Encodable.encode d
  let k₀ := max kbase (max kouter ksmall)
  refine ⟨k₀, ?_⟩
  intro k hk
  have hdk : d ∈ primalFølnerDisplacementBox k :=
    primal_mem_FølnerDisplacementBox_eventually d k
      (le_trans (le_max_left _ _) hk)
  have hthreshold' := hthreshold k d hd hdk
  have hjq : j₀ k d hd ≤ m k := by omega
  let q : ℕ := m k - j₀ k d hd
  have hqge : q₀ k d hd ≤ q := by dsimp [q]; omega
  have hindex : j₀ k d hd + q = m k := by dsimp [q]; omega
  have hvalid : primalFølnerValidCube (L.subsequence (m k)) (s k) d := by
    have h := hv k d hd q
    rw [← hindex]
    exact h
  refine ⟨hvalid, ?_⟩
  have happrox := hq₀ k d hd q hqge
  have happrox' : dist
      (primalActualPrimalFølnerCorrelation
        (L.subsequence (m k)) (s k) β (rootBeta_pos hβ) d hvalid) (B k d) <
        1 / (k + 1 : ℝ) := by
    simpa [hindex, hvalid] using happrox
  have hmajor : max kouter ksmall ≤ k :=
    le_trans (le_max_right kbase (max kouter ksmall)) hk
  have hkouter : kouter ≤ k := le_trans (le_max_left kouter ksmall) hmajor
  have hksmall : ksmall ≤ k := le_trans (le_max_right kouter ksmall) hmajor
  have hsmallk := hsmall k hksmall
  have hkpos : 0 < (k : ℝ) + 1 := by positivity
  have hsmallk' : 1 / ((k : ℝ) + 1) < ε / 2 := by
    simpa [Real.dist_eq, abs_of_pos hkpos] using hsmallk
  have hA : dist
      (primalActualPrimalFølnerCorrelation
        (L.subsequence (m k)) (s k) β (rootBeta_pos hβ) d hvalid) (B k d) < ε / 2 :=
    lt_trans happrox' hsmallk'
  have hB : dist (B k d) (spectralFieldStrengthCorrelation S d) < ε / 2 := by
    simpa [B, primalFølnerPrimalCorrelation] using houter k hkouter
  calc
    dist (primalActualPrimalFølnerCorrelation
        (L.subsequence (m k)) (s k) β (rootBeta_pos hβ) d hvalid)
        (spectralFieldStrengthCorrelation S d) ≤
      dist (primalActualPrimalFølnerCorrelation
        (L.subsequence (m k)) (s k) β (rootBeta_pos hβ) d hvalid) (B k d) +
        dist (B k d) (spectralFieldStrengthCorrelation S d) := dist_triangle _ _ _
    _ < ε := by linarith


/-- The source off-diagonal primal correlations converge along actual finite
Villain volumes to the selected stationary state's dual-curvature
correlation, whose absolute spatial sum is not finite. The diagonal contact
identity is recorded separately because a single displacement cannot affect
this conclusion. -/
theorem primal_selectedPrimalFølnerLimit_not_absSummable
    {β : ℝ} (hβ : rootBetaThreshold ≤ β)
    (L : CubeCurvatureLimitState β (rootBeta_pos hβ))
    (s : ℕ → ℕ) (S : CurvatureCylinderState)
    (hpoint : ∀ P x, Tendsto
      (fun k => (averagedCylinderLaw (cubeStateToCylinderState L) (s k) P x).toReal)
      atTop (𝓝 ((S.law P x).toReal)))
    (hinv : ∀ a P, translateCylinderLaw S a P = S.law P)
    (hβlo : 0 < betaDoublePrime rootPackingCoefficient β) :
    (∃ m : ℕ → ℕ, StrictMono m ∧
      ∀ d : LatticePoint, d ≠ 0 → ∀ ε : ℝ, 0 < ε →
        ∃ k₀, ∀ k ≥ k₀,
          ∃ hvalid : primalFølnerValidCube (L.subsequence (m k)) (s k) d,
            dist (primalActualPrimalFølnerCorrelation
              (L.subsequence (m k)) (s k) β (rootBeta_pos hβ) d hvalid)
              (spectralFieldStrengthCorrelation S d) < ε) ∧
      ¬ Summable (fun d => |spectralFieldStrengthCorrelation S d|) := by
  constructor
  · exact primal_selectedActualPrimalFølnerCorrelation_eventually_close
      hβ L s S hpoint hinv
  · exact primal_selectedTwoStagePrimal_not_absSummable
      hβ L s S hpoint hinv hβlo

end FroehlichSpencer.FS82.Infinite.Nonsummability
