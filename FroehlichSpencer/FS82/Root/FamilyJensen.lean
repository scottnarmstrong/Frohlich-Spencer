/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Root.BranchIntegralBridge
public import FroehlichSpencer.FS82.Root.ReducedLaw
public import FroehlichSpencer.FS82.Root.CosineJensen
public import FroehlichSpencer.FS82.Root.PlaquetteIndependence

/-!
# the lower bound (2.101) for a separated family on the gauge-averaged law

For a family of integer currents with pairwise disjoint, plaquette-separated and vertex-separated
supports, and one colour class of selected links per current, the real-tilted gauge-averaged
integral of the raw product `∏ (1 + K cos α(ϱ))` is at least

`exp(t²β/2 · ⟨τ, V_Λ τ⟩) · exp(−Σ γ(z) θ²) ·` (the zero-tilt integral),

where `z` is the one-link renormalized amplitude of the co-closed currents (zero on the others) and
`θ = ⟨ϱ, tβ V_Λ τ⟩`.

The proof transports the branch to the source quotient Gaussian
(`branch_bridge`), reads it in the chord coordinates of the adaptive tree that avoids the selected
links, and applies identity with Jensen (`adaptiveTree_family_jensen`).
-/

open MeasureTheory
open scoped BigOperators InnerProductSpace
open FroehlichSpencer.FS82.Gaussian.ConditionalGaussian
open FroehlichSpencer.FS82.Gaussian.RenormalizedFamily
open FroehlichSpencer.FS82.Gaussian
open FroehlichSpencer.FS82.Gaussian.GaugeAveraged
open FroehlichSpencer.FS82.Gaussian.SourceTreeChart
open FroehlichSpencer.FS82.Gaussian.TreeGaugeQuotient
open FroehlichSpencer.FS82.Currents
open FroehlichSpencer.FS82.Currents.AdaptiveTree
open FroehlichSpencer.FS82.Currents.SelectedLinkSelection
open FroehlichSpencer.FS82.Currents.SelectedCurrentLinks
open FroehlichSpencer.FS82.Currents.SourceLinkColoring
open FroehlichSpencer.FS82.Moment
open FroehlichSpencer.FS82.Moment.SourceCoercivity
open FroehlichSpencer.FS82.Moment.SourceConstructor
open FroehlichSpencer.FS82.Moment.SourceEnsembleConstructor
open FroehlichSpencer.FS82.Poisson
open FroehlichSpencer.FS82.Root.RenormalizedInterface

@[expose] public section

namespace FroehlichSpencer.FS82.Root.MomentComparisonAssembly

variable {B : Cubical.Box 4}


/-! ## Chord coordinates of a co-closed test -/

/-- A sum over all links splits into the chords and the tree edges of a rooted tree. -/
theorem sum_eq_sum_chords_add_tree
    (T : RootedTreeGauge (SourcePoissonVertex B) (SourcePoissonEdge B))
    (a : SourcePoissonEdge B → ℝ) :
    (∑ e, a e) = (∑ c : T.Chord, a c.1) +
      ∑ x : {x : SourcePoissonVertex B // x ≠ T.root}, a (T.treeEdge x) := by
  classical
  calc
    (∑ e, a e) = ∑ s : T.Chord ⊕ {x : SourcePoissonVertex B // x ≠ T.root},
        a ((RootedTreeGauge.edgeSplitEquiv T).symm s) :=
      (Equiv.sum_comp (RootedTreeGauge.edgeSplitEquiv T).symm a).symm
    _ = _ := by
      rw [Fintype.sum_sum_type]
      simp

/-- **Chord coordinates of a co-closed test.** On the source quotient, a co-closed test is the
chord pairing of its restriction to the chords with the chord coordinates of the class. -/
theorem testFunctional_eq_chartPairing
    (T : RootedTreeGauge (SourcePoissonVertex B) (SourcePoissonEdge B))
    (hT : T.edgeSource = (sourceRootedTree B).edgeSource ∧
      T.edgeTarget = (sourceRootedTree B).edgeTarget)
    (x : coClosed (sourceDualComplex B))
    (q : FiniteGaugeQuotient (sourceDualComplex B)) :
    sourceDualQuotientTestFunctional x q =
      chartPairing (fun c : T.Chord => (x : EuclideanSpace ℝ (SourceDualOneCells B)) c.1)
        (sourceGaussianQuotientChordEquiv T hT q) := by
  classical
  let y := sourceGaussianQuotientChordEquiv T hT q
  have hq : q = sourceDualQuotientMap (B := B)
      (sourceFunctionToEuclidean (extendChordsLinear T y)) := by
    have h1 : q = (sourceGaussianQuotientChordEquiv T hT).symm y :=
      (LinearEquiv.symm_apply_apply _ q).symm
    rw [h1]
    change sourceCurlQuotientToFiniteGauge ((sourceCurlQuotientChordEquiv T hT).symm y) = _
    rw [sourceCurlQuotientChordEquiv_symm_apply_mk, sourceCurlQuotientToFiniteGauge_mk]
    rfl
  have hval : sourceDualQuotientTestFunctional x q =
      inner ℝ (x : EuclideanSpace ℝ (SourceDualOneCells B))
        (sourceFunctionToEuclidean (extendChordsLinear T y)) := by
    conv_lhs => rw [hq]
    exact sourceDualQuotientTestFunctional_mk x _
  rw [hval, PiLp.inner_apply]
  simp only [Real.inner_apply]
  rw [sum_eq_sum_chords_add_tree T]
  have htree : ∀ v : {v : SourcePoissonVertex B // v ≠ T.root},
      (sourceFunctionToEuclidean (extendChordsLinear T y)) (T.treeEdge v) = 0 :=
    extendChordsLinear_mem_treeGauge T y
  have hchord : ∀ c : T.Chord,
      (sourceFunctionToEuclidean (extendChordsLinear T y)) c.1 = y c := by
    intro c
    change T.extendChord y c.1 = y c
    exact congrFun (RootedTreeGauge.restrict_extendChord T y) c
  simp only [htree, hchord, mul_zero, Finset.sum_const_zero, add_zero]
  rfl

/-! ## The twisted mode in source-star coordinates -/

/-- The source-star coordinates of the twisted lattice mode of a co-closed current are its
physical link coefficients. -/
theorem latticeToSource_closedMode_apply (J : IntegerCurrent B)
    (h : currentDivergence J = 0) (e : SourceDualOneCells B) :
    (latticeToSourceCoClosed Cubical.originZero (closedMode J) :
        EuclideanSpace ℝ (SourceDualOneCells B)) e = physicalLinkCoefficient J e := by
  rw [latticeToSourceCoClosed_coe, closedMode_of_closed J h,
    sourcePhysicalCurrentCoClosed_eq_two_pi_mode, sourceDualTLinear_apply]
  simp only [PiLp.smul_apply, smul_eq_mul, latticeIntegerModeVector_apply, latticePhysicalMode,
    Int.cast_mul, sourceDualT_cast_eq_orientationSign, physicalLinkCoefficient]
  have hs : dualCellOrientationSign e.1 ^ 2 = 1 := dualCellOrientationSign_sq e
  linear_combination (2 * Real.pi * (J e : ℝ)) * hs

theorem latticeToSource_closedMode_apply_of_not_closed (J : IntegerCurrent B)
    (h : currentDivergence J ≠ 0) (e : SourceDualOneCells B) :
    (latticeToSourceCoClosed Cubical.originZero (closedMode J) :
        EuclideanSpace ℝ (SourceDualOneCells B)) e = 0 := by
  rw [latticeToSourceCoClosed_coe]
  simp [closedMode, h]

/-- The translated phase of a co-closed current is the twisted test evaluated on the class of the
twisted translation. -/
theorem testFunctional_closedMode_translation (β t : ℝ) (τ : SourceW B)
    (J : IntegerCurrent B) (h : currentDivergence J = 0) :
    sourceDualQuotientTestFunctional (latticeToSourceCoClosed Cubical.originZero (closedMode J))
        (sourceDualQuotientMap (B := B)
          (sourceDualTLinear (sourceGaussianTranslation (B := B) β t τ))) =
      sourcePhysicalTheta β τ t J := by
  rw [sourceDualQuotientTestFunctional_mk, latticeToSourceCoClosed_coe,
    sourceDualTLinear_symmetric, sourceDualTLinear_apply_apply, closedMode_of_closed J h]
  rfl

/-! ## The raw branch integral and its renormalized amplitude -/

/-- The real-tilted gauge-averaged integral of a raw cosine product. -/
noncomputable def gaugeBranchIntegral {ι : Type*} [Fintype ι] (β : ℝ) (hβ : 0 ≤ β) (t : ℝ)
    (τ : SourceW B) (K : ι → ℝ) (J : ι → IntegerCurrent B) : ℂ :=
  ∫ α : EuclideanSpace ℝ (SourceDualOneCells B),
    Complex.exp ((t * inner ℝ (τ : EuclideanSpace ℝ (SourceDualOneCells B)) α : ℝ) : ℂ) *
      ((∏ i, (1 + K i * Real.cos (inner ℝ
        ((2 * Real.pi) • latticeIntegerModeVector (B := B) (J i)) α)) : ℝ) : ℂ)
    ∂gaugeAveragedRealGaussian (B := B) β hβ

/-- The one-link renormalized amplitude of a current with selected colour class `c`: the
activity times the conditional Gaussian attenuation on the selected links, and zero when the
current is not co-closed. -/
noncomputable def branchAmplitude (β K : ℝ) (J : IntegerCurrent B) (c : Fin 8) : ℝ :=
  closedActivity K J * Real.exp (-((β / 2) *
    ∑ e ∈ colorClass J.support linkColor c,
      physicalLinkCoefficient J e ^ 2 / (incidentPlaquetteCount e : ℝ)))

theorem branchAmplitude_nonneg (β K : ℝ) (hK : 0 ≤ K) (J : IntegerCurrent B) (c : Fin 8) :
    0 ≤ branchAmplitude β K J c := by
  unfold branchAmplitude closedActivity
  split_ifs <;> positivity

theorem branchAmplitude_of_not_closed (β K : ℝ) (J : IntegerCurrent B) (c : Fin 8)
    (h : currentDivergence J ≠ 0) : branchAmplitude β K J c = 0 := by
  simp [branchAmplitude, closedActivity_of_not_closed K J h]

/-! ## The selected links, the adaptive tree and the reduced law of a family -/

section Family

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (J : ι → IntegerCurrent B) (c : ι → Fin 8)

/-- The selected links of one current: its support links of colour `c i`. -/
noncomputable def familyBlockLinks (i : ι) : Finset (SourceDualOneCells B) :=
  colorClass (J i).support linkColor (c i)

/-- All selected links of the family. -/
noncomputable def familySelected : Finset (SourceDualOneCells B) :=
  Finset.univ.biUnion (familyBlockLinks J c)

omit [Fintype ι] [DecidableEq ι] in
theorem familyBlockLinks_subset_support (i : ι) :
    familyBlockLinks J c i ⊆ (J i).support := Finset.filter_subset _ _

omit [DecidableEq ι] in
theorem familyBlockLinks_subset_selected (i : ι) :
    familyBlockLinks J c i ⊆ familySelected J c := fun _ he =>
  Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, he⟩

/-- The selected links of a plaquette-separated family are plaquette independent: within one
current by the colouring, across currents by the separation. -/
theorem familySelected_plaquetteIndependent
    (hplaq : ∀ i j, i ≠ j → ∀ e ∈ (J i).support, ∀ f ∈ (J j).support,
      ¬ ∃ p : SourceDualTwoCells B, linkIncidentPlaquette e p ∧ linkIncidentPlaquette f p) :
    PlaquetteIndependent (familySelected J c) := by
  rw [plaquetteIndependent_iff]
  intro e he f hf hne
  obtain ⟨i, -, hei⟩ := Finset.mem_biUnion.mp he
  obtain ⟨j, -, hfj⟩ := Finset.mem_biUnion.mp hf
  by_cases hij : i = j
  · subst hij
    exact (plaquetteIndependent_iff _).mp
      (plaquetteIndependent_colorClass (J i).support (c i)) e hei f hfj hne
  · exact hplaq i j hij e (familyBlockLinks_subset_support J c i hei) f
      (familyBlockLinks_subset_support J c j hfj)

variable (hsel : PlaquetteIndependent (familySelected J c))

/-- The adaptive tree avoiding the selected links of the family. -/
noncomputable abbrev familyTree := renormalizedAdaptiveTree (familySelected J c) hsel

/-- The source curl matrix in the chords of the family tree. -/
noncomputable abbrev familyCurl := renormalizedAdaptiveCurlMatrix (familySelected J c) hsel

/-- The selected chords of one current. -/
noncomputable def familyBlock (i : ι) : Finset (familyTree J c hsel).Chord :=
  Finset.univ.filter fun b : (familyTree J c hsel).Chord => b.1 ∈ familyBlockLinks J c i

/-- All selected chords. -/
noncomputable def familyBsel : Finset (familyTree J c hsel).Chord :=
  Finset.univ.filter fun b : (familyTree J c hsel).Chord => b.1 ∈ familySelected J c

/-- The chord coordinates of the twisted co-closed mode of one current (zero when the current is
not co-closed). -/
noncomputable def familyRho (i : ι) : (familyTree J c hsel).Chord → ℝ := fun b =>
  (latticeToSourceCoClosed Cubical.originZero (closedMode (J i)) :
    EuclideanSpace ℝ (SourceDualOneCells B)) b.1

/-- The retained chord coordinates of the family. -/
abbrev FamilyRetained :=
  {b : (familyTree J c hsel).Chord // b ∉ familyBsel J c hsel} → ℝ

/-- The reduced Gaussian of the family: the normalized retained marginal of the chart law after
integrating the selected chords. -/
noncomputable def familyReducedLaw (β : ℝ) : Measure (FamilyRetained J c hsel) :=
  normalizedMeasure (reducedMeasure β (familyCurl J c hsel) (familyBsel J c hsel))

/-- The renormalized angle of one current on the retained coordinates. -/
noncomputable def familyAngle (i : ι) : FamilyRetained J c hsel → ℝ :=
  renormalizedFunctional (familyCurl J c hsel) (familyBsel J c hsel) (familyRho J c hsel i)

omit [DecidableEq ι] in
theorem familyTree_treeEdge_notMem_selected
    (x : {x : SourcePoissonVertex B // x ≠ (familyTree J c hsel).root}) :
    (familyTree J c hsel).treeEdge x ∉ familySelected J c :=
  adaptiveRootedTree_avoids B (familySelected J c) hsel x

omit [DecidableEq ι] in
theorem family_hsep : ∀ p, ∀ b₁ ∈ familyBsel J c hsel, ∀ b₂ ∈ familyBsel J c hsel, b₁ ≠ b₂ →
    familyCurl J c hsel p b₁ = 0 ∨ familyCurl J c hsel p b₂ = 0 := by
  intro p b₁ hb₁ b₂ hb₂ hne
  by_contra hboth
  push Not at hboth
  have hinc₁ : linkIncidentPlaquette b₁.1 p := by
    by_contra h
    exact hboth.1 (sourceCurlCoefficient_eq_zero_of_not_incident p b₁.1 h)
  have hinc₂ : linkIncidentPlaquette b₂.1 p := by
    by_contra h
    exact hboth.2 (sourceCurlCoefficient_eq_zero_of_not_incident p b₂.1 h)
  exact (plaquetteIndependent_iff _).mp hsel
    b₁.1 (Finset.mem_filter.mp hb₁).2 b₂.1 (Finset.mem_filter.mp hb₂).2
    (fun h => hne (Subtype.ext h)) ⟨p, hinc₁, hinc₂⟩

omit [DecidableEq ι] in
theorem family_linkMass (b : (familyTree J c hsel).Chord) :
    linkMass (familyCurl J c hsel) b = (incidentPlaquetteCount b.1 : ℝ) :=
  sourceCurlCoefficient_sq_sum_eq_incidentPlaquetteCount b.1

omit [DecidableEq ι] in
theorem family_hn : ∀ b ∈ familyBsel J c hsel, 0 < linkMass (familyCurl J c hsel) b := by
  intro b _
  rw [family_linkMass]
  exact_mod_cast incidentPlaquetteCount_pos b.1

omit [DecidableEq ι] in
theorem family_hsub : ∀ i, familyBlock J c hsel i ⊆ familyBsel J c hsel := by
  intro i b hb
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    familyBlockLinks_subset_selected J c i (Finset.mem_filter.mp hb).2⟩

omit [DecidableEq ι] in
theorem family_hdisj (hdisjoint : ∀ i j, i ≠ j → Disjoint (J i).support (J j).support) :
    ∀ i j, i ≠ j → Disjoint (familyBlock J c hsel i) (familyBlock J c hsel j) := by
  intro i j hij
  refine Finset.disjoint_left.mpr fun b hbi hbj => ?_
  exact Finset.disjoint_left.mp (hdisjoint i j hij)
    (familyBlockLinks_subset_support J c i (Finset.mem_filter.mp hbi).2)
    (familyBlockLinks_subset_support J c j (Finset.mem_filter.mp hbj).2)

omit [DecidableEq ι] in
theorem family_hcover : ∀ b ∈ familyBsel J c hsel, ∃ i, b ∈ familyBlock J c hsel i := by
  intro b hb
  obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp (Finset.mem_filter.mp hb).2
  exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩

omit [DecidableEq ι] in
theorem familyRho_apply (i : ι) (b : (familyTree J c hsel).Chord) :
    familyRho J c hsel i b =
      if currentDivergence (J i) = 0 then physicalLinkCoefficient (J i) b.1 else 0 := by
  classical
  by_cases h : currentDivergence (J i) = 0
  · simp only [familyRho, h, ite_true]
    exact latticeToSource_closedMode_apply (J i) h b.1
  · simp only [familyRho, h, ite_false]
    exact latticeToSource_closedMode_apply_of_not_closed (J i) h b.1

omit [DecidableEq ι] in
theorem family_hcross (hdisjoint : ∀ i j, i ≠ j → Disjoint (J i).support (J j).support) :
    ∀ i j b, i ≠ j → b ∈ familyBlock J c hsel i → familyRho J c hsel j b = 0 := by
  intro i j b hij hb
  have hbi : b.1 ∈ (J i).support :=
    familyBlockLinks_subset_support J c i (Finset.mem_filter.mp hb).2
  have hbj : b.1 ∉ (J j).support := fun h =>
    Finset.disjoint_left.mp (hdisjoint i j hij) hbi h
  rw [familyRho_apply]
  split_ifs
  · simp [physicalLinkCoefficient, Finsupp.notMem_support_iff.mp hbj]
  · rfl

omit [DecidableEq ι] in
/--
The renormalized activity of the family is the branch amplitude.
-/
theorem family_renormalizedActivity (β : ℝ) (K : ι → ℝ) (i : ι) :
    renormalizedActivity β (closedActivity (K i) (J i)) (familyCurl J c hsel)
        (familyBlock J c hsel i) (familyRho J c hsel i) =
      branchAmplitude β (K i) (J i) (c i) := by
  classical
  by_cases h : currentDivergence (J i) = 0
  · have hsum : (∑ b ∈ familyBlock J c hsel i,
          familyRho J c hsel i b ^ 2 / linkMass (familyCurl J c hsel) b) =
        ∑ e ∈ familyBlockLinks J c i,
          physicalLinkCoefficient (J i) e ^ 2 / (incidentPlaquetteCount e : ℝ) := by
      let g : SourceDualOneCells B → ℝ := fun e =>
        if e ∈ familyBlockLinks J c i then
          physicalLinkCoefficient (J i) e ^ 2 / (incidentPlaquetteCount e : ℝ)
        else 0
      have hL : (∑ b ∈ familyBlock J c hsel i,
          familyRho J c hsel i b ^ 2 / linkMass (familyCurl J c hsel) b) =
          ∑ b : (familyTree J c hsel).Chord, g b.1 := by
        rw [familyBlock, Finset.sum_filter]
        refine Finset.sum_congr rfl fun b _ => ?_
        simp only [g, familyRho_apply, h, ite_true, family_linkMass]
      have hRsum : (∑ e ∈ familyBlockLinks J c i,
          physicalLinkCoefficient (J i) e ^ 2 / (incidentPlaquetteCount e : ℝ)) =
          ∑ e, g e := by
        simp only [g]
        rw [Finset.sum_ite_mem, Finset.univ_inter]
      rw [hL, hRsum, sum_eq_sum_chords_add_tree (familyTree J c hsel) g]
      have htree : ∀ x : {x : SourcePoissonVertex B // x ≠ (familyTree J c hsel).root},
          g ((familyTree J c hsel).treeEdge x) = 0 := by
        intro x
        have hx : (familyTree J c hsel).treeEdge x ∉ familyBlockLinks J c i := fun hmem =>
          familyTree_treeEdge_notMem_selected J c hsel x
            (familyBlockLinks_subset_selected J c i hmem)
        simp [g, hx]
      simp [htree]
    unfold renormalizedActivity branchAmplitude
    rw [hsum, neg_mul, closedActivity_of_closed _ _ h]
    rfl
  · rw [branchAmplitude_of_not_closed _ _ _ _ h]
    simp [renormalizedActivity, closedActivity_of_not_closed _ _ h]

omit [DecidableEq ι] in
/-- The tests of the family in the chord coordinates of the family tree. -/
theorem family_chart (i : ι) (q : FiniteGaugeQuotient (sourceDualComplex B)) :
    chartPairing (familyRho J c hsel i)
        (renormalizedAdaptiveChartMap (familySelected J c) hsel q) =
      sourceDualQuotientTestFunctional
        (latticeToSourceCoClosed Cubical.originZero (closedMode (J i))) q :=
  (testFunctional_eq_chartPairing (familyTree J c hsel)
    (adaptiveRootedTree_endpointMaps B (familySelected J c) hsel) _ q).symm

/-- The chord coordinates of the twisted translation `T(tβ V_Λ τ)`. -/
noncomputable def familyShift (β t : ℝ) (τ : SourceW B) : (familyTree J c hsel).Chord → ℝ :=
  renormalizedAdaptiveChartMap (familySelected J c) hsel
    (sourceDualQuotientMap (B := B)
      (sourceDualTLinear (sourceGaussianTranslation (B := B) β t τ)))

omit [DecidableEq ι] in
theorem family_phase (β t : ℝ) (τ : SourceW B) (i : ι) (hi : currentDivergence (J i) = 0) :
    chartPairing (familyRho J c hsel i) (familyShift J c hsel β t τ) =
      sourcePhysicalTheta β τ t (J i) := by
  rw [familyShift, family_chart]
  exact testFunctional_closedMode_translation β t τ (J i) hi

/-- The reduced law of a family is a probability measure. -/
theorem familyReducedLaw_isProbability {β : ℝ} (hβ : 0 < β)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (J i).support (J j).support) :
    IsProbabilityMeasure (familyReducedLaw J c hsel β) :=
  adaptiveTree_reducedLaw_isProbability β hβ (familySelected J c) hsel
    (familyBsel J c hsel) (familyBlock J c hsel) (familyRho J c hsel)
    (family_hsep J c hsel) (family_hn J c hsel) (family_hsub J c hsel)
    (family_hdisj J c hsel hdisjoint) (family_hcover J c hsel)
    (family_hcross J c hsel hdisjoint)

omit [DecidableEq ι] in
theorem familyReducedLaw_map_neg (β : ℝ) :
    Measure.map (fun y : FamilyRetained J c hsel => -y) (familyReducedLaw J c hsel β) =
      familyReducedLaw J c hsel β :=
  normalizedReducedMeasure_map_neg β _ _

omit [DecidableEq ι] in
theorem familyAngle_neg (i : ι) (y : FamilyRetained J c hsel) :
    familyAngle J c hsel i (-y) = -familyAngle J c hsel i y :=
  renormalizedFunctional_neg _ _ _ y

omit [DecidableEq ι] in
theorem measurable_familyAngle (i : ι) : Measurable (familyAngle J c hsel i) :=
  measurable_renormalizedFunctional _ _ _

/-- **The reduced identity for a separated family (2.97)–(2.100).** The real-tilted
gauge-averaged integral of the raw product is the completed square times the integral, against
the reduced law, of the product of the renormalized factors with translated phases. -/
theorem family_reduced_identity {β : ℝ} (hβ : 0 < β) (τ : SourceW B) (K : ι → ℝ)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (J i).support (J j).support)
    (hvert : ∀ i j, i ≠ j → ∀ e ∈ (J i).support, ∀ f ∈ (J j).support,
      ¬ linksShareFiniteVertex e f) (t : ℝ) :
    (gaugeBranchIntegral β hβ.le t τ K J).re =
      Real.exp ((t ^ 2 * β / 2) *
          quotientCovarianceQuadratic (sourceLatticeComplex (B := B)) τ) *
        ∫ y, ∏ i, (1 + branchAmplitude β (K i) (J i) (c i) *
          Real.cos (familyAngle J c hsel i y + sourcePhysicalTheta β τ t (J i)))
          ∂familyReducedLaw J c hsel β := by
  classical
  have hVD : ∀ σ : ι → RenormalizedCharacters.Sign, (∃ i, σ i ≠ 0 ∧ currentDivergence (J i) ≠ 0) →
      currentDivergence (signedCurrent J σ) ≠ 0 := by
    rintro σ ⟨i, hi, hdiv⟩
    exact signedCurrent_divergence_ne_zero J hvert σ i hi hdiv
  unfold gaugeBranchIntegral
  rw [branch_bridge β hβ.le t τ K J hVD, ← Complex.ofReal_exp, ← Complex.ofReal_mul,
    Complex.ofReal_re]
  congr 1
  have hRenormalized := adaptiveTree_translateThenZeroTilt_familyIdentity β hβ (familySelected J c) hsel
    (familyBsel J c hsel) (familyBlock J c hsel) (familyRho J c hsel)
    (fun i => closedActivity (K i) (J i)) (familyShift J c hsel β t τ)
    (family_hsep J c hsel) (family_hn J c hsel) (family_hsub J c hsel)
    (family_hdisj J c hsel hdisjoint) (family_hcover J c hsel)
    (family_hcross J c hsel hdisjoint)
  have hL : (∫ q, ∏ i, (1 + closedActivity (K i) (J i) * Real.cos
        (sourceDualQuotientTestFunctional
            (latticeToSourceCoClosed Cubical.originZero (closedMode (J i))) q +
          sourcePhysicalTheta β τ t (J i)))
        ∂sourceDualQuotientGaussian (B := B) β hβ.le) =
      ∫ q, ∏ i, (1 + closedActivity (K i) (J i) * Real.cos
        (chartPairing (familyRho J c hsel i)
            (renormalizedAdaptiveChartMap (familySelected J c) hsel q) +
          chartPairing (familyRho J c hsel i) (familyShift J c hsel β t τ)))
        ∂sourceDualQuotientGaussian (B := B) β hβ.le := by
    refine integral_congr_ae (ae_of_all _ fun q => ?_)
    refine Finset.prod_congr rfl fun i _ => ?_
    by_cases hi : currentDivergence (J i) = 0
    · rw [family_chart, family_phase J c hsel β t τ i hi]
    · simp [closedActivity_of_not_closed _ _ hi]
  rw [hL, hRenormalized]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [family_renormalizedActivity]
  by_cases hi : currentDivergence (J i) = 0
  · rw [family_phase J c hsel β t τ i hi]
    rfl
  · simp [branchAmplitude_of_not_closed _ _ _ _ hi]

end Family

/-! ## The family estimate -/


end FroehlichSpencer.FS82.Root.MomentComparisonAssembly

end
