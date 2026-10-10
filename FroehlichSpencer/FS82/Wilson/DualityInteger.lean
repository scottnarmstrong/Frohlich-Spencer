/- Signed integer Hodge transport for the finite-volume Wilson loop. -/
module

public import FroehlichSpencer.FS82.Gaussian.IntegerExactness
public import FroehlichSpencer.FS82.Gaussian.IntegerGauge
public import FroehlichSpencer.FS82.Wilson.DualityFinite
public import FroehlichSpencer.FS82.Cubical.UnitBox
public import FroehlichSpencer.FS82.Wilson.CubeLoopField

/-!
# Integer dual plaquette fields for the Wilson loop

The cubical star is orientation-matched at the source level. The C2 cell
orientation character converts its coefficients to coordinate-oriented
lattice cells; on dual 2–3 plaquettes that character is `-1`.
-/

public section

namespace FroehlichSpencer.FS82.Wilson

open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Gaussian
open FroehlichSpencer.FS82.Infinite


abbrev SourceIntegerDualTwoField (B : SourceBox) := SourceDualTwoCells B →₀ ℤ


@[expose] noncomputable def sourceIntegerDualTwoChain {B : SourceBox}
    (q : SourceIntegerDualTwoField B) : DualIntegerChain B :=
  Finsupp.embDomain sourceDualTwoEmbedding q

@[expose] noncomputable def sourceIntegerDualOneChain {B : SourceBox}
    (q : SourceDualOneCells B →₀ ℤ) : DualIntegerChain B :=
  Finsupp.embDomain sourceDualOneEmbedding q

@[expose] def sourceIntegerClosedTwo {B : SourceBox}
    (q : SourceIntegerDualTwoField B) : Prop :=
  Cubical.boundary (integerStarMapInverse (sourceIntegerDualTwoChain q)) = 0

/-- Every closed integer dual plaquette field on the grounded finite dual box
is the exterior difference of a grounded integer link field. -/
theorem exists_sourceIntegerDualOneField_of_closedTwo {B : SourceBox}
    (q : SourceIntegerDualTwoField B) (hclosed : sourceIntegerClosedTwo q) :
    ∃ a : SourceDualOneCells B →₀ ℤ,
      integerDualExteriorDifference (sourceIntegerDualOneChain a) =
        sourceIntegerDualTwoChain q := by
  let qDual : DualIntegerChain B := sourceIntegerDualTwoChain q
  let p : Cubical.Chain 4 B := integerStarMapInverse qDual
  have hqSupport : (qDual.support : Set (Cubical.DualCell 4 B)) ⊆
      Set.range sourceDualTwoEmbedding := by
    intro c hc
    by_contra hnot
    have hzero : qDual c = 0 :=
      Finsupp.embDomain_of_notMem_range sourceDualTwoEmbedding q c hnot
    exact (Finsupp.mem_support_iff.mp hc) hzero
  have hpHomogeneous : Cubical.homogeneousSupport p 2 := by
    intro c hc
    have hdual : Cubical.primalDualCellEquiv c ∈ qDual.support := by
      simpa [p, integerStarMapInverse, Finsupp.equivMapDomain_apply] using hc
    obtain ⟨f, hf⟩ := hqSupport hdual
    have hdeg : Cubical.dualCellDegree (Cubical.primalDualCellEquiv c) = 2 := by
      calc
        Cubical.dualCellDegree (Cubical.primalDualCellEquiv c) =
            Cubical.dualCellDegree (sourceDualTwoEmbedding f) := by rw [hf]
        _ = 2 := f.2
    have hstar := Cubical.star_complementary_degree c
    rw [hdeg] at hstar
    omega
  have hpPositive : Cubical.positiveDegreeSupport p := by
    intro c hc
    rw [hpHomogeneous c hc]
    omega
  let anchor : Cubical.Anchor 4 B := fun i => ⟨0, Nat.zero_lt_succ _⟩
  have hprism := congrArg
      (fun T : Cubical.Chain 4 B →ₗ[ℤ] Cubical.Chain 4 B => T p)
      (Cubical.orderedPrism_identity anchor (List.finRange 4)
        (B := B))
  change Cubical.boundary
        (Cubical.orderedPrismFilling anchor (List.finRange 4) p) +
          Cubical.orderedPrismFilling anchor (List.finRange 4)
            (Cubical.boundary p) =
        p - Cubical.orderedPrismProjection anchor (List.finRange 4) p at hprism
  have hproj := Cubical.orderedPrismProjection_kills_positiveSupport
    anchor p hpPositive
  have hcycle : Cubical.boundary p = 0 := hclosed
  rw [hcycle, map_zero, hproj, sub_zero, add_zero] at hprism
  have hfill : Cubical.boundary (Cubical.fillingOperator anchor p) = p := by
    simpa [Cubical.fillingOperator] using hprism
  let fill : Cubical.Chain 4 B :=
    Cubical.fillingOperator anchor p
  have hfill' : Cubical.boundary fill = p := by
    simpa [fill] using hfill
  have hfillDegree : Cubical.homogeneousSupport fill 3 :=
    Cubical.fillingOperator_homogeneousSupport anchor p 2 hpHomogeneous
  let uDual : DualIntegerChain B := integerStarMap fill
  have huSupport : (uDual.support : Set (Cubical.DualCell 4 B)) ⊆
      Set.range sourceDualOneEmbedding := by
    intro c hc
    have hprimal : Cubical.primalDualCellEquiv.symm c ∈ fill.support := by
      simpa [uDual, integerStarMap, Finsupp.equivMapDomain_apply] using hc
    have hthree := hfillDegree (Cubical.primalDualCellEquiv.symm c) hprimal
    have hstar := Cubical.star_complementary_degree (Cubical.primalDualCellEquiv.symm c)
    rw [Cubical.primalDualCellEquiv.apply_symm_apply] at hstar
    rw [hthree] at hstar
    have hcdegree : Cubical.dualCellDegree c = 1 := by omega
    exact ⟨⟨c, hcdegree⟩, rfl⟩
  let a : SourceDualOneCells B →₀ ℤ :=
    Finsupp.comapDomain sourceDualOneEmbedding uDual
      sourceDualOneEmbedding.injective.injOn
  have haEmbed : sourceIntegerDualOneChain a = uDual := by
    dsimp [sourceIntegerDualOneChain, a]
    exact Finsupp.embDomain_comapDomain huSupport
  refine ⟨a, ?_⟩
  change integerStarMap
      (Cubical.boundary (integerStarMapInverse (sourceIntegerDualOneChain a))) = qDual
  rw [haEmbed, integerStarMapInverse_starMap, hfill']
  exact integerStarMap_starMapInverse qDual

@[expose] noncomputable def sourceIntegerDualTwoCompression {B : SourceBox}
    (q : DualIntegerChain B) : SourceIntegerDualTwoField B :=
  Finsupp.comapDomain sourceDualTwoEmbedding q
    sourceDualTwoEmbedding.injective.injOn

theorem sourceIntegerDualTwoChain_compression {B : SourceBox}
    (q : DualIntegerChain B)
    (hq : (q.support : Set (Cubical.DualCell 4 B)) ⊆
      Set.range sourceDualTwoEmbedding) :
    sourceIntegerDualTwoChain (sourceIntegerDualTwoCompression q) = q := by
  exact Finsupp.embDomain_comapDomain hq

theorem exists_sourceIntegerDualOneField_of_closedDualChain {B : SourceBox}
    (q : DualIntegerChain B)
    (hdegree : ∀ c ∈ q.support, Cubical.dualCellDegree c = 2)
    (hclosed : Cubical.boundary (integerStarMapInverse q) = 0) :
    ∃ a : SourceDualOneCells B →₀ ℤ,
      integerDualExteriorDifference (sourceIntegerDualOneChain a) = q := by
  have hqSupport : (q.support : Set (Cubical.DualCell 4 B)) ⊆
      Set.range sourceDualTwoEmbedding := by
    intro c hc
    exact ⟨⟨c, hdegree c hc⟩, rfl⟩
  let q₂ := sourceIntegerDualTwoCompression q
  have hEmbed : sourceIntegerDualTwoChain q₂ = q := by
    exact sourceIntegerDualTwoChain_compression q hqSupport
  have hclosed₂ : sourceIntegerClosedTwo q₂ := by
    unfold sourceIntegerClosedTwo
    rw [hEmbed]
    exact hclosed
  obtain ⟨a, ha⟩ := exists_sourceIntegerDualOneField_of_closedTwo q₂ hclosed₂
  refine ⟨a, ?_⟩
  rw [ha, hEmbed]

@[expose] noncomputable def sourceIntegerDualOneDifferential {B : SourceBox}
    (a : SourceDualOneCells B →₀ ℤ) : DualIntegerChain B :=
  integerDualExteriorDifference (sourceIntegerDualOneChain a)

theorem sourceIntegerDualOneChain_sub {B : SourceBox}
    (a b : SourceDualOneCells B →₀ ℤ) :
    sourceIntegerDualOneChain (a - b) =
      sourceIntegerDualOneChain a - sourceIntegerDualOneChain b := by
  change Finsupp.embDomain sourceDualOneEmbedding (a - b) = _
  rw [sub_eq_add_neg, Finsupp.embDomain_add]
  have hneg : Finsupp.embDomain sourceDualOneEmbedding (-b) =
      -Finsupp.embDomain sourceDualOneEmbedding b := by
    exact map_neg (Finsupp.embDomain.addMonoidHom sourceDualOneEmbedding) b
  rw [hneg]
  simp [sourceIntegerDualOneChain, sub_eq_add_neg]

/-- Potentials producing the same dual plaquette field differ by the source's
grounded integer gauge relation (2.26). -/
theorem sourceIntegerDualOneDifferential_eq_implies_gauge {B : SourceBox}
    (origin : Fin 4 → ℤ) (a b : SourceDualOneCells B →₀ ℤ)
    (hab : sourceIntegerDualOneDifferential a =
      sourceIntegerDualOneDifferential b) :
    sourceExactShiftSupportCondition226 origin (fun e => a e) (fun e => b e) := by
  have hclosed : sourceIntegerClosed (a - b) := by
    unfold sourceIntegerClosed
    have hd : integerDualExteriorDifference
        (sourceIntegerDualOneChain (a - b)) = 0 := by
      rw [sourceIntegerDualOneChain_sub, map_sub]
      change sourceIntegerDualOneDifferential a -
        sourceIntegerDualOneDifferential b = 0
      rw [hab]
      simp
    change integerStarMap
        (Cubical.boundary (integerStarMapInverse
          (sourceIntegerDualOneChain (a - b)))) = 0 at hd
    have hdinv := congrArg integerStarMapInverse hd
    change Cubical.boundary (integerStarMapInverse
      (FroehlichSpencer.FS82.Gaussian.sourceIntegerDualOneChain (a - b))) = 0
    simpa [integerStarMapInverse_starMap, map_zero,
      FroehlichSpencer.FS82.Wilson.sourceIntegerDualOneChain,
      FroehlichSpencer.FS82.Gaussian.sourceIntegerDualOneChain] using hdinv
  obtain ⟨γ, hγvertex, hγlink, hgrad⟩ :=
    sourceIntegerClosed_has_supported_latticePotential origin (a - b) hclosed
  refine ⟨γ, hγlink, ?_⟩
  intro e
  simpa [Finsupp.sub_apply] using (hgrad e).symm


@[expose] def cubeSheetCell {L T N : ℕ}
    (f : SourceDualTwoCells (cube N)) : Prop :=
  (∃ v, f.1 0 = Sum.inl v ∧ N ≤ v.val ∧ v.val < N + L) ∧
  (∃ v, f.1 1 = Sum.inl v ∧ N ≤ v.val ∧ v.val < N + T) ∧
  (∃ e, f.1 2 = Sum.inr e ∧ e.val = N) ∧
  (∃ e, f.1 3 = Sum.inr e ∧ e.val = N)

@[expose] noncomputable def sourceIntegerCubeSheet (L T N : ℕ) :
    SourceIntegerDualTwoField (cube N) := by
  classical
  exact Finsupp.equivFunOnFinite.symm (fun f : SourceDualTwoCells (cube N) =>
    if cubeSheetCell (L := L) (T := T) (N := N) f then (1 : ℤ) else 0)

theorem sourceIntegerCubeSheet_cast_eq_cubeSheet (L T N : ℕ) :
    finsuppToEuclidean
        (castIntegerFinsupp (sourceIntegerCubeSheet L T N)) =
      cubeSheet L T N := by
  classical
  ext f
  simp only [finsuppToEuclidean_apply, castIntegerFinsupp,
    Finsupp.mapRange_apply, sourceIntegerCubeSheet,
    Finsupp.equivFunOnFinite_symm_apply_apply]
  rw [cubeSheet_apply]
  split_ifs <;> simp_all [cubeSheetCell]

@[expose] noncomputable def cubePrimalSheet (L T N : ℕ) :
    Cubical.Chain 4 (cube N) :=
  integerStarMapInverse
    (sourceIntegerDualTwoChain (sourceIntegerCubeSheet L T N))

theorem cubePrimalSheet_star (L T N : ℕ) :
    integerStarMap (cubePrimalSheet L T N) =
      sourceIntegerDualTwoChain (sourceIntegerCubeSheet L T N) := by
  simp [cubePrimalSheet, integerStarMap_starMapInverse]


@[expose] noncomputable def integerDualPairing {B : SourceBox}
    (q r : DualIntegerChain B) : ℝ :=
  ∑ c : Cubical.DualCell 4 B, (q c : ℝ) * (r c : ℝ)

@[expose] noncomputable def integerDualNormSq {B : SourceBox}
    (q : DualIntegerChain B) : ℝ := integerDualPairing q q

theorem integerDualNormSq_add {B : SourceBox}
    (q r : DualIntegerChain B) :
    integerDualNormSq (q + r) = integerDualNormSq q +
      2 * integerDualPairing q r + integerDualNormSq r := by
  classical
  unfold integerDualNormSq integerDualPairing
  simp only [Finsupp.add_apply, Int.cast_add]
  calc
    (∑ c : Cubical.DualCell 4 B,
        ((q c : ℝ) + (r c : ℝ)) * ((q c : ℝ) + (r c : ℝ))) =
      ∑ c : Cubical.DualCell 4 B,
        ((q c : ℝ) * (q c : ℝ) +
          2 * ((q c : ℝ) * (r c : ℝ)) +
          (r c : ℝ) * (r c : ℝ)) := by
            apply Finset.sum_congr rfl
            intro c hc
            ring
    _ = (∑ c : Cubical.DualCell 4 B, (q c : ℝ) * (q c : ℝ)) +
        2 * (∑ c : Cubical.DualCell 4 B, (q c : ℝ) * (r c : ℝ)) +
        ∑ c : Cubical.DualCell 4 B, (r c : ℝ) * (r c : ℝ) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]

theorem integerDualGaussianShift_term {B : SourceBox} (β : ℝ)
    (sigma d : DualIntegerChain B) :
    Real.exp (-integerDualNormSq (d + sigma) / (2 * β)) =
      Real.exp (-integerDualNormSq sigma / (2 * β)) *
        Real.exp (-integerDualNormSq d / (2 * β)) *
          Real.exp (-integerDualPairing d sigma / β) := by
  rw [integerDualNormSq_add]
  rw [show -(integerDualNormSq d +
      2 * integerDualPairing d sigma + integerDualNormSq sigma) /
      (2 * β) =
      -integerDualNormSq sigma / (2 * β) +
        (-integerDualNormSq d / (2 * β)) +
          (-integerDualPairing d sigma / β) by ring]
  rw [Real.exp_add, Real.exp_add]

abbrev SourceIntegerDualGaugeClass (B : SourceBox) :=
  Set.range (fun a : SourceDualOneCells B →₀ ℤ =>
    sourceIntegerDualOneDifferential a)

@[expose] noncomputable def sourceDualGaugeClassWeight {B : SourceBox}
    (β : ℝ) (x : SourceIntegerDualGaugeClass B) : ℝ :=
  Real.exp (-integerDualNormSq x.1 / (2 * β))

@[expose] noncomputable def sourceDualGaugeClassObservable {B : SourceBox}
    (β : ℝ) (sigma : DualIntegerChain B)
    (x : SourceIntegerDualGaugeClass B) : ℝ :=
  Real.exp (-integerDualPairing x.1 sigma / β)

@[expose] noncomputable def sourceDualWilsonGaugeClassWeight {B : SourceBox}
    (β : ℝ) (sigma : DualIntegerChain B)
    (x : SourceIntegerDualGaugeClass B) : ℝ :=
  Real.exp (-integerDualNormSq (x.1 + sigma) / (2 * β))

theorem sourceDualWilsonGaugeClassWeight_eq_tilt {B : SourceBox}
    (β : ℝ) (sigma : DualIntegerChain B)
    (x : SourceIntegerDualGaugeClass B) :
    sourceDualWilsonGaugeClassWeight β sigma x =
      Real.exp (-integerDualNormSq sigma / (2 * β)) *
        (sourceDualGaugeClassWeight β x *
          sourceDualGaugeClassObservable β sigma x) := by
  simpa [sourceDualWilsonGaugeClassWeight, sourceDualGaugeClassWeight,
    sourceDualGaugeClassObservable, mul_assoc] using
      integerDualGaussianShift_term β sigma x.1


noncomputable def sourceDualGaugeClassPartition {B : SourceBox} (β : ℝ) : ℝ :=
  ∑' x : SourceIntegerDualGaugeClass B, sourceDualGaugeClassWeight β x

noncomputable def sourceDualGaugeClassTiltSum {B : SourceBox}
    (β : ℝ) (sigma : DualIntegerChain B) : ℝ :=
  ∑' x : SourceIntegerDualGaugeClass B,
    sourceDualGaugeClassWeight β x * sourceDualGaugeClassObservable β sigma x

noncomputable def sourceDualGaugeClassShiftPartition {B : SourceBox}
    (β : ℝ) (sigma : DualIntegerChain B) : ℝ :=
  ∑' x : SourceIntegerDualGaugeClass B,
    sourceDualWilsonGaugeClassWeight β sigma x

noncomputable def sourceDiscreteDualExpectation {B : SourceBox}
    (β : ℝ) (sigma : DualIntegerChain B) : ℝ :=
  sourceDualGaugeClassTiltSum (B := B) β sigma /
    sourceDualGaugeClassPartition (B := B) β

theorem sourceDualGaugeClassShiftPartition_eq_tilted {B : SourceBox}
    (β : ℝ) (_hβ : 0 < β) (sigma : DualIntegerChain B) :
    sourceDualGaugeClassShiftPartition β sigma =
      Real.exp (-integerDualNormSq sigma / (2 * β)) *
        sourceDualGaugeClassTiltSum β sigma := by
  unfold sourceDualGaugeClassShiftPartition sourceDualGaugeClassTiltSum
  rw [show (fun x : SourceIntegerDualGaugeClass B =>
      sourceDualWilsonGaugeClassWeight β sigma x) =
        (fun x => Real.exp (-integerDualNormSq sigma / (2 * β)) *
        (sourceDualGaugeClassWeight β x *
          sourceDualGaugeClassObservable β sigma x)) by
        funext x
        simpa [mul_assoc] using sourceDualWilsonGaugeClassWeight_eq_tilt β sigma x]
  rw [tsum_mul_left]

theorem integerBoundary_homogeneousSupport {B : SourceBox}
    (q : Cubical.Chain 4 B) (k : ℕ) (hk : 0 < k)
    (hq : Cubical.homogeneousSupport q k) :
    Cubical.homogeneousSupport (Cubical.boundary q) (k - 1) := by
  intro c hc
  have hqR : Cubical.realHomogeneousSupport
      (Cubical.castIntegerChain q) k := by
    intro x hx
    exact hq x (Finsupp.support_mapRange hx)
  have hbdR := Gaussian.realBoundary_homogeneousSupport
    (Cubical.castIntegerChain q) k hk hqR
  have hcast : Cubical.castIntegerChain (Cubical.boundary q) =
      Cubical.realBoundary (Cubical.castIntegerChain q) := by
    simpa [Cubical.realBoundary] using
      (Cubical.realifyLinearMap_cast Cubical.boundary q).symm
  have hcR : c ∈ (Cubical.realBoundary (Cubical.castIntegerChain q)).support := by
    rw [← hcast]
    rw [Finsupp.mem_support_iff] at hc ⊢
    intro hz
    apply hc
    have hzero : ((Cubical.boundary q c : ℤ) : ℝ) = 0 := by
      simpa [Cubical.castIntegerChain, Finsupp.mapRange_apply] using hz
    exact_mod_cast hzero
  exact hbdR c hcR

theorem plaquetteModeChain_homogeneousSupport {B : Box 4}
    (m : PrimalPlaquettes B → ℤ) :
    Cubical.homogeneousSupport (plaquetteModeChain m) 2 := by
  classical
  unfold plaquetteModeChain
  have hs : ∀ t : Finset (PrimalPlaquettes B),
      Cubical.homogeneousSupport
        (∑ p ∈ t, Finsupp.single p.1 (m p)) 2 := by
    intro t
    induction t using Finset.induction_on with
    | empty => simp [Cubical.homogeneousSupport]
    | @insert p t hp ih =>
        rw [Finset.sum_insert hp]
        apply Cubical.homogeneousSupport_add
        · have hsingle : Finsupp.single p.1 (m p) =
              (m p) • Cubical.basisChain p.1 := by
            ext c
            simp [Cubical.basisChain]
          rw [hsingle]
          have hbase : Cubical.homogeneousSupport
              (Cubical.basisChain p.1) 2 := by
            simpa [p.2] using Cubical.homogeneousSupport_basis p.1
          exact Cubical.homogeneousSupport_smul (m p)
            hbase
        · exact ih
  simpa using hs Finset.univ

theorem plaquetteModeChain_restrict {B : Box 4}
    (q : Cubical.Chain 4 B)
    (hq : Cubical.homogeneousSupport q 2) :
    plaquetteModeChain (fun p : PrimalPlaquettes B => q p.1) = q := by
  classical
  ext c
  by_cases hc : Cubical.cellDegree c = 2
  · let p : PrimalPlaquettes B := ⟨c, hc⟩
    unfold plaquetteModeChain
    rw [Finset.sum_apply']
    rw [Finset.sum_eq_single p]
    · simp [p]
    · intro b hb hne
      have hbc : b.1 ≠ c := by
        intro h
        apply hne
        exact Subtype.ext h
      simp [hbc]
    · simp [p]
  · have hqzero : q c = 0 := by
      by_contra hne
      have hcSupport : c ∈ q.support := Finsupp.mem_support_iff.mpr hne
      exact hc (hq c hcSupport)
    rw [hqzero]
    unfold plaquetteModeChain
    rw [Finset.sum_apply']
    apply Finset.sum_eq_zero
    intro p hp
    have hne : p.1 ≠ c := by
      intro h
      exact hc (h ▸ p.2)
    simp [hne]

theorem plaquetteModeDivergence_eq_boundary {B : Box 4}
    (m : PrimalPlaquettes B → ℤ) (S : Cubical.Chain 4 B)
    (hS : Cubical.homogeneousSupport S 2) :
    plaquetteModeDivergence m = primalSheetLoopFrequency S ↔
      Cubical.boundary (plaquetteModeChain m) = Cubical.boundary S := by
  have hmode := integerBoundary_homogeneousSupport
    (plaquetteModeChain m) 2 (by omega) (plaquetteModeChain_homogeneousSupport m)
  have hsheet := integerBoundary_homogeneousSupport S 2 (by omega) hS
  constructor
  · intro h
    ext c
    by_cases hc : Cubical.cellDegree c = 1
    · have hl := congrArg (fun f : PrimalLinks B → ℤ => f ⟨c, hc⟩) h
      simpa [plaquetteModeDivergence, primalSheetLoopFrequency] using hl
    · have hmodeZero : Cubical.boundary (plaquetteModeChain m) c = 0 := by
        by_contra hn
        exact hc (hmode c (Finsupp.mem_support_iff.mpr hn))
      have hsheetZero : Cubical.boundary S c = 0 := by
        by_contra hn
        exact hc (hsheet c (Finsupp.mem_support_iff.mpr hn))
      simp [hmodeZero, hsheetZero]
  · intro h
    funext l
    simpa [plaquetteModeDivergence, primalSheetLoopFrequency] using
      congrArg (fun q : Cubical.Chain 4 B => q l.1) h


def dualIntegerHomogeneousSupport {B : SourceBox}
    (q : DualIntegerChain B) (k : ℕ) : Prop :=
  ∀ c ∈ q.support, Cubical.dualCellDegree c = k

theorem integerStarMap_homogeneousSupport {B : SourceBox}
    (q : Cubical.Chain 4 B) (k : ℕ)
    (hq : Cubical.homogeneousSupport q k) :
    dualIntegerHomogeneousSupport (integerStarMap q) (4 - k) := by
  intro c hc
  have hp : Cubical.primalDualCellEquiv.symm c ∈ q.support := by
    simpa [integerStarMap, Finsupp.equivMapDomain_apply] using hc
  have hcomp := Cubical.star_complementary_degree
    (Cubical.primalDualCellEquiv.symm c)
  rw [Cubical.primalDualCellEquiv.apply_symm_apply] at hcomp
  rw [hq _ hp] at hcomp
  omega

theorem integerStarMapInverse_homogeneousSupport {B : SourceBox}
    (q : DualIntegerChain B) (k : ℕ)
    (hq : dualIntegerHomogeneousSupport q k) :
    Cubical.homogeneousSupport (integerStarMapInverse q) (4 - k) := by
  intro c hc
  have hdual : Cubical.primalDualCellEquiv c ∈ q.support := by
    simpa [integerStarMapInverse, Finsupp.equivMapDomain_apply] using hc
  have hcomp := Cubical.star_complementary_degree c
  rw [hq _ hdual] at hcomp
  omega

theorem sourceIntegerDualOneChain_homogeneousSupport {B : SourceBox}
    (a : SourceDualOneCells B →₀ ℤ) :
    ∀ c ∈ (sourceIntegerDualOneChain a).support,
      Cubical.dualCellDegree c = 1 := by
  intro c hc
  by_contra hdegree
  have hnot : c ∉ Set.range sourceDualOneEmbedding := by
    rintro ⟨e, rfl⟩
    exact hdegree e.2
  have hz := Finsupp.embDomain_of_notMem_range sourceDualOneEmbedding a c hnot
  exact (Finsupp.mem_support_iff.mp hc) hz

theorem integerDualExteriorDifference_homogeneousSupport_one {B : SourceBox}
    (q : DualIntegerChain B)
    (hq : ∀ c ∈ q.support, Cubical.dualCellDegree c = 1) :
    dualIntegerHomogeneousSupport (integerDualExteriorDifference q) 2 := by
  have hinv := integerStarMapInverse_homogeneousSupport q 1 hq
  have hboundary := integerBoundary_homogeneousSupport
    (integerStarMapInverse q) 3 (by omega) hinv
  have hstar := integerStarMap_homogeneousSupport
    (Cubical.boundary (integerStarMapInverse q)) 2 hboundary
  simpa [integerDualExteriorDifference, LinearMap.comp_apply] using hstar

theorem sourceIntegerDualOneDifferential_homogeneousSupport {B : SourceBox}
    (a : SourceDualOneCells B →₀ ℤ) :
    dualIntegerHomogeneousSupport (sourceIntegerDualOneDifferential a) 2 := by
  exact integerDualExteriorDifference_homogeneousSupport_one
    (sourceIntegerDualOneChain a) (sourceIntegerDualOneChain_homogeneousSupport a)

abbrev SourceWilsonModes {B : SourceBox} (S : Cubical.Chain 4 B) :=
  {m : PrimalPlaquettes B → ℤ //
    plaquetteModeDivergence m = primalSheetLoopFrequency S}

private theorem sourceGaugeClass_homogeneousSupport {B : SourceBox}
    (x : SourceIntegerDualGaugeClass B) :
    dualIntegerHomogeneousSupport x.1 2 := by
  obtain ⟨a, ha⟩ := x.2
  rw [← ha]
  exact sourceIntegerDualOneDifferential_homogeneousSupport a

private theorem integerDualModeSheet_boundary {B : SourceBox}
    (S : Cubical.Chain 4 B) (_hS : Cubical.homogeneousSupport S 2)
    (x : SourceIntegerDualGaugeClass B) :
    Cubical.boundary
        (integerStarMapInverse (integerStarMap S + x.1)) =
      Cubical.boundary S := by
  obtain ⟨a, ha⟩ := x.2
  rw [← ha]
  let u : Cubical.Chain 4 B :=
    integerStarMapInverse (sourceIntegerDualOneChain a)
  have hdx : sourceIntegerDualOneDifferential a =
      integerStarMap (Cubical.boundary u) := by
    rfl
  have hstar : integerStarMapInverse
      (sourceIntegerDualOneDifferential a) = Cubical.boundary u := by
    rw [hdx, integerStarMapInverse_starMap]
  rw [map_add, integerStarMapInverse_starMap, hstar]
  change Cubical.boundary (S + Cubical.boundary u) =
    Cubical.boundary S
  rw [map_add]
  have hbb : Cubical.boundary (Cubical.boundary u) = 0 := by
    have hh := congrArg
      (fun f : Cubical.Chain 4 B →ₗ[ℤ] Cubical.Chain 4 B => f u)
      Cubical.boundary_square_zero
    change Cubical.boundary (Cubical.boundary u) = 0 at hh
    exact hh
  rw [hbb]
  simp

noncomputable def sourceExactFieldToWilsonMode {B : SourceBox}
    (S : Cubical.Chain 4 B) (hS : Cubical.homogeneousSupport S 2)
    (x : SourceIntegerDualGaugeClass B) : SourceWilsonModes S := by
  classical
  let q : Cubical.Chain 4 B := integerStarMapInverse
    (integerStarMap S + x.1)
  let m : PrimalPlaquettes B → ℤ := fun p => q p.1
  have hqHom : Cubical.homogeneousSupport q 2 := by
    apply integerStarMapInverse_homogeneousSupport
      (integerStarMap S + x.1) 2
    intro c hc
    have hc' : c ∈ (integerStarMap S).support ∨ c ∈ x.1.support := by
      by_contra h
      have hA : c ∉ (integerStarMap S).support := fun hA => h (Or.inl hA)
      have hB : c ∉ x.1.support := fun hB => h (Or.inr hB)
      have hA0 := Finsupp.notMem_support_iff.mp hA
      have hB0 := Finsupp.notMem_support_iff.mp hB
      exact (Finsupp.mem_support_iff.mp hc) (by simp [hA0, hB0])
    rcases hc' with hcs | hcx
    · have hs := integerStarMap_homogeneousSupport S 2 hS
      exact hs c hcs
    · exact sourceGaugeClass_homogeneousSupport x c hcx
  have hboundary := integerDualModeSheet_boundary S hS x
  have hmodeChain : plaquetteModeChain m = q := by
    exact plaquetteModeChain_restrict q hqHom
  have hdiv : plaquetteModeDivergence m =
      primalSheetLoopFrequency S := by
    apply (plaquetteModeDivergence_eq_boundary m S hS).2
    rw [hmodeChain]
    exact hboundary
  exact ⟨m, hdiv⟩

private theorem sourceWilsonMode_toExactField {B : SourceBox}
    (S : Cubical.Chain 4 B) (hS : Cubical.homogeneousSupport S 2)
    (m : SourceWilsonModes S) :
    ∃ x : SourceIntegerDualGaugeClass B,
      integerStarMap S + x.1 = integerStarMap (plaquetteModeChain m.1) := by
  let p : Cubical.Chain 4 B := plaquetteModeChain m.1 - S
  have hpHom : Cubical.homogeneousSupport p 2 := by
    intro c hc
    have hp : c ∈ (plaquetteModeChain m.1).support ∨ c ∈ S.support := by
      by_contra h
      have hA : c ∉ (plaquetteModeChain m.1).support := fun hA => h (Or.inl hA)
      have hB : c ∉ S.support := fun hB => h (Or.inr hB)
      have hA0 := Finsupp.notMem_support_iff.mp hA
      have hB0 := Finsupp.notMem_support_iff.mp hB
      exact (Finsupp.mem_support_iff.mp hc) (by simp [p, hA0, hB0])
    rcases hp with hpq | hps
    · exact plaquetteModeChain_homogeneousSupport m.1 c hpq
    · exact hS c hps
  have hboundaryEq := (plaquetteModeDivergence_eq_boundary m.1 S hS).1 m.2
  have hclosed : Cubical.boundary p = 0 := by
    dsimp [p]
    rw [map_sub, hboundaryEq]
    simp
  let q : DualIntegerChain B := integerStarMap p
  have hqDegree : dualIntegerHomogeneousSupport q 2 := by
    exact integerStarMap_homogeneousSupport p 2 hpHom
  have hclosedStar : Cubical.boundary (integerStarMapInverse q) = 0 := by
    simpa [q, integerStarMapInverse_starMap] using hclosed
  obtain ⟨a, ha⟩ := exists_sourceIntegerDualOneField_of_closedDualChain
    q hqDegree hclosedStar
  refine ⟨⟨sourceIntegerDualOneDifferential a, ⟨a, rfl⟩⟩, ?_⟩
  change integerStarMap S +
      integerDualExteriorDifference (sourceIntegerDualOneChain a) = _
  rw [ha]
  dsimp [q, p]
  rw [map_sub]
  abel

theorem plaquetteModeChain_apply {B : Box 4}
    (m : PrimalPlaquettes B → ℤ) (p : PrimalPlaquettes B) :
    plaquetteModeChain m p.1 = m p := by
  classical
  unfold plaquetteModeChain
  rw [Finset.sum_apply']
  rw [Finset.sum_eq_single p]
  · simp
  · intro b hb hne
    have hbc : b.1 ≠ p.1 := by
      intro h
      apply hne
      exact Subtype.ext h
    simp [hbc]
  · simp

theorem sourceExactFieldToWilsonMode_chain {B : SourceBox}
    (S : Cubical.Chain 4 B) (hS : Cubical.homogeneousSupport S 2)
    (x : SourceIntegerDualGaugeClass B) :
    plaquetteModeChain (sourceExactFieldToWilsonMode S hS x).1 =
      integerStarMapInverse (integerStarMap S + x.1) := by
  let q : Cubical.Chain 4 B := integerStarMapInverse
    (integerStarMap S + x.1)
  have hqHom : Cubical.homogeneousSupport q 2 := by
    apply integerStarMapInverse_homogeneousSupport
      (integerStarMap S + x.1) 2
    intro c hc
    have hc' : c ∈ (integerStarMap S).support ∨ c ∈ x.1.support := by
      by_contra h
      have hA : c ∉ (integerStarMap S).support := fun hA => h (Or.inl hA)
      have hB : c ∉ x.1.support := fun hB => h (Or.inr hB)
      have hA0 := Finsupp.notMem_support_iff.mp hA
      have hB0 := Finsupp.notMem_support_iff.mp hB
      exact (Finsupp.mem_support_iff.mp hc) (by simp [hA0, hB0])
    rcases hc' with hcs | hcx
    · have hs := integerStarMap_homogeneousSupport S 2 hS
      exact hs c hcs
    · exact sourceGaugeClass_homogeneousSupport x c hcx
  change plaquetteModeChain (fun p => q p.1) = q
  exact plaquetteModeChain_restrict q hqHom

noncomputable def sourceWilsonModesEquiv {B : SourceBox}
    (S : Cubical.Chain 4 B) (hS : Cubical.homogeneousSupport S 2) :
    SourceIntegerDualGaugeClass B ≃ SourceWilsonModes S where
  toFun := sourceExactFieldToWilsonMode S hS
  invFun := fun m => Classical.choose (sourceWilsonMode_toExactField S hS m)
  left_inv := by
    intro x
    apply Subtype.ext
    let m := sourceExactFieldToWilsonMode S hS x
    let z := Classical.choose (sourceWilsonMode_toExactField S hS m)
    have hz := Classical.choose_spec (sourceWilsonMode_toExactField S hS m)
    have hm := sourceExactFieldToWilsonMode_chain S hS x
    have hz' : integerStarMap S + z.1 =
        integerStarMap S + x.1 := by
      calc
        integerStarMap S + z.1 =
            integerStarMap (plaquetteModeChain m.1) := by
              simpa [m] using hz
        _ = integerStarMap
            (integerStarMapInverse (integerStarMap S + x.1)) := by
              exact congrArg integerStarMap hm
        _ = integerStarMap S + x.1 := integerStarMap_starMapInverse _
    exact add_left_cancel hz'
  right_inv := by
    intro m
    apply Subtype.ext
    let z := Classical.choose (sourceWilsonMode_toExactField S hS m)
    have hz := Classical.choose_spec (sourceWilsonMode_toExactField S hS m)
    have hstar := congrArg integerStarMapInverse hz
    have hchain : S + integerStarMapInverse z.1 =
        plaquetteModeChain m.1 := by
      calc
        S + integerStarMapInverse z.1 =
            integerStarMapInverse (integerStarMap S) +
              integerStarMapInverse z.1 := by
                rw [integerStarMapInverse_starMap]
        _ = integerStarMapInverse (integerStarMap S + z.1) := by
              rw [map_add]
        _ = integerStarMapInverse
            (integerStarMap (plaquetteModeChain m.1)) := hstar
        _ = plaquetteModeChain m.1 := integerStarMapInverse_starMap _
    have hq : integerStarMapInverse (integerStarMap S + z.1) =
        plaquetteModeChain m.1 := by
      calc
        integerStarMapInverse (integerStarMap S + z.1) =
            S + integerStarMapInverse z.1 := by
              rw [map_add, integerStarMapInverse_starMap]
        _ = plaquetteModeChain m.1 := hchain
    apply funext
    intro p
    change integerStarMapInverse (integerStarMap S + z.1) p.1 = m.1 p
    rw [hq]
    exact plaquetteModeChain_apply m.1 p

theorem integerDualNormSq_star_eq_chain {B : SourceBox}
    (q : Cubical.Chain 4 B) :
    integerDualNormSq (integerStarMap q) =
      ∑ c : Cubical.Cell 4 B, (q c : ℝ) ^ 2 := by
  classical
  unfold integerDualNormSq integerDualPairing
  calc
    (∑ c : Cubical.DualCell 4 B,
        (integerStarMap q c : ℝ) * (integerStarMap q c : ℝ)) =
      ∑ c : Cubical.Cell 4 B,
        (integerStarMap q (Cubical.primalDualCellEquiv c) : ℝ) *
          (integerStarMap q (Cubical.primalDualCellEquiv c) : ℝ) := by
            symm
            exact Equiv.sum_comp Cubical.primalDualCellEquiv
              (fun c : Cubical.DualCell 4 B =>
                (integerStarMap q c : ℝ) * (integerStarMap q c : ℝ))
    _ = ∑ c : Cubical.Cell 4 B, (q c : ℝ) ^ 2 := by
          apply Finset.sum_congr rfl
          intro c hc
          simp [integerStarMap, Finsupp.equivMapDomain_apply, pow_two]

theorem plaquetteModeChain_sq_sum {B : Box 4}
    (m : PrimalPlaquettes B → ℤ) :
    (∑ c : Cubical.Cell 4 B, (plaquetteModeChain m c : ℝ) ^ 2) =
      ∑ p : PrimalPlaquettes B, (m p : ℝ) ^ 2 := by
  classical
  let P : Cubical.Cell 4 B → Prop := fun c => Cubical.cellDegree c = 2
  let f : Cubical.Cell 4 B → ℝ :=
    fun c => (plaquetteModeChain m c : ℝ) ^ 2
  let g : PrimalPlaquettes B → ℝ := fun p => (m p : ℝ) ^ 2
  have hfilter :
      (∑ c ∈ Finset.univ.filter P, f c) = ∑ p : PrimalPlaquettes B, g p := by
    refine Finset.sum_bij
      (fun c hc => (⟨c, (Finset.mem_filter.mp hc).2⟩ : PrimalPlaquettes B))
      ?_ ?_ ?_ ?_
    · intro c hc
      simp
    · intro c hc d hd h
      exact congrArg Subtype.val h
    · intro p hp
      refine ⟨p.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, p.2⟩, ?_⟩
      apply Subtype.ext
      rfl
    · intro c hc
      have hdegree := (Finset.mem_filter.mp hc).2
      have hcoeff := plaquetteModeChain_apply m
        (⟨c, hdegree⟩ : PrimalPlaquettes B)
      change plaquetteModeChain m c =
        m (⟨c, hdegree⟩ : PrimalPlaquettes B) at hcoeff
      exact congrArg (fun z : ℤ => (z : ℝ) ^ 2) hcoeff
  have hzero :
      (∑ c ∈ Finset.univ.filter (fun c => ¬ P c), f c) = 0 := by
    apply Finset.sum_eq_zero
    intro c hc
    have hnot := (Finset.mem_filter.mp hc).2
    have hqzero : plaquetteModeChain m c = 0 := by
      by_contra hn
      exact hnot (plaquetteModeChain_homogeneousSupport m c
        (Finsupp.mem_support_iff.mpr hn))
    simp [f, hqzero]
  calc
    (∑ c : Cubical.Cell 4 B, (plaquetteModeChain m c : ℝ) ^ 2) =
        (∑ c ∈ Finset.univ.filter P, f c) +
          ∑ c ∈ Finset.univ.filter (fun c => ¬ P c), f c := by
            symm
            exact Finset.sum_filter_add_sum_filter_not
              Finset.univ P f
    _ = ∑ p : PrimalPlaquettes B, (m p : ℝ) ^ 2 := by
          rw [hzero, hfilter]
          simp [g]

theorem dualGaussianProduct_eq_exp_sum {B : Box 4} (β : ℝ)
    (m : PrimalPlaquettes B → ℤ) :
    dualGaussianProduct β m =
      Real.exp (-(∑ p : PrimalPlaquettes B, (m p : ℝ) ^ 2) / (2 * β)) := by
  unfold dualGaussianProduct
  rw [← Real.exp_sum]
  congr 1
  calc
    (∑ p : PrimalPlaquettes B,
        -(m p : ℝ) ^ 2 / (2 * β)) =
      (∑ p : PrimalPlaquettes B, -(m p : ℝ) ^ 2) / (2 * β) := by
        rw [← Finset.sum_div]
    _ = -(∑ p : PrimalPlaquettes B, (m p : ℝ) ^ 2) / (2 * β) := by
        rw [← Finset.sum_neg_distrib]

theorem dualGaussianProduct_eq_integerDualNormSq {B : Box 4} (β : ℝ)
    (m : PrimalPlaquettes B → ℤ) :
    dualGaussianProduct β m =
      Real.exp
        (-integerDualNormSq (integerStarMap (plaquetteModeChain m)) /
          (2 * β)) := by
  rw [dualGaussianProduct_eq_exp_sum, integerDualNormSq_star_eq_chain,
    plaquetteModeChain_sq_sum]

theorem dualWilsonPartition_eq_sourceWilsonModes_sum {B : Box 4}
    (β : ℝ) (S : Cubical.Chain 4 B) :
    dualWilsonPartition β S =
      ∑' m : SourceWilsonModes S, dualGaussianProduct β m.1 := by
  classical
  let P : Set (PrimalPlaquettes B → ℤ) :=
    {m | plaquetteModeDivergence m = primalSheetLoopFrequency S}
  change (∑' m : PrimalPlaquettes B → ℤ, dualWilsonTerm β S m) = _
  calc
    (∑' m : PrimalPlaquettes B → ℤ, dualWilsonTerm β S m) =
      ∑' m : PrimalPlaquettes B → ℤ,
        P.indicator (dualGaussianProduct β) m := by
          apply tsum_congr
          intro m
          simp [dualWilsonTerm, P, Set.indicator]
    _ = ∑' m : SourceWilsonModes S, dualGaussianProduct β m.1 := by
          symm
          change (∑' m : {m // m ∈ P}, dualGaussianProduct β m.1) = _
          exact tsum_subtype P (fun m => dualGaussianProduct β m)

theorem sourceExactFieldToWilsonMode_star {B : SourceBox}
    (S : Cubical.Chain 4 B) (hS : Cubical.homogeneousSupport S 2)
    (x : SourceIntegerDualGaugeClass B) :
    integerStarMap (plaquetteModeChain
      (sourceExactFieldToWilsonMode S hS x).1) =
        integerStarMap S + x.1 := by
  have h := congrArg integerStarMap
    (sourceExactFieldToWilsonMode_chain S hS x)
  rw [integerStarMap_starMapInverse] at h
  exact h

theorem sourceDualGaugeClassShiftPartition_eq_dualWilsonPartition
    {B : SourceBox} (β : ℝ) (S : Cubical.Chain 4 B)
    (hS : Cubical.homogeneousSupport S 2) :
    sourceDualGaugeClassShiftPartition β (integerStarMap S) =
      dualWilsonPartition β S := by
  classical
  let e := sourceWilsonModesEquiv S hS
  calc
    sourceDualGaugeClassShiftPartition β (integerStarMap S) =
      ∑' x : SourceIntegerDualGaugeClass B,
        sourceDualWilsonGaugeClassWeight β (integerStarMap S) x := rfl
    _ = ∑' x : SourceIntegerDualGaugeClass B,
        dualGaussianProduct β (e x).1 := by
          apply tsum_congr
          intro x
          have hstar := sourceExactFieldToWilsonMode_star S hS x
          have he : (e x).1 = sourceExactFieldToWilsonMode S hS x := rfl
          have hstar' : integerStarMap
              (plaquetteModeChain (e x).1) = integerStarMap S + x.1 := by
            exact (congrArg (fun m : PrimalPlaquettes B → ℤ =>
              integerStarMap (plaquetteModeChain m)) he).trans hstar
          calc
            sourceDualWilsonGaugeClassWeight β (integerStarMap S) x =
                Real.exp
                  (-integerDualNormSq (x.1 + integerStarMap S) /
                    (2 * β)) := by
                    simp [sourceDualWilsonGaugeClassWeight]
            _ = Real.exp
                (-integerDualNormSq (integerStarMap S + x.1) /
                  (2 * β)) := by rw [add_comm x.1]
            _ = Real.exp
                (-integerDualNormSq
                    (integerStarMap
                      (plaquetteModeChain (e x).1)) /
                  (2 * β)) := by rw [← hstar']
            _ = dualGaussianProduct β (e x).1 :=
                  (dualGaussianProduct_eq_integerDualNormSq β (e x).1).symm
    _ = ∑' m : SourceWilsonModes S, dualGaussianProduct β m.1 :=
          Equiv.tsum_eq e (fun m => dualGaussianProduct β m.1)
    _ = dualWilsonPartition β S :=
          (dualWilsonPartition_eq_sourceWilsonModes_sum β S).symm

theorem sourceDualGaugeClassPartition_eq_dualWilsonPartition_zero
    {B : SourceBox} (β : ℝ) :
    sourceDualGaugeClassPartition (B := B) β =
      dualWilsonPartition β (0 : Cubical.Chain 4 B) := by
  have h := sourceDualGaugeClassShiftPartition_eq_dualWilsonPartition
    (B := B) β 0 (by
      intro c hc
      simp at hc)
  simpa [sourceDualGaugeClassShiftPartition,
    sourceDualGaugeClassPartition, sourceDualGaugeClassWeight,
    sourceDualWilsonGaugeClassWeight, integerStarMap] using h

theorem primalWilsonExpectation_eq_sourceDiscreteDualMoment
    {B : Box 4} (β : ℝ) (hβ : 0 < β)
    (S : Cubical.Chain 4 B)
    (hS : Cubical.homogeneousSupport S 2) :
    primalWilsonExpectation β S =
      (Real.exp (-integerDualNormSq (integerStarMap S) / (2 * β)) *
        sourceDiscreteDualExpectation β (integerStarMap S) : ℂ) := by
  have hnum := sourceDualGaugeClassShiftPartition_eq_dualWilsonPartition
    (B := B) β S hS
  have hden := sourceDualGaugeClassPartition_eq_dualWilsonPartition_zero
    (B := B) β
  rw [primalWilsonExpectation_eq_dualPartition_ratio β hβ S]
  rw [← hnum, ← hden, ← Complex.ofReal_div]
  rw [sourceDualGaugeClassShiftPartition_eq_tilted β hβ
    (integerStarMap S)]
  simp [sourceDiscreteDualExpectation, sourceDualGaugeClassPartition,
    sourceDualGaugeClassTiltSum, integerStarMap]
  ring


end FroehlichSpencer.FS82.Wilson

end
