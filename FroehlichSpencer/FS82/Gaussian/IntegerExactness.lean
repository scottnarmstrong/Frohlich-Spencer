/- Integer exactness and supported gauge potentials for the physical dual box. -/
module

public import FroehlichSpencer.FS82.Gaussian.LatticeOperator
public import FroehlichSpencer.FS82.Cubical.IntegerExactness

/-!
# Integer exactness on the finite dual box

A closed integer dual one-chain is a primal 3-cycle under the oriented cubical
star. integer prism fills that cycle; starring the filling gives an
integer dual zero-cochain.

The physical realization is developed below.
-/

public section

namespace FroehlichSpencer.FS82.Gaussian

open FroehlichSpencer.FS82.Cubical

abbrev DualIntegerChain (B : SourceBox) := Cubical.DualCell 4 B →₀ ℤ

@[expose] def integerStarMap {B : SourceBox} :
    Cubical.Chain 4 B →ₗ[ℤ] DualIntegerChain B where
  toFun q := Finsupp.equivMapDomain Cubical.primalDualCellEquiv q
  map_add' q r := by ext c; simp [Finsupp.equivMapDomain_apply]
  map_smul' a q := by ext c; simp [Finsupp.equivMapDomain_apply]

@[expose] def integerStarMapInverse {B : SourceBox} :
    DualIntegerChain B →ₗ[ℤ] Cubical.Chain 4 B where
  toFun q := Finsupp.equivMapDomain Cubical.primalDualCellEquiv.symm q
  map_add' q r := by ext c; simp [Finsupp.equivMapDomain_apply]
  map_smul' a q := by ext c; simp [Finsupp.equivMapDomain_apply]

theorem integerStarMapInverse_starMap {B : SourceBox}
    (q : Cubical.Chain 4 B) : integerStarMapInverse (integerStarMap q) = q := by
  ext c
  simp [integerStarMap, integerStarMapInverse, Finsupp.equivMapDomain_apply]

theorem integerStarMap_starMapInverse {B : SourceBox}
    (q : DualIntegerChain B) : integerStarMap (integerStarMapInverse q) = q := by
  ext c
  simp [integerStarMap, integerStarMapInverse, Finsupp.equivMapDomain_apply]

@[expose] noncomputable def sourceIntegerDualOneChain {B : SourceBox}
    (q : SourceDualOneCells B →₀ ℤ) : DualIntegerChain B :=
  Finsupp.embDomain sourceDualOneEmbedding q

@[expose] noncomputable def sourceIntegerDualZeroChain {B : SourceBox}
    (q : SourceDualZeroCells B →₀ ℤ) : DualIntegerChain B :=
  Finsupp.embDomain sourceDualZeroEmbedding q

@[expose] noncomputable def integerDualExteriorDifference {B : SourceBox} :
    DualIntegerChain B →ₗ[ℤ] DualIntegerChain B :=
  integerStarMap.comp
    (Cubical.boundary.comp integerStarMapInverse)

/-- Closedness is the primal cycle condition transported by the cubical star. -/
@[expose] def sourceIntegerClosed {B : SourceBox}
    (q : SourceDualOneCells B →₀ ℤ) : Prop :=
  Cubical.boundary (integerStarMapInverse (sourceIntegerDualOneChain q)) = 0

/-- Every integer closed field on the finite `Λ*` links is the dual gradient
of an integer potential on the finite dual vertices. -/
theorem exists_sourceIntegerDualPotential_of_closed {B : SourceBox}
    (q : SourceDualOneCells B →₀ ℤ) (hclosed : sourceIntegerClosed q) :
    ∃ u : SourceDualZeroCells B →₀ ℤ,
      integerDualExteriorDifference (sourceIntegerDualZeroChain u) =
        sourceIntegerDualOneChain q := by
  let qDual : DualIntegerChain B := sourceIntegerDualOneChain q
  let p : Cubical.Chain 4 B := integerStarMapInverse qDual
  have hqSupport : (qDual.support : Set (Cubical.DualCell 4 B)) ⊆
      Set.range sourceDualOneEmbedding := by
    intro c hc
    by_contra hnot
    have hzero : qDual c = 0 :=
      Finsupp.embDomain_of_notMem_range sourceDualOneEmbedding q c hnot
    exact (Finsupp.mem_support_iff.mp hc) hzero
  have hpHomogeneous : Cubical.homogeneousSupport p 3 := by
    intro c hc
    have hdual : Cubical.primalDualCellEquiv c ∈ qDual.support := by
      simpa [p, integerStarMapInverse, Finsupp.equivMapDomain_apply] using hc
    obtain ⟨e, he⟩ := hqSupport hdual
    have hdeg : Cubical.dualCellDegree (Cubical.primalDualCellEquiv c) = 1 := by
      rw [← he]
      exact e.2
    have hstar := Cubical.star_complementary_degree c
    rw [hdeg] at hstar
    omega
  have hpositive : Cubical.positiveDegreeSupport p := by
    intro c hc
    rw [hpHomogeneous c hc]
    omega
  have hcycle : Cubical.boundary p = 0 := by
    exact hclosed
  let anchor : Cubical.Anchor 4 B := fun i => ⟨0, Nat.zero_lt_succ _⟩
  have hfill : Cubical.boundary (Cubical.fillingOperator anchor p) = p := by
    have hprism := congrArg
      (fun T : Cubical.Chain 4 B →ₗ[ℤ] Cubical.Chain 4 B => T p)
      (Cubical.orderedPrism_identity anchor (List.finRange 4))
    change Cubical.boundary
          (Cubical.orderedPrismFilling anchor (List.finRange 4) p) +
        Cubical.orderedPrismFilling anchor (List.finRange 4)
          (Cubical.boundary p) =
        p - Cubical.orderedPrismProjection anchor (List.finRange 4) p at hprism
    have hproj := Cubical.orderedPrismProjection_kills_positiveSupport
      anchor p hpositive
    rw [hcycle, map_zero, hproj, sub_zero, add_zero] at hprism
    simpa [Cubical.fillingOperator] using hprism
  have hmHomogeneous : Cubical.homogeneousSupport
      (Cubical.fillingOperator anchor p) 4 := by
    exact Cubical.fillingOperator_homogeneousSupport anchor p 3 hpHomogeneous
  let uDual : DualIntegerChain B := integerStarMap (Cubical.fillingOperator anchor p)
  have huSupport : (uDual.support : Set (Cubical.DualCell 4 B)) ⊆
      Set.range sourceDualZeroEmbedding := by
    intro c hc
    have hprimal : Cubical.primalDualCellEquiv.symm c ∈
        (Cubical.fillingOperator anchor p).support := by
      simpa [uDual, integerStarMap, Finsupp.equivMapDomain_apply] using hc
    have hfour := hmHomogeneous (Cubical.primalDualCellEquiv.symm c) hprimal
    have hstar := Cubical.star_complementary_degree
      (Cubical.primalDualCellEquiv.symm c)
    rw [Cubical.primalDualCellEquiv.apply_symm_apply] at hstar
    rw [hfour] at hstar
    have hcdegree : Cubical.dualCellDegree c = 0 := by omega
    exact ⟨⟨c, hcdegree⟩, rfl⟩
  let u : SourceDualZeroCells B →₀ ℤ :=
    Finsupp.comapDomain sourceDualZeroEmbedding uDual
      sourceDualZeroEmbedding.injective.injOn
  have huEmbed : sourceIntegerDualZeroChain u = uDual := by
    dsimp [sourceIntegerDualZeroChain, u]
    exact Finsupp.embDomain_comapDomain huSupport
  refine ⟨u, ?_⟩
  change integerStarMap (Cubical.boundary
      (integerStarMapInverse (sourceIntegerDualZeroChain u))) = qDual
  rw [huEmbed, integerStarMapInverse_starMap, hfill]
  exact integerStarMap_starMapInverse qDual

@[expose] noncomputable def castIntegerFinsupp {α : Type*} (q : α →₀ ℤ) : α →₀ ℝ :=
  Finsupp.mapRange (fun z : ℤ => (z : ℝ)) (by simp) q

theorem castIntegerStarMap {B : SourceBox} (q : Cubical.Chain 4 B) :
    castIntegerFinsupp (integerStarMap q) =
      Cubical.starMap (Cubical.castIntegerChain q) := by
  ext c
  simp [castIntegerFinsupp, integerStarMap, Cubical.starMap,
    Cubical.castIntegerChain, Finsupp.equivMapDomain_apply]

theorem castIntegerStarMapInverse {B : SourceBox} (q : DualIntegerChain B) :
    Cubical.castIntegerChain (integerStarMapInverse q) =
      Cubical.starMapInverse (castIntegerFinsupp q) := by
  ext c
  simp [integerStarMapInverse, castIntegerFinsupp, Cubical.starMapInverse,
    Cubical.castIntegerChain, Finsupp.equivMapDomain_apply]

theorem castIntegerDualExteriorDifference {B : SourceBox}
    (q : DualIntegerChain B) :
    castIntegerFinsupp (integerDualExteriorDifference q) =
      Cubical.dualExteriorDifference (castIntegerFinsupp q) := by
  change castIntegerFinsupp
      (integerStarMap (Cubical.boundary (integerStarMapInverse q))) = _
  rw [castIntegerStarMap]
  change Cubical.starMap
      (Cubical.castIntegerChain (Cubical.boundary (integerStarMapInverse q))) = _
  have hbd := (Cubical.realifyLinearMap_cast Cubical.boundary
    (integerStarMapInverse q)).symm
  rw [show Cubical.castIntegerChain (Cubical.boundary (integerStarMapInverse q)) =
      Cubical.realBoundary (Cubical.castIntegerChain (integerStarMapInverse q)) by
        simpa [Cubical.realBoundary] using hbd]
  rw [castIntegerStarMapInverse]
  change Cubical.starMap
      (Cubical.realBoundary (Cubical.starMapInverse (castIntegerFinsupp q))) =
    Cubical.dualExteriorDifference (castIntegerFinsupp q)
  simp [Cubical.dualExteriorDifference, LinearMap.comp_apply]

theorem castSourceIntegerDualOneChain {B : SourceBox}
    (q : SourceDualOneCells B →₀ ℤ) :
    castIntegerFinsupp (sourceIntegerDualOneChain q) =
      embedDualSubtype sourceDualOneEmbedding (castIntegerFinsupp q) := by
  rw [embedDualSubtype_eq_embDomain]
  change Finsupp.mapRange (fun z : ℤ => (z : ℝ)) (by simp)
      (Finsupp.embDomain sourceDualOneEmbedding q) =
    Finsupp.embDomain sourceDualOneEmbedding
      (Finsupp.mapRange (fun z : ℤ => (z : ℝ)) (by simp) q)
  exact (Finsupp.embDomain_mapRange sourceDualOneEmbedding
    (fun z : ℤ => (z : ℝ)) q (by simp)).symm

theorem castSourceIntegerDualZeroChain {B : SourceBox}
    (q : SourceDualZeroCells B →₀ ℤ) :
    castIntegerFinsupp (sourceIntegerDualZeroChain q) =
      embedDualSubtype sourceDualZeroEmbedding (castIntegerFinsupp q) := by
  rw [embedDualSubtype_eq_embDomain]
  change Finsupp.mapRange (fun z : ℤ => (z : ℝ)) (by simp)
      (Finsupp.embDomain sourceDualZeroEmbedding q) =
    Finsupp.embDomain sourceDualZeroEmbedding
      (Finsupp.mapRange (fun z : ℤ => (z : ℝ)) (by simp) q)
  exact (Finsupp.embDomain_mapRange sourceDualZeroEmbedding
    (fun z : ℤ => (z : ℝ)) q (by simp)).symm

@[expose] def sourceDualZeroPhysicalEmbedding {B : SourceBox} (origin : Fin 4 → ℤ) :
    SourceDualZeroCells B ↪ Cubical.LatticeCell 4 :=
  Function.Embedding.trans sourceDualZeroEmbedding
    (Cubical.dualCellEmbedding origin)

theorem dualCellEmbedding_zero_isLatticeVertex {B : SourceBox}
    (origin : Fin 4 → ℤ) (a : SourceDualZeroCells B) :
    sourceLatticeVertex (Cubical.dualCellEmbedding origin a.1) := by
  change ∀ i : Fin 4, (Cubical.dualCellEmbedding origin a.1 i).isLeft
  intro i
  have hnot : i ∉ Cubical.dualCellAxes a.1 := by
    intro hi
    have hpos : 0 < (Cubical.dualCellAxes a.1).card :=
      Finset.card_pos.mpr ⟨i, hi⟩
    rw [← Cubical.dualCellDegree, a.2] at hpos
    omega
  cases hcoord : a.1 i with
  | inl v => simp [Cubical.dualCellEmbedding,
      Cubical.dualEmbedCoord, hcoord]
  | inr e =>
      exfalso
      apply hnot
      simp [Cubical.dualCellAxes, hcoord]

theorem integerLinearCombination_single_embedding_vanishes
    {α β : Type*} [DecidableEq β] (e : α ↪ β) (w : α → ℤ)
    (q : α →₀ ℤ) (b : β) (hb : b ∉ Set.range e) :
    Finsupp.linearCombination ℤ
      (fun a : α => Finsupp.single (e a) (w a)) q b = 0 := by
  classical
  induction q using Finsupp.induction_linear with
  | zero => simp
  | add q r hq hr =>
      rw [map_add]
      simp [Finsupp.add_apply, hq, hr]
  | single a z =>
      have hne : e a ≠ b := fun h => hb ⟨a, h⟩
      simp [Finsupp.linearCombination_single, hne]

theorem integerLinearCombination_single_eq_embDomain {α β : Type*}
    [DecidableEq β] (e : α ↪ β) (q : α →₀ ℤ) :
    Finsupp.linearCombination ℤ
      (fun a : α => Finsupp.single (e a) (1 : ℤ)) q =
      Finsupp.embDomain e q := by
  classical
  induction q using Finsupp.induction_linear with
  | zero => simp [Finsupp.linearCombination]
  | add q r hq hr =>
      rw [map_add, hq, hr]
      ext b
      simp [Finsupp.embDomain_apply]
  | single a z =>
      simp [Finsupp.linearCombination_single, Finsupp.embDomain_single]

theorem dualCellOrientationSign_zero {B : SourceBox}
    (c : Cubical.DualCell 4 B) (hc : Cubical.dualCellDegree c = 0) :
    dualCellOrientationSign c = 1 := by
  have haxes : Cubical.dualCellAxes c = ∅ := by
    apply Finset.card_eq_zero.mp
    simpa [Cubical.dualCellDegree] using hc
  simp [dualCellOrientationSign, axisSetOrientationSign, haxes]

@[expose] noncomputable def sourceIntegerPotentialOfDualZero {B : SourceBox}
    (origin : Fin 4 → ℤ) (u : SourceDualZeroCells B →₀ ℤ) :
    SourceIntegerPotential := by
  let e := sourceDualZeroPhysicalEmbedding (B := B) origin
  refine ⟨Finsupp.linearCombination ℤ
    (fun a : SourceDualZeroCells B => Finsupp.single (e a) (1 : ℤ)) u, ?_⟩
  intro c hnotVertex
  have hnotRange : c ∉ Set.range e := by
    rintro ⟨a, ha⟩
    have hv : sourceLatticeVertex c := by
      rw [← ha]
      exact dualCellEmbedding_zero_isLatticeVertex origin a
    exact hnotVertex hv
  exact integerLinearCombination_single_embedding_vanishes
    e (fun _ => 1) u c hnotRange

theorem sourceIntegerPotentialOfDualZero_eq_embDomain {B : SourceBox}
    (origin : Fin 4 → ℤ) (u : SourceDualZeroCells B →₀ ℤ) :
    (sourceIntegerPotentialOfDualZero origin u).1 =
      Finsupp.embDomain (sourceDualZeroPhysicalEmbedding origin) u := by
  change Finsupp.linearCombination ℤ
      (fun a : SourceDualZeroCells B => Finsupp.single
        (sourceDualZeroPhysicalEmbedding origin a) (1 : ℤ)) u = _
  exact integerLinearCombination_single_eq_embDomain
    (sourceDualZeroPhysicalEmbedding origin) u

theorem dualOrientationSignTwist_embedSourceZero {B : SourceBox}
    (u : SourceDualZeroCells B →₀ ℝ) :
    dualOrientationSignTwist (embedDualSubtype sourceDualZeroEmbedding u) =
      embedDualSubtype sourceDualZeroEmbedding u := by
  classical
  induction u using Finsupp.induction_linear with
  | zero => simp [dualOrientationSignTwist, embedDualSubtype]
  | add u v hu hv => simp [map_add, hu, hv]
  | single a z =>
      rw [embedDualSubtype_apply_single, dualOrientationSignTwist_single]
      have hsign : dualCellOrientationSign (sourceDualZeroEmbedding a) = 1 := by
        change dualCellOrientationSign a.1 = 1
        exact dualCellOrientationSign_zero a.1 a.2
      rw [hsign]
      simp

theorem castSourceIntegerPotentialOfDualZero {B : SourceBox}
    (origin : Fin 4 → ℤ) (u : SourceDualZeroCells B →₀ ℤ) :
    Cubical.castLatticeChain (sourceIntegerPotentialOfDualZero origin u).1 =
      sourcePhysicalDualZeroExtension origin
        (dualOrientationSignTwist
          (embedDualSubtype sourceDualZeroEmbedding (castIntegerFinsupp u))) := by
  rw [sourceIntegerPotentialOfDualZero_eq_embDomain,
    dualOrientationSignTwist_embedSourceZero,
    sourcePhysicalDualZeroExtension_embedDualSubtype]
  rw [show Cubical.castLatticeChain
      (Finsupp.embDomain (sourceDualZeroPhysicalEmbedding (B := B) origin) u) =
      Finsupp.embDomain (sourceDualZeroPhysicalEmbedding (B := B) origin)
        (castIntegerFinsupp u) by
        change Finsupp.mapRange (fun z : ℤ => (z : ℝ)) (by simp)
            (Finsupp.embDomain (sourceDualZeroPhysicalEmbedding (B := B) origin) u) = _
        exact (Finsupp.embDomain_mapRange
          (sourceDualZeroPhysicalEmbedding (B := B) origin)
          (fun z : ℤ => (z : ℝ)) u (by simp)).symm]
  rw [← linearCombination_single_eq_embDomain]
  rfl

theorem sourcePhysicalDualZeroExtension_twist_commutes {B : SourceBox}
    (origin : Fin 4 → ℤ) (q : Cubical.DualRealChain 4 B) :
    latticeOrientationSignTwist (sourcePhysicalDualZeroExtension origin q) =
      sourcePhysicalDualZeroExtension origin (dualOrientationSignTwist q) := by
  classical
  induction q using Finsupp.induction_linear with
  | zero => simp [sourcePhysicalDualZeroExtension, dualOrientationSignTwist]
  | add q r hq hr => simp [map_add, hq, hr]
  | single c z =>
      rw [dualOrientationSignTwist_single,
        sourcePhysicalDualZeroExtension_single,
        latticeOrientationSignTwist_single,
        sourcePhysicalDualZeroExtension_single,
        latticeCellOrientationSign_physical]

theorem castLatticeChain_add {d : ℕ} (q r : Cubical.LatticeChain d) :
    Cubical.castLatticeChain (q + r) =
      Cubical.castLatticeChain q + Cubical.castLatticeChain r := by
  ext c
  simp [Cubical.castLatticeChain, Finsupp.mapRange]

theorem castLatticeChain_int_smul {d : ℕ} (z : ℤ)
    (q : Cubical.LatticeChain d) :
    Cubical.castLatticeChain (z • q) =
      (z : ℝ) • Cubical.castLatticeChain q := by
  ext c
  simp [Cubical.castLatticeChain, Finsupp.mapRange, Int.cast_mul]

theorem sourceRealLatticeCoboundary_cast (q : Cubical.LatticeChain 4) :
    sourceRealLatticeCoboundary (Cubical.castLatticeChain q) =
      Cubical.castLatticeChain (Cubical.latticeCoboundary q) := by
  induction q using Finsupp.induction_linear with
  | zero => simp [sourceRealLatticeCoboundary, Cubical.castLatticeChain]
  | add q r hq hr =>
      calc
        sourceRealLatticeCoboundary (Cubical.castLatticeChain (q + r)) =
            sourceRealLatticeCoboundary (Cubical.castLatticeChain q) +
              sourceRealLatticeCoboundary (Cubical.castLatticeChain r) := by
          rw [castLatticeChain_add, map_add]
        _ = Cubical.castLatticeChain (Cubical.latticeCoboundary q) +
              Cubical.castLatticeChain (Cubical.latticeCoboundary r) := by rw [hq, hr]
        _ = Cubical.castLatticeChain
              (Cubical.latticeCoboundary (q + r)) := by
          rw [map_add, castLatticeChain_add]
  | single c z =>
      rw [show Finsupp.single c z = z • Cubical.latticeBasis c by
        ext x
        simp [Cubical.latticeBasis]]
      have hbase : sourceRealLatticeCoboundary
          (Cubical.castLatticeChain (Cubical.latticeBasis c)) =
          Cubical.castLatticeChain (Cubical.latticeCoboundaryBasis c) := by
        simp [sourceRealLatticeCoboundary, Cubical.castLatticeChain,
          Cubical.latticeBasis,
          Finsupp.linearCombination_single]
      calc
        sourceRealLatticeCoboundary
            (Cubical.castLatticeChain (z • Cubical.latticeBasis c)) =
            (z : ℝ) • sourceRealLatticeCoboundary
              (Cubical.castLatticeChain (Cubical.latticeBasis c)) := by
          rw [castLatticeChain_int_smul, map_smul]
        _ = (z : ℝ) • Cubical.castLatticeChain
            (Cubical.latticeCoboundaryBasis c) := by rw [hbase]
        _ = Cubical.castLatticeChain (z • Cubical.latticeCoboundaryBasis c) := by
          rw [castLatticeChain_int_smul]
        _ = Cubical.castLatticeChain
            (Cubical.latticeCoboundary (z • Cubical.latticeBasis c)) := by
          rw [map_smul, Cubical.latticeCoboundary_basis]

theorem castLambdaStarZeroExtension {B : SourceBox}
    (origin : Fin 4 → ℤ) (q : Cubical.LambdaStarChain B) :
    Cubical.castLatticeChain (Cubical.lambdaStarZeroExtension origin q) =
      Cubical.lambdaStarRealZeroExtension origin (castIntegerFinsupp q) := by
  rw [Cubical.lambdaStarZeroExtension_eq_embDomain,
    Cubical.lambdaStarRealZeroExtension_eq_embDomain]
  change Finsupp.mapRange (fun z : ℤ => (z : ℝ)) (by simp)
      (Finsupp.embDomain (Cubical.lambdaStarEmbedding (B := B) origin) q) =
    Finsupp.embDomain (Cubical.lambdaStarEmbedding (B := B) origin)
      (Finsupp.mapRange (fun z : ℤ => (z : ℝ)) (by simp) q)
  exact (Finsupp.embDomain_mapRange
    (Cubical.lambdaStarEmbedding (B := B) origin)
    (fun z : ℤ => (z : ℝ)) q (by simp)).symm

@[expose] noncomputable def sourceIntegerTChain {B : SourceBox}
    (q : SourceDualOneCells B →₀ ℤ) : SourceDualOneCells B →₀ ℤ :=
  Finsupp.linearCombination ℤ
    (fun e : SourceDualOneCells B => Finsupp.single e
      (sourceIntegerOrientationSign e)) q

theorem sourceIntegerTChain_apply {B : SourceBox}
    (q : SourceDualOneCells B →₀ ℤ) (e : SourceDualOneCells B) :
    sourceIntegerTChain q e = sourceIntegerOrientationSign e * q e := by
  classical
  induction q using Finsupp.induction_linear with
  | zero => simp [sourceIntegerTChain]
  | add q r hq hr =>
      change (Finsupp.linearCombination ℤ
        (fun e : SourceDualOneCells B => Finsupp.single e
          (sourceIntegerOrientationSign e)) (q + r)) e = _
      rw [map_add, Finsupp.add_apply]
      change (sourceIntegerTChain q) e + (sourceIntegerTChain r) e = _
      rw [hq, hr, Finsupp.add_apply]
      ring
  | single a z =>
      by_cases h : a = e
      · subst a
        simp [sourceIntegerTChain, Finsupp.linearCombination_single]
        ring
      · simp [sourceIntegerTChain, Finsupp.linearCombination_single, h]

theorem castSourceIntegerTChain {B : SourceBox}
    (q : SourceDualOneCells B →₀ ℤ) :
    castIntegerFinsupp (sourceIntegerTChain q) =
      sourceDualTMap (castIntegerFinsupp q) := by
  ext e
  change (sourceIntegerTChain q e : ℝ) =
    sourceDualTMap (castIntegerFinsupp q) e
  rw [sourceIntegerTChain_apply, sourceDualTMap_apply]
  have hsign : (sourceIntegerOrientationSign e : ℝ) =
      dualCellOrientationSign e.1 := by
    rw [sourceIntegerOrientationSign_eq_sourceDualT,
      sourceDualT_cast_eq_orientationSign]
  simp [castIntegerFinsupp, hsign, Int.cast_mul]

theorem castLambdaStarZeroExtension_sourceIntegerTChain {B : SourceBox}
    (origin : Fin 4 → ℤ) (q : SourceDualOneCells B →₀ ℤ) :
    Cubical.castLatticeChain
        (Cubical.lambdaStarZeroExtension origin (sourceIntegerTChain q)) =
      Cubical.lambdaStarRealZeroExtension origin
        (sourceDualTMap (castIntegerFinsupp q)) := by
  rw [castLambdaStarZeroExtension, castSourceIntegerTChain]

theorem sourceIntegerClosed_has_supported_latticePotential {B : SourceBox}
    (origin : Fin 4 → ℤ) (q : SourceDualOneCells B →₀ ℤ)
    (hclosed : sourceIntegerClosed q) :
    ∃ γ : SourceIntegerPotential,
      ((γ.1.support : Set (Cubical.LatticeCell 4)) ⊆
        Set.range (sourceDualZeroPhysicalEmbedding (B := B) origin)) ∧
      ((Cubical.latticeCoboundary γ.1).support : Set (Cubical.LatticeCell 4)) ⊆
        Set.range (Cubical.lambdaStarEmbedding (B := B) origin) ∧
      ∀ e : SourceDualOneCells B,
        Cubical.latticeCoboundary γ.1
            (Cubical.lambdaStarEmbedding (B := B) origin e) =
          sourceIntegerOrientationSign e * q e := by
  obtain ⟨u, hu⟩ := exists_sourceIntegerDualPotential_of_closed q hclosed
  let qR := castIntegerFinsupp q
  let uR := castIntegerFinsupp u
  let x : EuclideanSpace ℝ (SourceDualZeroCells B) := finsuppToEuclidean uR
  let y : EuclideanSpace ℝ (SourceDualOneCells B) := finsuppToEuclidean qR
  have hdualExact : Cubical.dualExteriorDifference
      (embedDualSubtype sourceDualZeroEmbedding uR) =
        embedDualSubtype sourceDualOneEmbedding qR := by
    have hcast := congrArg castIntegerFinsupp hu
    rw [castIntegerDualExteriorDifference, castSourceIntegerDualZeroChain,
      castSourceIntegerDualOneChain] at hcast
    exact hcast
  have hx : sourceDualZeroToChain x =
      embedDualSubtype sourceDualZeroEmbedding uR := by
    simp [x, sourceDualZeroToChain, LinearMap.comp_apply,
      euclideanToFinsupp_finsuppToEuclidean]
  have hy : sourceDualOneToChain y =
      embedDualSubtype sourceDualOneEmbedding qR := by
    simp [y, sourceDualOneToChain, LinearMap.comp_apply,
      euclideanToFinsupp_finsuppToEuclidean]
  have hD₀ : sourceDualD₀ x = y := by
    apply sourceDualOneToChain_injective
    calc
      sourceDualOneToChain (sourceDualD₀ x) =
          Cubical.dualExteriorDifference (sourceDualZeroToChain x) :=
        sourceDualD₀_embed_eq_derivative x
      _ = embedDualSubtype sourceDualOneEmbedding qR := by
        rw [hx, hdualExact]
      _ = sourceDualOneToChain y := hy.symm
  let γ := sourceIntegerPotentialOfDualZero origin u
  have hbridge := sourceDualD₀_physical_bridge origin x
  rw [hD₀, hy, sourcePhysicalDualZeroExtension_embedSourceOne] at hbridge
  rw [hx] at hbridge
  rw [← castSourceIntegerPotentialOfDualZero origin u] at hbridge
  rw [sourceRealLatticeCoboundary_cast] at hbridge
  have htwisted := congrArg latticeOrientationSignTwist hbridge
  rw [latticeOrientationSignTwist_involutive] at htwisted
  have hleft :
      latticeOrientationSignTwist
          (Cubical.lambdaStarRealZeroExtension origin qR) =
        Cubical.lambdaStarRealZeroExtension origin (sourceDualTMap qR) := by
    calc
      latticeOrientationSignTwist
          (Cubical.lambdaStarRealZeroExtension origin qR) =
          latticeOrientationSignTwist
            (sourcePhysicalDualZeroExtension origin
              (sourceDualOneToChain y)) := by
          rw [hy, sourcePhysicalDualZeroExtension_embedSourceOne]
      _ = sourcePhysicalDualZeroExtension origin
          (dualOrientationSignTwist (sourceDualOneToChain y)) :=
        sourcePhysicalDualZeroExtension_twist_commutes origin _
      _ = Cubical.lambdaStarRealZeroExtension origin
          (sourceDualTMap (euclideanToFinsupp y)) :=
        sourcePhysicalDualZeroExtension_sourceDualTMap origin y
      _ = Cubical.lambdaStarRealZeroExtension origin (sourceDualTMap qR) := by
        rw [show euclideanToFinsupp y = qR by
          simp [y, euclideanToFinsupp_finsuppToEuclidean]]
  rw [hleft] at htwisted
  have hreal :
      Cubical.castLatticeChain (Cubical.latticeCoboundary γ.1) =
        Cubical.castLatticeChain
          (Cubical.lambdaStarZeroExtension origin (sourceIntegerTChain q)) := by
    calc
      Cubical.castLatticeChain (Cubical.latticeCoboundary γ.1) =
          Cubical.lambdaStarRealZeroExtension origin (sourceDualTMap qR) :=
        htwisted.symm
      _ = Cubical.castLatticeChain
          (Cubical.lambdaStarZeroExtension origin (sourceIntegerTChain q)) :=
        (castLambdaStarZeroExtension_sourceIntegerTChain origin q).symm
  have hexact : Cubical.latticeCoboundary γ.1 =
      Cubical.lambdaStarZeroExtension origin (sourceIntegerTChain q) := by
    ext c
    have hc := congrArg (fun z : Cubical.RealLatticeChain 4 => z c) hreal
    have hc' : ((Cubical.latticeCoboundary γ.1 c : ℤ) : ℝ) =
        ((Cubical.lambdaStarZeroExtension origin (sourceIntegerTChain q) c : ℤ) : ℝ) := by
      simpa [Cubical.castLatticeChain, castIntegerFinsupp] using hc
    exact Int.cast_injective hc'
  refine ⟨γ, ?_, ?_, ?_⟩
  · intro c hc
    by_contra hnot
    have hzero : γ.1 c = 0 := by
      rw [sourceIntegerPotentialOfDualZero_eq_embDomain]
      exact Finsupp.embDomain_of_notMem_range
        (sourceDualZeroPhysicalEmbedding origin) u c hnot
    exact (Finsupp.mem_support_iff.mp hc) hzero
  · intro c hc
    by_contra hnot
    have hzero := Cubical.lambdaStarZeroExtension_vanishes_outside
      origin (sourceIntegerTChain q) c hnot
    rw [hexact] at hc
    exact (Finsupp.mem_support_iff.mp hc) hzero
  · intro e
    rw [hexact, sourceLambdaStarEmbedding_preserves_coefficients,
      sourceIntegerTChain_apply]

end FroehlichSpencer.FS82.Gaussian
end
