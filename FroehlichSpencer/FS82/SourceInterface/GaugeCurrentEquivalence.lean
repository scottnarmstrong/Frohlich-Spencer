module

public import FroehlichSpencer.FS82.SourceInterface.IntegerGaugeTransport
public import FroehlichSpencer.FS82.SourceInterface.CarrierTransport
public import FroehlichSpencer.FS82.SourceInterface.CurlExactness

@[expose] public section

open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Gaussian
open FroehlichSpencer.FS82.Surface
open FroehlichSpencer.FS82.Surface.IntegerGaugeTransport
open FroehlichSpencer.FS82.SourceModels.IntegerDualModel

namespace FroehlichSpencer.FS82.Surface.GaugeCurrentEquivalence

variable [SourceRelationEquivalenceGate]

noncomputable def signedDifference (R : RectBox4)
    (α α' : IntegerDualField R) : SourceDualOneCells R.side →₀ ℤ :=
  Finsupp.equivFunOnFinite.symm
    (fun e => sourceIntegerSignTwist α' e - sourceIntegerSignTwist α e)

omit [SourceRelationEquivalenceGate] in
theorem sourceCurlInput_eq_signedField (R : RectBox4)
    (α : IntegerDualField R) (e : SourceDualOneCells R.side) :
    sourceCurlInput R α e = (sourceIntegerSignTwist α e : ℝ) := by
  rw [sourceCurlInput, sourceDualTLinear_apply]
  change dualCellOrientationSign e.1 *
    (castIntegerFinsupp (sourceFieldOfLiteral R α) e) = _
  simp only [castIntegerFinsupp, Finsupp.mapRange_apply]
  rw [sourceFieldOfLiteral_apply]
  have he : (linksEquivSource R).symm e = e := rfl
  rw [he]
  have hsign : dualCellOrientationSign e.1 =
      (sourceIntegerOrientationSign e : ℝ) := by
    rw [sourceIntegerOrientationSign_eq_sourceDualT,
      sourceDualT_cast_eq_orientationSign]
  rw [hsign]
  simp [sourceIntegerSignTwist, Int.cast_mul]

omit [SourceRelationEquivalenceGate] in
theorem sourceDualOneToChain_signedDifference (R : RectBox4)
    (α α' : IntegerDualField R) :
    sourceDualOneToChain
        (sourceCurlInput R α' - sourceCurlInput R α) =
      castIntegerFinsupp (sourceIntegerDualOneChain
        (signedDifference R α α')) := by
  have hv : sourceCurlInput R α' - sourceCurlInput R α =
      Gaussian.finsuppToEuclidean
        (castIntegerFinsupp (signedDifference R α α')) := by
    ext e
    change sourceCurlInput R α' e - sourceCurlInput R α e = _
    rw [sourceCurlInput_eq_signedField, sourceCurlInput_eq_signedField]
    simp [signedDifference, castIntegerFinsupp]
  rw [hv, sourceDualOneToChain_finsuppToEuclidean,
    castSourceIntegerDualOneChain]

omit [SourceRelationEquivalenceGate] in
theorem integerCurl_eq_implies_sourceD₁_eq (R : RectBox4)
    (α α' : IntegerDualField R)
    (hcurl : integerLatticeCurl R α' = integerLatticeCurl R α) :
    sourceDualD₁ (sourceCurlInput R α') = sourceDualD₁ (sourceCurlInput R α) := by
  have hcast := congrArg (castLatticeChain) hcurl
  change Cubical.castLatticeChain (integerLatticeCurl R α') =
    Cubical.castLatticeChain (integerLatticeCurl R α) at hcast
  rw [literalCurl_cast_eq_sourceCurl, literalCurl_cast_eq_sourceCurl] at hcast
  have hphys0 := congrArg latticeOrientationSignTwist hcast
  have hphys : sourcePhysicalDualZeroExtension R.origin
      (sourceDualTwoToChain (sourceDualD₁ (sourceCurlInput R α'))) =
    sourcePhysicalDualZeroExtension R.origin
      (sourceDualTwoToChain (sourceDualD₁ (sourceCurlInput R α))) := by
    simpa only [latticeOrientationSignTwist_involutive] using hphys0
  rw [sourceDualTwoPhysicalChain_repr, sourceDualTwoPhysicalChain_repr] at hphys
  ext f
  have hcoeff := congrArg (fun q : Cubical.RealLatticeChain 4 =>
    q (sourcePhysicalDualTwoEmbedding R.origin f)) hphys
  simpa [Finsupp.embDomain_apply_self, Gaussian.euclideanToFinsupp] using hcoeff

omit [SourceRelationEquivalenceGate] in
theorem sourceCurl_eq_implies_integerClosed (R : RectBox4)
    (α α' : IntegerDualField R)
    (hcurl : integerLatticeCurl R α' = integerLatticeCurl R α) :
    sourceIntegerClosed (signedDifference R α α') := by
  have hD₁ := integerCurl_eq_implies_sourceD₁_eq R α α' hcurl
  have hzero : sourceDualD₁
      (sourceCurlInput R α' - sourceCurlInput R α) = 0 := by
    rw [map_sub, hD₁]
    simp
  have hchain := congrArg sourceDualTwoToChain hzero
  rw [sourceDualD₁_embed_eq_derivative] at hchain
  rw [sourceDualOneToChain_signedDifference] at hchain
  have hdual : Cubical.dualExteriorDifference
      (castIntegerFinsupp (sourceIntegerDualOneChain
        (signedDifference R α α'))) = 0 := by
    simpa using hchain
  have hcast := castIntegerDualExteriorDifference
    (sourceIntegerDualOneChain (signedDifference R α α'))
  have hcastZero : castIntegerFinsupp
      (integerDualExteriorDifference
        (sourceIntegerDualOneChain (signedDifference R α α'))) = 0 := by
    rw [hcast]
    exact hdual
  have hinterm : integerDualExteriorDifference
      (sourceIntegerDualOneChain (signedDifference R α α')) = 0 := by
    ext c
    have hc := congrArg (fun q : Cubical.DualRealChain 4 R.side => q c) hcastZero
    have hreal : ((integerDualExteriorDifference
        (sourceIntegerDualOneChain (signedDifference R α α')) c : ℤ) : ℝ) = 0 := by
      simpa [castIntegerFinsupp, Finsupp.mapRange_apply] using hc
    exact_mod_cast hreal
  change integerStarMap (Cubical.boundary
      (integerStarMapInverse
        (sourceIntegerDualOneChain (signedDifference R α α')))) = 0 at hinterm
  have hboundary := congrArg integerStarMapInverse hinterm
  change Cubical.boundary
      (integerStarMapInverse
        (sourceIntegerDualOneChain (signedDifference R α α'))) = 0
  simpa [integerStarMapInverse_starMap] using hboundary

omit [SourceRelationEquivalenceGate] in
theorem sourceCurl_eq_implies_gauge (R : RectBox4)
    (α α' : IntegerDualField R)
    (hcurl : integerLatticeCurl R α' = integerLatticeCurl R α) :
    sourceIntegerGaugeRelation R α α' := by
  let q := signedDifference R α α'
  obtain ⟨γ, _hpotentialSupport, hsupport, hshift⟩ :=
    sourceIntegerClosed_has_supported_latticePotential R.origin q
      (sourceCurl_eq_implies_integerClosed R α α' hcurl)
  apply (sourceIntegerGaugeRelation_iff_sourceExactShiftSupportCondition226_internal
    R α α').mpr
  refine ⟨γ, hsupport, ?_⟩
  intro e
  exact (hshift e).symm

noncomputable def untwistedCurrent (R : RectBox4)
    (J : SourceClosedIntegerCurrent R) : SourceDualTwoCells R.side →₀ ℤ :=
  Finsupp.equivFunOnFinite.symm (fun f =>
    sourceDualSigma f * J.1 (sourcePhysicalDualTwoEmbedding R.origin f))

omit [SourceRelationEquivalenceGate] in
theorem cast_embDomain_integer {α β : Type*} [DecidableEq β]
    (e : α ↪ β) (q : α →₀ ℤ) :
    castIntegerFinsupp (Finsupp.embDomain e q) =
      Finsupp.embDomain e (castIntegerFinsupp q) := by
  change Finsupp.mapRange (fun z : ℤ => (z : ℝ)) (by simp)
      (Finsupp.embDomain e q) =
    Finsupp.embDomain e
      (Finsupp.mapRange (fun z : ℤ => (z : ℝ)) (by simp) q)
  exact (Finsupp.embDomain_mapRange e (fun z : ℤ => (z : ℝ)) q (by simp)).symm

omit [SourceRelationEquivalenceGate] in
theorem untwistedCurrent_physical_repr (R : RectBox4)
    (J : SourceClosedIntegerCurrent R) :
    Finsupp.embDomain (sourcePhysicalDualTwoEmbedding R.origin)
        (castIntegerFinsupp (untwistedCurrent R J)) =
      latticeOrientationSignTwist (Cubical.castLatticeChain J.1) := by
  classical
  ext c
  by_cases hc : c ∈ Set.range
      (sourcePhysicalDualTwoEmbedding (B := R.side) R.origin)
  · rcases hc with ⟨f, rfl⟩
    have hsign : (sourceDualSigma f : ℝ) =
        latticeCellOrientationSign
          (sourcePhysicalDualTwoEmbedding (B := R.side) R.origin f) := by
      calc
        (sourceDualSigma f : ℝ) = dualCellOrientationSign f.1 :=
          sourceDualSigma_cast_eq_orientationSign f
        _ = latticeCellOrientationSign
            (sourcePhysicalDualTwoEmbedding (B := R.side) R.origin f) := by
          exact (latticeCellOrientationSign_physical R.origin f.1).symm
    have hval : untwistedCurrent R J f =
        sourceDualSigma f * J.1
          (sourcePhysicalDualTwoEmbedding (B := R.side) R.origin f) := by
      exact congrFun (Finsupp.coe_equivFunOnFinite_symm
        (fun g : SourceDualTwoCells R.side => sourceDualSigma g *
          J.1 (sourcePhysicalDualTwoEmbedding (B := R.side) R.origin g))) f
    simp only [Finsupp.embDomain_apply_self, castIntegerFinsupp,
      Finsupp.mapRange_apply, latticeOrientationSignTwist_apply,
      Cubical.castLatticeChain, Finsupp.mapRange_apply]
    rw [hval, Int.cast_mul, hsign]
  · have hJzero : J.1 c = 0 := by
      by_contra hne
      have hmem := J.2.2 c (Finsupp.mem_support_iff.mpr hne)
      rcases hmem with ⟨p, hp⟩
      let f : SourceDualTwoCells R.side := ⟨p.1, p.2⟩
      apply hc
      refine ⟨f, ?_⟩
      change Cubical.dualCellEmbedding (B := R.side) R.origin p.1 = c
      rw [← c1Cell_bridge R]
      exact hp
    have hleft : (Finsupp.embDomain
        (sourcePhysicalDualTwoEmbedding (B := R.side) R.origin)
        (castIntegerFinsupp (untwistedCurrent R J))) c = 0 :=
      Finsupp.embDomain_of_notMem_range _ _ c hc
    rw [hleft, latticeOrientationSignTwist_apply]
    change 0 = latticeCellOrientationSign c * ((J.1 c : ℤ) : ℝ)
    rw [hJzero]
    simp

omit [SourceRelationEquivalenceGate] in
theorem sourcePhysicalDualZeroExtension_apply_embedding {B : SourceBox}
    (origin : Fin 4 → ℤ) (q : Cubical.DualRealChain 4 B)
    (c : Cubical.DualCell 4 B) :
    sourcePhysicalDualZeroExtension origin q
      (Cubical.dualCellEmbedding (B := B) origin c) = q c := by
  change Finsupp.linearCombination ℝ
      (fun d : Cubical.DualCell 4 B =>
        Finsupp.single (Cubical.dualCellEmbedding (B := B) origin d) 1)
      q (Cubical.dualCellEmbedding (B := B) origin c) = q c
  exact linearCombination_single_embedding_hits
    (Cubical.dualCellEmbedding (B := B) origin) q c

omit [SourceRelationEquivalenceGate] in
theorem untwistedCurrent_dualClosed (R : RectBox4)
    (J : SourceClosedIntegerCurrent R) :
    Cubical.dualExteriorDifference
      (sourceDualTwoToChain
        (Gaussian.finsuppToEuclidean
          (castIntegerFinsupp (untwistedCurrent R J)))) = 0 := by
  let D := sourceDualTwoToChain
    (Gaussian.finsuppToEuclidean (castIntegerFinsupp (untwistedCurrent R J)))
  have hrepr : sourcePhysicalDualZeroExtension R.origin D =
      latticeOrientationSignTwist (Cubical.castLatticeChain J.1) := by
    rw [sourceDualTwoPhysicalChain_repr]
    simp only [Gaussian.euclideanToFinsupp_finsuppToEuclidean]
    exact untwistedCurrent_physical_repr R J
  have htwist : sourcePhysicalDualZeroExtension R.origin
      (dualOrientationSignTwist D) = Cubical.castLatticeChain J.1 := by
    calc
      _ = latticeOrientationSignTwist
          (sourcePhysicalDualZeroExtension R.origin D) :=
        (sourcePhysicalDualZeroExtension_twist_commutes R.origin D).symm
      _ = latticeOrientationSignTwist
          (latticeOrientationSignTwist (Cubical.castLatticeChain J.1)) := by
        rw [hrepr]
      _ = Cubical.castLatticeChain J.1 := latticeOrientationSignTwist_involutive _
  have hboundary : sourceRealLatticeCoboundary
      (Cubical.castLatticeChain J.1) = 0 := by
    have hJclosed : Cubical.latticeCoboundary J.1 = 0 := J.2.1
    rw [sourceRealLatticeCoboundary_cast, hJclosed]
    simp [Cubical.castLatticeChain]
  have hbridge := LinearMap.congr_fun
    (sourcePhysicalDualZeroExtension_comp_dualExteriorDifference R.origin) D
  have hbridge' : sourcePhysicalDualZeroExtension R.origin
      (Cubical.dualExteriorDifference D) =
        latticeOrientationSignTwist
          (sourceRealLatticeCoboundary
            (sourcePhysicalDualZeroExtension R.origin
              (dualOrientationSignTwist D))) := by
    simpa [LinearMap.comp_apply] using hbridge
  have hphysical : sourcePhysicalDualZeroExtension R.origin
      (Cubical.dualExteriorDifference D) = 0 := by
    rw [hbridge', htwist, hboundary]
    simp
  ext c
  have hc := congrArg (fun q : Cubical.RealLatticeChain 4 =>
    q (Cubical.dualCellEmbedding (B := R.side) R.origin c)) hphysical
  simpa [sourcePhysicalDualZeroExtension_apply_embedding] using hc

omit [SourceRelationEquivalenceGate] in
theorem untwistedCurrent_integerClosed (R : RectBox4)
    (J : SourceClosedIntegerCurrent R) :
    integerDualExteriorDifference
      (Finsupp.embDomain sourceDualTwoEmbedding (untwistedCurrent R J)) = 0 := by
  have hcast := untwistedCurrent_dualClosed R J
  have hcastEmb : castIntegerFinsupp
      (Finsupp.embDomain sourceDualTwoEmbedding (untwistedCurrent R J)) =
        sourceDualTwoToChain
          (Gaussian.finsuppToEuclidean
            (castIntegerFinsupp (untwistedCurrent R J))) := by
    rw [cast_embDomain_integer]
    simp [sourceDualTwoToChain, LinearMap.comp_apply,
      euclideanToFinsupp_finsuppToEuclidean, embedDualSubtype_eq_embDomain]
  have hzero : castIntegerFinsupp
      (integerDualExteriorDifference
        (Finsupp.embDomain sourceDualTwoEmbedding (untwistedCurrent R J))) = 0 := by
    rw [castIntegerDualExteriorDifference, hcastEmb]
    exact hcast
  ext c
  have hc := congrArg (fun q : Cubical.DualRealChain 4 R.side => q c) hzero
  have hreal : ((integerDualExteriorDifference
      (Finsupp.embDomain sourceDualTwoEmbedding (untwistedCurrent R J)) c : ℤ) : ℝ) = 0 := by
    simpa [castIntegerFinsupp, Finsupp.mapRange_apply] using hc
  exact_mod_cast hreal

omit [SourceRelationEquivalenceGate] in
theorem sourceDualTwoFilling (R : RectBox4)
    (J : SourceClosedIntegerCurrent R) :
    ∃ α : IntegerDualField R,
      integerLatticeCurl R α = J.1 := by
  let q₂ := untwistedCurrent R J
  let qDual : Gaussian.DualIntegerChain R.side :=
    Finsupp.embDomain sourceDualTwoEmbedding q₂
  let p : Cubical.Chain 4 R.side := integerStarMapInverse qDual
  have hdualSupport : (qDual.support : Set (Cubical.DualCell 4 R.side)) ⊆
      Set.range sourceDualTwoEmbedding := by
    intro c hc
    rw [Finsupp.support_embDomain] at hc
    rcases Finset.mem_map.mp hc with ⟨f, hf, rfl⟩
    exact ⟨f, rfl⟩
  have hpHomogeneous : Cubical.homogeneousSupport p 2 := by
    intro c hc
    have hdual : Cubical.primalDualCellEquiv c ∈ qDual.support := by
      rw [Finsupp.mem_support_iff] at hc ⊢
      change qDual (Cubical.primalDualCellEquiv c) ≠ 0
      simpa [p, integerStarMapInverse, Finsupp.equivMapDomain_apply] using hc
    obtain ⟨f, hf⟩ := hdualSupport hdual
    have hdeg : Cubical.dualCellDegree
        (Cubical.primalDualCellEquiv c) = 2 := by
      rw [← hf]
      exact f.2
    have hstar := Cubical.star_complementary_degree c
    rw [hdeg] at hstar
    omega
  have hpPositive : Cubical.positiveDegreeSupport p := by
    intro c hc
    rw [hpHomogeneous c hc]
    omega
  have hpCycle : Cubical.boundary p = 0 := by
    have hzero := untwistedCurrent_integerClosed R J
    change integerStarMap (Cubical.boundary (integerStarMapInverse qDual)) = 0 at hzero
    have h := congrArg integerStarMapInverse hzero
    simpa [integerStarMapInverse_starMap] using h
  let anchor : Cubical.Anchor 4 R.side :=
    fun i => ⟨0, Nat.zero_lt_succ _⟩
  have _hexistence := Cubical.exists_boundary_eq_of_cycle_positive
    anchor p hpPositive hpCycle
  have hfill : Cubical.boundary
      (Cubical.fillingOperator anchor p) = p := by
    have hprism := congrArg
      (fun T : Cubical.Chain 4 R.side →ₗ[ℤ] Cubical.Chain 4 R.side => T p)
      (Cubical.orderedPrism_identity anchor (List.finRange 4))
    change Cubical.boundary
        (Cubical.orderedPrismFilling anchor (List.finRange 4) p) +
      Cubical.orderedPrismFilling anchor (List.finRange 4)
        (Cubical.boundary p) =
      p - Cubical.orderedPrismProjection anchor (List.finRange 4) p at hprism
    have hproj := Cubical.orderedPrismProjection_kills_positiveSupport
      anchor p hpPositive
    rw [hpCycle, map_zero, hproj, sub_zero, add_zero] at hprism
    simpa [Cubical.fillingOperator] using hprism
  have hfillHomogeneous : Cubical.homogeneousSupport
      (Cubical.fillingOperator anchor p) 3 :=
    Cubical.fillingOperator_homogeneousSupport anchor p 2 hpHomogeneous
  let vDual : Gaussian.DualIntegerChain R.side :=
    integerStarMap (Cubical.fillingOperator anchor p)
  have hvSupport : (vDual.support : Set (Cubical.DualCell 4 R.side)) ⊆
      Set.range sourceDualOneEmbedding := by
    intro c hc
    have hprimal : Cubical.primalDualCellEquiv.symm c ∈
        (Cubical.fillingOperator anchor p).support := by
      simpa [vDual, integerStarMap, Finsupp.equivMapDomain_apply] using hc
    have hthree := hfillHomogeneous (Cubical.primalDualCellEquiv.symm c) hprimal
    have hstar := Cubical.star_complementary_degree
      (Cubical.primalDualCellEquiv.symm c)
    rw [Cubical.primalDualCellEquiv.apply_symm_apply] at hstar
    rw [hthree] at hstar
    have hcDegree : Cubical.dualCellDegree c = 1 := by omega
    exact ⟨⟨c, hcDegree⟩, rfl⟩
  let q₁ : SourceDualOneCells R.side →₀ ℤ :=
    Finsupp.comapDomain sourceDualOneEmbedding vDual
      sourceDualOneEmbedding.injective.injOn
  have hq₁Embed : Finsupp.embDomain sourceDualOneEmbedding q₁ = vDual := by
    dsimp [q₁]
    exact Finsupp.embDomain_comapDomain hvSupport
  have hintegerExact : integerDualExteriorDifference
      (sourceIntegerDualOneChain q₁) = qDual := by
    change integerStarMap (Cubical.boundary
      (integerStarMapInverse (sourceIntegerDualOneChain q₁))) = qDual
    rw [show sourceIntegerDualOneChain q₁ = vDual by
      exact hq₁Embed]
    rw [integerStarMapInverse_starMap, hfill]
    exact integerStarMap_starMapInverse qDual
  let x : EuclideanSpace ℝ (SourceDualOneCells R.side) :=
    Gaussian.finsuppToEuclidean (castIntegerFinsupp q₁)
  let y : EuclideanSpace ℝ (SourceDualTwoCells R.side) :=
    Gaussian.finsuppToEuclidean (castIntegerFinsupp q₂)
  have hrealExact : Cubical.dualExteriorDifference
      (sourceDualOneToChain x) = sourceDualTwoToChain y := by
    have hcast := congrArg castIntegerFinsupp hintegerExact
    rw [castIntegerDualExteriorDifference,
      castSourceIntegerDualOneChain] at hcast
    have hxChain : sourceDualOneToChain x =
        embedDualSubtype sourceDualOneEmbedding (castIntegerFinsupp q₁) := by
      simp [x, sourceDualOneToChain, LinearMap.comp_apply,
        euclideanToFinsupp_finsuppToEuclidean]
    have hyChain : sourceDualTwoToChain y =
        Finsupp.embDomain sourceDualTwoEmbedding (castIntegerFinsupp q₂) := by
      simp [y, sourceDualTwoToChain, LinearMap.comp_apply,
        euclideanToFinsupp_finsuppToEuclidean, embedDualSubtype_eq_embDomain]
    have hqDualCast : castIntegerFinsupp qDual = sourceDualTwoToChain y := by
      dsimp [qDual]
      rw [cast_embDomain_integer]
      exact hyChain.symm
    rw [← hxChain, hqDualCast] at hcast
    exact hcast
  have hD₁ : sourceDualD₁ x = y := by
    apply sourceDualTwoToChain_injective
    rw [sourceDualD₁_embed_eq_derivative]
    exact hrealExact
  let α : IntegerDualField R := fun e =>
    sourceIntegerOrientationSign e * q₁ e
  have hinput : sourceCurlInput R α = x := by
    ext e
    rw [sourceCurlInput_eq_signedField]
    change ((sourceIntegerSignTwist α e : ℤ) : ℝ) =
      Gaussian.finsuppToEuclidean (castIntegerFinsupp q₁) e
    simp only [sourceIntegerSignTwist, α,
      Gaussian.finsuppToEuclidean_apply, castIntegerFinsupp,
      Finsupp.mapRange_apply]
    have hsquare := sourceIntegerOrientationSign_sq e
    have hint : sourceIntegerOrientationSign e *
        (sourceIntegerOrientationSign e * q₁ e) = q₁ e := by
      calc
        sourceIntegerOrientationSign e *
            (sourceIntegerOrientationSign e * q₁ e) =
            (sourceIntegerOrientationSign e ^ 2) * q₁ e := by ring
        _ = q₁ e := by rw [hsquare]; norm_num
    exact_mod_cast hint
  have hcurlCast : Cubical.castLatticeChain (integerLatticeCurl R α) =
      Cubical.castLatticeChain J.1 := by
    calc
      Cubical.castLatticeChain (integerLatticeCurl R α) =
          latticeOrientationSignTwist
            (sourcePhysicalDualZeroExtension R.origin
              (sourceDualTwoToChain
                (sourceDualD₁ (sourceCurlInput R α)))) :=
        literalCurl_cast_eq_sourceCurl R α
      _ = latticeOrientationSignTwist
          (sourcePhysicalDualZeroExtension R.origin
            (sourceDualTwoToChain y)) := by rw [hinput, hD₁]
      _ = latticeOrientationSignTwist
          (latticeOrientationSignTwist (Cubical.castLatticeChain J.1)) := by
        have hrepr : sourcePhysicalDualZeroExtension R.origin
            (sourceDualTwoToChain y) =
            latticeOrientationSignTwist (Cubical.castLatticeChain J.1) := by
          rw [sourceDualTwoPhysicalChain_repr]
          simpa only [y, Gaussian.euclideanToFinsupp_finsuppToEuclidean] using
            untwistedCurrent_physical_repr R J
        exact congrArg latticeOrientationSignTwist hrepr
      _ = Cubical.castLatticeChain J.1 := latticeOrientationSignTwist_involutive _
  refine ⟨α, ?_⟩
  ext c
  have hc := congrArg (fun q : Cubical.RealLatticeChain 4 => q c) hcurlCast
  have hreal : ((integerLatticeCurl R α c : ℤ) : ℝ) = (J.1 c : ℝ) := by
    simpa [Cubical.castLatticeChain, Finsupp.mapRange_apply] using hc
  exact_mod_cast hreal

theorem integerGaugeQuotient_toSourceClosedCurrent_injective (R : RectBox4) :
    Function.Injective (integerGaugeQuotient_toSourceClosedCurrent R) := by
  intro q q'
  refine Quotient.inductionOn₂ q q' ?_
  intro α α' h
  apply Quotient.sound
  have hval := congrArg Subtype.val h
  have hcurl : integerLatticeCurl R α = integerLatticeCurl R α' := by
    simpa [integerGaugeQuotient_toSourceClosedCurrent,
      integerLatticeCurl_mem_sourceClosedIntegerCurrent] using hval
  exact sourceCurl_eq_implies_gauge R α α' hcurl.symm

theorem integerGaugeQuotient_toSourceClosedCurrent_surjective (R : RectBox4) :
    Function.Surjective (integerGaugeQuotient_toSourceClosedCurrent R) := by
  intro J
  obtain ⟨α, hcurl⟩ := sourceDualTwoFilling R J
  refine ⟨Quotient.mk _ α, ?_⟩
  apply Subtype.ext
  exact hcurl

noncomputable def sourceGaugeClass_closedCurrentEquiv (R : RectBox4) :
    IntegerDualGaugeQuotient R ≃ SourceClosedIntegerCurrent R :=
  Equiv.ofBijective (integerGaugeQuotient_toSourceClosedCurrent R)
    ⟨integerGaugeQuotient_toSourceClosedCurrent_injective R,
      integerGaugeQuotient_toSourceClosedCurrent_surjective R⟩


end FroehlichSpencer.FS82.Surface.GaugeCurrentEquivalence
end
