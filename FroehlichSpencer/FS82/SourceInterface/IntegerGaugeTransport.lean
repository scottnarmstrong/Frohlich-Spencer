module
public import FroehlichSpencer.FS82.SourceInterface.GaugeWeightGate
public import FroehlichSpencer.FS82.SourceInterface.SourceModels
public import FroehlichSpencer.FS82.Gaussian.LatticeBridgeHigher
public import FroehlichSpencer.FS82.Cubical.IntegerExactness

@[expose] public section
open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Gaussian
open FroehlichSpencer.FS82.Surface
open FroehlichSpencer.FS82.SourceModels.IntegerDualModel

namespace FroehlichSpencer.FS82.Surface.IntegerGaugeTransport

noncomputable def linksEquivSource (R : RectBox4) : DualLinks R ≃ SourceDualOneCells R.side :=
  Equiv.refl _

noncomputable def plaquettesEquivSource (R : RectBox4) : DualPlaquettes R ≃ SourceDualTwoCells R.side :=
  Equiv.refl _

variable [SourceRelationEquivalenceGate]

omit [SourceRelationEquivalenceGate] in
noncomputable def sourceFieldOfLiteral (R : RectBox4)
    (α : IntegerDualField R) : SourceDualOneCells R.side →₀ ℤ :=
  Finsupp.equivFunOnFinite.symm (fun e => α ((linksEquivSource R).symm e))

omit [SourceRelationEquivalenceGate] in
theorem sourceFieldOfLiteral_apply (R : RectBox4)
    (α : IntegerDualField R) (e : SourceDualOneCells R.side) :
    sourceFieldOfLiteral R α e = α ((linksEquivSource R).symm e) := by
  simp [sourceFieldOfLiteral]

omit [SourceRelationEquivalenceGate] in
theorem lambdaStarIntegerZeroExtension_cubical (R : RectBox4)
    (q : DualLinks R →₀ ℤ) :
    lambdaStarIntegerZeroExtension R q =
      Cubical.lambdaStarZeroExtension (B := R.side) R.origin q := by
  classical
  change Finsupp.linearCombination ℤ
      (fun e : DualLinks R =>
        Finsupp.single (lambdaStarEmbeddingC1 R e) (1 : ℤ)) q =
    Finsupp.linearCombination ℤ
      (fun e : DualLinks R => Finsupp.single
        (Cubical.lambdaStarEmbedding (B := R.side) R.origin e) (1 : ℤ)) q
  have hfun : (lambdaStarEmbeddingC1 R : DualLinks R → LatticeCell) =
      (Cubical.lambdaStarEmbedding (B := R.side) R.origin :
        DualLinks R → LatticeCell) :=
    congrArg Function.Embedding.toFun (c1LambdaStar_bridge R)
  exact congrArg (fun f : DualLinks R → LatticeCell =>
    Finsupp.linearCombination ℤ (fun e => Finsupp.single (f e) 1) q) hfun

noncomputable def literalFieldRealVector (R : RectBox4)
    (α : IntegerDualField R) : EuclideanSpace ℝ (SourceDualOneCells R.side) :=
  Gaussian.finsuppToEuclidean (castIntegerFinsupp (sourceFieldOfLiteral R α))

noncomputable def sourceCurlInput (R : RectBox4)
    (α : IntegerDualField R) : EuclideanSpace ℝ (SourceDualOneCells R.side) :=
  sourceDualTLinear (literalFieldRealVector R α)

omit [SourceRelationEquivalenceGate] in
theorem sourceCurlInput_twist_reconstruct (R : RectBox4)
    (α : IntegerDualField R) :
    sourceDualTLinear (sourceCurlInput R α) = literalFieldRealVector R α :=
  sourceDualTLinear_apply_apply _

omit [SourceRelationEquivalenceGate] in
theorem literalCurl_cast_eq_sourceCurl (R : RectBox4)
    (α : IntegerDualField R) :
    Cubical.castLatticeChain (integerLatticeCurl R α) =
      latticeOrientationSignTwist
        (sourcePhysicalDualZeroExtension (B := R.side) R.origin
          (sourceDualTwoToChain
            (sourceDualD₁ (sourceCurlInput R α)))) := by
  let qI := sourceFieldOfLiteral R α
  let qR := castIntegerFinsupp qI
  let a := literalFieldRealVector R α
  let x := sourceCurlInput R α
  have hvec : Gaussian.euclideanToFinsupp a = qR := by
    change Gaussian.euclideanToFinsupp
      (Gaussian.finsuppToEuclidean (castIntegerFinsupp qI)) = castIntegerFinsupp qI
    exact euclideanToFinsupp_finsuppToEuclidean _
  have hT : sourceDualTMap (Gaussian.euclideanToFinsupp x) = qR := by
    calc
      sourceDualTMap (Gaussian.euclideanToFinsupp x) =
          Gaussian.euclideanToFinsupp (sourceDualTLinear x) := by
            simp [sourceDualTLinear, LinearMap.comp_apply]
      _ = Gaussian.euclideanToFinsupp a := by
            rw [sourceCurlInput_twist_reconstruct]
      _ = qR := hvec
  have hext :
      sourcePhysicalDualZeroExtension (B := R.side) R.origin
          (dualOrientationSignTwist (sourceDualOneToChain x)) =
        Cubical.lambdaStarRealZeroExtension (B := R.side) R.origin qR := by
    rw [sourcePhysicalDualZeroExtension_sourceDualTMap]
    exact congrArg (Cubical.lambdaStarRealZeroExtension (B := R.side) R.origin) hT
  unfold integerLatticeCurl
  rw [lambdaStarIntegerZeroExtension_cubical]
  calc
    Cubical.castLatticeChain
        (Cubical.latticeCoboundary
          (Cubical.lambdaStarZeroExtension (B := R.side) R.origin qI)) =
        sourceRealLatticeCoboundary
          (Cubical.castLatticeChain
            (Cubical.lambdaStarZeroExtension (B := R.side) R.origin qI)) := by
              exact (sourceRealLatticeCoboundary_cast _).symm
    _ = sourceRealLatticeCoboundary
          (Cubical.lambdaStarRealZeroExtension (B := R.side) R.origin qR) := by
            rw [castLambdaStarZeroExtension]
    _ = sourceRealLatticeCoboundary
          (sourcePhysicalDualZeroExtension (B := R.side) R.origin
            (dualOrientationSignTwist (sourceDualOneToChain x))) := by
            rw [hext]
    _ = latticeOrientationSignTwist
          (sourcePhysicalDualZeroExtension (B := R.side) R.origin
            (sourceDualTwoToChain (sourceDualD₁ x))) := by
            have hb := sourceDualD₁_physical_bridge R.origin x
            have hb' := congrArg latticeOrientationSignTwist hb
            rw [latticeOrientationSignTwist_involutive] at hb'
            exact hb'.symm


omit [SourceRelationEquivalenceGate] in
theorem sourcePotentialVertexSupport (ζ : SourceIntegerPotential) :
    (ζ.1.support : Set LatticeCell) ⊆ Set.range latticePotentialVertexEmbedding := by
  intro c hc
  have hv : sourceLatticeVertex c := by
    by_contra hnot
    exact (Finsupp.mem_support_iff.mp hc) (ζ.2 c hnot)
  let x : LatticeVertices4 := fun i => Sum.elim id id (c i)
  refine ⟨x, ?_⟩
  funext i
  cases hci : c i with
  | inl t => simp [latticePotentialVertexEmbedding, latticePotentialVertexCell, x, hci]
  | inr t =>
      have hi := hv i
      simp [hci] at hi

noncomputable def sourcePotentialVertexFinsupp
    (ζ : SourceIntegerPotential) : LatticeVertices4 →₀ ℤ :=
  Finsupp.comapDomain latticePotentialVertexEmbedding ζ.1
    latticePotentialVertexEmbedding.injective.injOn

omit [SourceRelationEquivalenceGate] in
theorem sourcePotentialVertexFinsupp_reconstruct
    (ζ : SourceIntegerPotential) :
    latticePotentialVertexFinsupp (sourcePotentialVertexFinsupp ζ) = ζ.1 := by
  dsimp [sourcePotentialVertexFinsupp, latticePotentialVertexFinsupp]
  exact Finsupp.embDomain_comapDomain (sourcePotentialVertexSupport ζ)

omit [SourceRelationEquivalenceGate] in
theorem sourcePotentialGradient_eq_coboundary
    (ζ : SourceIntegerPotential) (c : LatticeCell) :
    latticePotentialGradient (fun x => sourcePotentialVertexFinsupp ζ x) c =
      Cubical.latticeCoboundary ζ.1 c := by
  calc
    latticePotentialGradient (fun x => sourcePotentialVertexFinsupp ζ x) c =
        Cubical.latticeCoboundary
          (latticePotentialVertexFinsupp (sourcePotentialVertexFinsupp ζ)) c :=
      latticePotentialGradient_vertexFinsupp_eq_coboundary _ c
    _ = Cubical.latticeCoboundary ζ.1 c := by
      rw [sourcePotentialVertexFinsupp_reconstruct]

omit [SourceRelationEquivalenceGate] in
theorem latticeCoboundary_sq_zero_of_source_support
    (R : RectBox4) (ζ : SourceIntegerPotential)
    (hsupport : ((Cubical.latticeCoboundary ζ.1).support : Set LatticeCell) ⊆
      Set.range (Cubical.lambdaStarEmbedding (B := R.side) R.origin)) :
    Cubical.latticeCoboundary (Cubical.latticeCoboundary ζ.1) = 0 := by
  let p := sourcePotentialVertexFinsupp ζ
  have hgradientSupport : ∀ c : LatticeCell,
      latticePotentialGradient (fun x => p x) c ≠ 0 →
        c ∈ Set.range (lambdaStarEmbeddingC1 R) := by
    intro c hc
    have hdc : Cubical.latticeCoboundary ζ.1 c ≠ 0 := by
      rw [← sourcePotentialGradient_eq_coboundary ζ c]
      exact hc
    have hmem := hsupport (Finsupp.mem_support_iff.mpr hdc)
    rw [← lambdaStarEmbeddingC1_range_bridge R] at hmem
    exact hmem
  obtain ⟨γ₀, hsame, hfinite, hvertices, _hexterior, _hunique⟩ :=
    normalizeIntegerGaugePotential_connectedExterior_internal R (fun x => p x)
      hgradientSupport
  let p₀ : LatticeVertices4 →₀ ℤ := Finsupp.ofSupportFinite γ₀ hfinite
  have hp₀fun : (p₀ : LatticeVertices4 → ℤ) = γ₀ :=
    Finsupp.ofSupportFinite_coe
  let potential₀ : LatticeChain := latticePotentialVertexFinsupp p₀
  have hpotentialSupport : (potential₀.support : Set LatticeCell) ⊆
      Set.range (sourceDualZeroPhysicalEmbedding (B := R.side) R.origin) := by
    intro c hc
    have hc' : c ∈ (Finsupp.embDomain latticePotentialVertexEmbedding p₀).support := by
      simpa [potential₀, latticePotentialVertexFinsupp] using hc
    rw [Finsupp.support_embDomain] at hc'
    rcases Finset.mem_map.mp hc' with ⟨x, hx, rfl⟩
    have hx₀ : γ₀ x ≠ 0 := by
      have hx' : p₀ x ≠ 0 := Finsupp.mem_support_iff.mp hx
      rw [← congrFun hp₀fun x]
      exact hx'
    obtain ⟨v, hv⟩ := hvertices x hx₀
    refine ⟨v, ?_⟩
    change Cubical.dualCellEmbedding (B := R.side) R.origin v.1 =
      latticePotentialVertexCell x
    rw [← c1Cell_bridge R]
    exact hv
  let u : SourceDualZeroCells R.side →₀ ℤ :=
    Finsupp.comapDomain
      (sourceDualZeroPhysicalEmbedding (B := R.side) R.origin)
      potential₀
      (sourceDualZeroPhysicalEmbedding (B := R.side) R.origin).injective.injOn
  have hu : Finsupp.embDomain
      (sourceDualZeroPhysicalEmbedding (B := R.side) R.origin) u = potential₀ := by
    dsimp [u]
    exact Finsupp.embDomain_comapDomain hpotentialSupport
  have hpotential₀ :
      (sourceIntegerPotentialOfDualZero (B := R.side) R.origin u).1 = potential₀ := by
    rw [sourceIntegerPotentialOfDualZero_eq_embDomain]
    exact hu
  let x : EuclideanSpace ℝ (SourceDualZeroCells R.side) :=
    Gaussian.finsuppToEuclidean (castIntegerFinsupp u)
  have hcastPotential :
      Cubical.castLatticeChain potential₀ =
        sourcePhysicalDualZeroExtension (B := R.side) R.origin
          (sourceDualZeroToChain x) := by
    rw [← hpotential₀]
    simpa [x, sourceDualZeroToChain,
      dualOrientationSignTwist_embedSourceZero] using
      (castSourceIntegerPotentialOfDualZero (B := R.side) R.origin u)
  have hfirst :
      Cubical.lambdaStarRealZeroExtension (B := R.side) R.origin
          (Gaussian.euclideanToFinsupp
            ((latticeExactOneComplex (B := R.side) R.origin).d₀ x)) =
        sourceRealLatticeCoboundary (Cubical.castLatticeChain potential₀) := by
    rw [hcastPotential]
    exact sourceD0_physical_extension_eq_coboundary R x
  have hD₁D₀ : sourceDualD₁ (sourceDualD₀ x) = 0 := by
    have h := congrArg (fun T : EuclideanSpace ℝ (SourceDualZeroCells R.side) →ₗ[ℝ]
      EuclideanSpace ℝ (SourceDualTwoCells R.side) => T x)
        (sourceDualD₁_comp_D₀_zero (B := R.side))
    simpa [LinearMap.comp_apply] using h
  have hcurlD₀ :
      sourceRealLatticeCoboundary
          (sourcePhysicalDualZeroExtension (B := R.side) R.origin
            (dualOrientationSignTwist (sourceDualOneToChain (sourceDualD₀ x)))) = 0 := by
    have h := sourceDualD₁_coboundary_as_signed_embedding R.origin
      (sourceDualD₀ x)
    rw [hD₁D₀] at h
    simpa using h
  have hTbridge :
      Cubical.lambdaStarRealZeroExtension (B := R.side) R.origin
          (Gaussian.euclideanToFinsupp
            ((latticeExactOneComplex (B := R.side) R.origin).d₀ x)) =
        sourcePhysicalDualZeroExtension (B := R.side) R.origin
          (dualOrientationSignTwist (sourceDualOneToChain (sourceDualD₀ x))) := by
    have hT : Gaussian.euclideanToFinsupp
        ((latticeExactOneComplex (B := R.side) R.origin).d₀ x) =
          sourceDualTMap (Gaussian.euclideanToFinsupp (sourceDualD₀ x)) := by
      simp [latticeExactOneComplex, sourceDualTLinear, LinearMap.comp_apply]
    rw [hT]
    exact (sourcePhysicalDualZeroExtension_sourceDualTMap R.origin
      (sourceDualD₀ x)).symm
  have hsecond :
      sourceRealLatticeCoboundary
          (Cubical.castLatticeChain (Cubical.latticeCoboundary potential₀)) = 0 := by
    rw [← sourceRealLatticeCoboundary_cast potential₀, ← hfirst, hTbridge]
    exact hcurlD₀
  have hcastDouble :
      Cubical.castLatticeChain
          (Cubical.latticeCoboundary (Cubical.latticeCoboundary potential₀)) = 0 := by
    calc
      _ = sourceRealLatticeCoboundary
          (Cubical.castLatticeChain (Cubical.latticeCoboundary potential₀)) :=
        (sourceRealLatticeCoboundary_cast
          (Cubical.latticeCoboundary potential₀)).symm
      _ = 0 := hsecond
  have hdouble₀ :
      Cubical.latticeCoboundary (Cubical.latticeCoboundary potential₀) = 0 := by
    ext c
    have hc := congrArg (fun q : Cubical.RealLatticeChain 4 => q c) hcastDouble
    exact_mod_cast (by simpa [Cubical.castLatticeChain] using hc)
  have hderivative :
      Cubical.latticeCoboundary potential₀ =
        Cubical.latticeCoboundary ζ.1 := by
    ext c
    calc
      Cubical.latticeCoboundary potential₀ c =
          latticePotentialGradient (fun y => p₀ y) c := by
        exact (latticePotentialGradient_vertexFinsupp_eq_coboundary p₀ c).symm
      _ = latticePotentialGradient γ₀ c := by
        rw [hp₀fun]
      _ = latticePotentialGradient (fun y => p y) c := hsame c
      _ = Cubical.latticeCoboundary ζ.1 c :=
        sourcePotentialGradient_eq_coboundary ζ c
  have hdouble :
      Cubical.latticeCoboundary (Cubical.latticeCoboundary ζ.1) = 0 := by
    calc
      Cubical.latticeCoboundary (Cubical.latticeCoboundary ζ.1) =
          Cubical.latticeCoboundary (Cubical.latticeCoboundary potential₀) := by
        exact congrArg Cubical.latticeCoboundary hderivative.symm
      _ = 0 := hdouble₀
  exact hdouble

omit [SourceRelationEquivalenceGate] in
theorem dualExteriorDifference_square_zero {B : SourceBox} :
    (Cubical.dualExteriorDifference (d := 4) (B := B)).comp
      (Cubical.dualExteriorDifference (d := 4) (B := B)) = 0 := by
  apply LinearMap.ext
  intro q
  change Cubical.starMap
      (Cubical.realBoundary
        (Cubical.starMapInverse
          (Cubical.starMap
            (Cubical.realBoundary (Cubical.starMapInverse q))))) = 0
  rw [Cubical.starMapInverse_starMap]
  have hb := congrArg
    (fun T : Cubical.RealChain 4 B →ₗ[ℝ] Cubical.RealChain 4 B =>
      T (Cubical.starMapInverse q))
    (realBoundary_square_zero (B := B))
  simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hb
  rw [hb]
  simp

omit [SourceRelationEquivalenceGate] in
theorem sourceCurl_dualExterior_closed (R : RectBox4)
    (α : IntegerDualField R) :
    Cubical.dualExteriorDifference
      (sourceDualTwoToChain (sourceDualD₁ (sourceCurlInput R α))) = 0 := by
  have hderiv := sourceDualD₁_embed_eq_derivative (sourceCurlInput R α)
  calc
    Cubical.dualExteriorDifference
        (sourceDualTwoToChain (sourceDualD₁ (sourceCurlInput R α))) =
        Cubical.dualExteriorDifference
          (Cubical.dualExteriorDifference (sourceDualOneToChain (sourceCurlInput R α))) := by
            rw [hderiv]
    _ = 0 := by
        have hz := LinearMap.congr_fun
          (dualExteriorDifference_square_zero (B := R.side))
          (sourceDualOneToChain (sourceCurlInput R α))
        simpa [LinearMap.comp_apply] using hz

omit [SourceRelationEquivalenceGate] in
theorem sourceCurl_physical_closed (R : RectBox4)
    (α : IntegerDualField R) :
    sourceRealLatticeCoboundary
      (sourcePhysicalDualZeroExtension (B := R.side) R.origin
        (dualOrientationSignTwist
          (sourceDualTwoToChain (sourceDualD₁ (sourceCurlInput R α))))) = 0 := by
  let y := sourceDualTwoToChain (sourceDualD₁ (sourceCurlInput R α))
  have hphys := LinearMap.congr_fun
    (sourcePhysicalDualZeroExtension_comp_dualExteriorDifference R.origin) y
  have htwist : latticeOrientationSignTwist
      (sourceRealLatticeCoboundary
        (sourcePhysicalDualZeroExtension (B := R.side) R.origin
          (dualOrientationSignTwist y))) = 0 := by
    simpa [y, sourceCurl_dualExterior_closed R α] using hphys.symm
  have hzero := congrArg latticeOrientationSignTwist htwist
  rw [latticeOrientationSignTwist_involutive] at hzero
  exact hzero

omit [SourceRelationEquivalenceGate] in
theorem sourceCurlCast_closed (R : RectBox4)
    (α : IntegerDualField R) :
    sourceRealLatticeCoboundary
      (Cubical.castLatticeChain (integerLatticeCurl R α)) = 0 := by
  rw [literalCurl_cast_eq_sourceCurl]
  rw [sourcePhysicalDualZeroExtension_twist_commutes]
  exact sourceCurl_physical_closed R α

omit [SourceRelationEquivalenceGate] in
theorem integerCurl_closed (R : RectBox4) (α : IntegerDualField R) :
    Cubical.latticeCoboundary (integerLatticeCurl R α) = 0 := by
  have hcast := sourceRealLatticeCoboundary_cast
    (integerLatticeCurl R α)
  have hcastZero : Cubical.castLatticeChain
      (Cubical.latticeCoboundary (integerLatticeCurl R α)) = 0 := by
    calc
      Cubical.castLatticeChain
          (Cubical.latticeCoboundary (integerLatticeCurl R α)) =
          sourceRealLatticeCoboundary
            (Cubical.castLatticeChain (integerLatticeCurl R α)) := hcast.symm
      _ = 0 := sourceCurlCast_closed R α
  ext c
  have hc := congrArg (fun q : Cubical.RealLatticeChain 4 => q c) hcastZero
  have hc' : ((Cubical.latticeCoboundary (integerLatticeCurl R α) c : ℤ) : ℝ) = 0 := by
    simpa [Cubical.castLatticeChain] using hc
  exact_mod_cast hc'


omit [SourceRelationEquivalenceGate] in
theorem integerCurl_support_plaquettes (R : RectBox4)
    (α : IntegerDualField R) (c : LatticeCell)
    (hc : c ∈ (integerLatticeCurl R α).support) :
    ∃ p : DualPlaquettes R, dualCellEmbeddingC1 R p.1 = c := by
  by_contra hnot
  have hout : c ∉ Set.range (sourcePhysicalDualTwoEmbedding (B := R.side) R.origin) := by
    intro hrange
    rcases hrange with ⟨f, hf⟩
    apply hnot
    refine ⟨(plaquettesEquivSource R).symm f, ?_⟩
    rw [c1Cell_bridge R]
    change Cubical.dualCellEmbedding (B := R.side) R.origin f.1 = c
    change Cubical.dualCellEmbedding (B := R.side) R.origin f.1 = c at hf
    exact hf
  have hvanish := sourceDualTwoToChain_physical_vanishes_outside R.origin
    (sourceDualD₁ (sourceCurlInput R α)) c hout
  have hcast : Cubical.castLatticeChain (integerLatticeCurl R α) c = 0 := by
    rw [literalCurl_cast_eq_sourceCurl, latticeOrientationSignTwist_apply]
    simp [hvanish]
  have hcoeff : ((integerLatticeCurl R α c : ℤ) : ℝ) = 0 := by
    simpa [Cubical.castLatticeChain] using hcast
  have hzero : integerLatticeCurl R α c = 0 := Int.cast_eq_zero.mp hcoeff
  exact (Finsupp.mem_support_iff.mp hc) hzero

noncomputable def integerLatticeCurl_mem_sourceClosedIntegerCurrent (R : RectBox4)
    (α : IntegerDualField R) : SourceClosedIntegerCurrent R :=
  ⟨integerLatticeCurl R α, integerCurl_closed R α,
    integerCurl_support_plaquettes R α⟩


omit [SourceRelationEquivalenceGate] in
theorem integerLatticeCurl_respectsGauge (R : RectBox4)
    (α α' : IntegerDualField R) (hα : sourceIntegerGaugeRelation R α α') :
    integerLatticeCurl R α' = integerLatticeCurl R α := by
  have hsource :=
    (sourceIntegerGaugeRelation_iff_sourceExactShiftSupportCondition226_internal R α α').mp hα
  rcases hsource with ⟨ζ, hsupport, hshift⟩
  have hdouble := latticeCoboundary_sq_zero_of_source_support R ζ hsupport
  have hdiff (e : DualLinks R) :
      α' e - α e = Cubical.latticeCoboundary ζ.1
        (Cubical.lambdaStarEmbedding (B := R.side) R.origin e) := by
    have hsign : sourceIntegerOrientationSign e *
        (sourceIntegerSignTwist α' e - sourceIntegerSignTwist α e) =
          α' e - α e := by
      simp only [sourceIntegerSignTwist]
      have hsquare := sourceIntegerOrientationSign_sq e
      calc
        sourceIntegerOrientationSign e *
            (sourceIntegerOrientationSign e * α' e -
              sourceIntegerOrientationSign e * α e) =
            sourceIntegerOrientationSign e ^ 2 * (α' e - α e) := by ring
        _ = α' e - α e := by rw [hsquare]; ring
    exact hsign.symm.trans (hshift e)
  let qdiff : DualLinks R →₀ ℤ :=
    Finsupp.equivFunOnFinite.symm (fun e => α' e - α e)
  let qdiffC : Cubical.LambdaStarChain R.side :=
    Finsupp.equivFunOnFinite.symm
      (fun e : Cubical.LambdaStarLinks R.side => α' e - α e)
  have hqdiff : qdiff = qdiffC := by
    ext e
    change (Finsupp.equivFunOnFinite.symm
        (fun x : DualLinks R => α' x - α x)) e =
      (Finsupp.equivFunOnFinite.symm
        (fun x : DualLinks R => α' x - α x)) e
    rfl
  have hzero :
      Cubical.lambdaStarZeroExtension (B := R.side) R.origin qdiffC =
        Cubical.latticeCoboundary ζ.1 := by
    ext c
    by_cases hc : c ∈ Set.range (Cubical.lambdaStarEmbedding (B := R.side) R.origin)
    · obtain ⟨e, rfl⟩ := hc
      rw [Cubical.lambdaStarZeroExtension_eq_embDomain]
      calc
        (Finsupp.embDomain (Cubical.lambdaStarEmbedding (B := R.side) R.origin)
            qdiffC) (Cubical.lambdaStarEmbedding (B := R.side) R.origin e) =
            qdiffC e := Finsupp.embDomain_apply_self
              (Cubical.lambdaStarEmbedding (B := R.side) R.origin) qdiffC e
        _ = Cubical.latticeCoboundary ζ.1
            (Cubical.lambdaStarEmbedding (B := R.side) R.origin e) := by
          have heval : qdiffC e = α' e - α e := by
            exact congrFun (Finsupp.coe_equivFunOnFinite_symm
              (fun e : Cubical.LambdaStarLinks R.side => α' e - α e)) e
          rw [heval]
          exact hdiff e
    · have hleft := Cubical.lambdaStarZeroExtension_vanishes_outside
        (B := R.side) R.origin qdiffC c hc
      have hright : Cubical.latticeCoboundary ζ.1 c = 0 := by
        by_contra hne
        exact hc (hsupport (Finsupp.mem_support_iff.mpr hne))
      simp [hleft, hright]
  have hfield :
      Finsupp.equivFunOnFinite.symm α' =
        Finsupp.equivFunOnFinite.symm α + qdiff := by
    ext e
    simp [qdiff]
  have hzeroSurface :
      lambdaStarIntegerZeroExtension R qdiff = Cubical.latticeCoboundary ζ.1 := by
    calc
      lambdaStarIntegerZeroExtension R qdiff =
          Cubical.lambdaStarZeroExtension (B := R.side) R.origin qdiffC := by
        rw [lambdaStarIntegerZeroExtension_cubical R qdiff, hqdiff]
      _ = Cubical.latticeCoboundary ζ.1 := hzero
  calc
    integerLatticeCurl R α' =
        Cubical.latticeCoboundary
          (lambdaStarIntegerZeroExtension R (Finsupp.equivFunOnFinite.symm α')) := rfl
    _ = Cubical.latticeCoboundary
          (lambdaStarIntegerZeroExtension R
            (Finsupp.equivFunOnFinite.symm α + qdiff)) := by rw [hfield]
    _ = Cubical.latticeCoboundary
          (lambdaStarIntegerZeroExtension R (Finsupp.equivFunOnFinite.symm α) +
            lambdaStarIntegerZeroExtension R qdiff) := by rw [map_add]
    _ = Cubical.latticeCoboundary
          (lambdaStarIntegerZeroExtension R (Finsupp.equivFunOnFinite.symm α) +
            Cubical.latticeCoboundary ζ.1) := by rw [hzeroSurface]
    _ = Cubical.latticeCoboundary
          (lambdaStarIntegerZeroExtension R (Finsupp.equivFunOnFinite.symm α)) := by
            rw [map_add, hdouble]
            simp


noncomputable def integerGaugeQuotient_toSourceClosedCurrent (R : RectBox4) :
    IntegerDualGaugeQuotient R → SourceClosedIntegerCurrent R :=
  Quotient.lift (integerLatticeCurl_mem_sourceClosedIntegerCurrent R)
    (fun α α' h => Subtype.ext (integerLatticeCurl_respectsGauge R α α' h).symm)


end FroehlichSpencer.FS82.Surface.IntegerGaugeTransport
end
