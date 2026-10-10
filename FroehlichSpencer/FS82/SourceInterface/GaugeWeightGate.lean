module

public import FroehlichSpencer.FS82.SourceInterface.GaugeAdapter
public import FroehlichSpencer.FS82.Gaussian.LatticeComplex
public import FroehlichSpencer.FS82.Gaussian.IntegerExactness
public import FroehlichSpencer.FS82.Gaussian.LatticeOperator

@[expose] public section

open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Gaussian
open FroehlichSpencer.FS82.Surface

namespace FroehlichSpencer.FS82.Surface

private theorem sourcePotentialVertexSupport (ζ : SourceIntegerPotential) :
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

private noncomputable def sourcePotentialVertexFinsupp
    (ζ : SourceIntegerPotential) : LatticeVertices4 →₀ ℤ :=
  Finsupp.comapDomain latticePotentialVertexEmbedding ζ.1
    latticePotentialVertexEmbedding.injective.injOn

private theorem sourcePotentialVertexFinsupp_reconstruct
    (ζ : SourceIntegerPotential) :
    latticePotentialVertexFinsupp (sourcePotentialVertexFinsupp ζ) = ζ.1 := by
  dsimp [sourcePotentialVertexFinsupp, latticePotentialVertexFinsupp]
  exact Finsupp.embDomain_comapDomain (sourcePotentialVertexSupport ζ)

private theorem sourcePotentialGradient_eq_coboundary
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

private theorem lambdaStarIntegerZeroExtension_cubical (R : RectBox4)
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
  induction q using Finsupp.induction_linear with
  | zero => simp
  | add q r hq hr => rw [map_add, map_add, hq, hr]
  | single e z =>
      simp only [Finsupp.linearCombination_single]
      have hfun : (lambdaStarEmbeddingC1 R : DualLinks R → LatticeCell) =
          (Cubical.lambdaStarEmbedding (B := R.side) R.origin :
            DualLinks R → LatticeCell) :=
        congrArg Function.Embedding.toFun (c1LambdaStar_bridge R)
      exact congrArg (fun f : DualLinks R → LatticeCell =>
        z • Finsupp.single (f e) (1 : ℤ)) hfun

private theorem latticeCoboundary_sq_zero_of_source_support
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

theorem integerLatticeCurl_respectsGauge
    (R : RectBox4) (α α' : IntegerDualField R)
    (hα : sourceIntegerGaugeRelation R α α') :
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
  have hdoubleSurface :
      latticeCoboundary (Cubical.latticeCoboundary ζ.1) = 0 := hdouble
  unfold integerLatticeCurl
  rw [hfield]
  rw [map_add (lambdaStarIntegerZeroExtension R)]
  rw [map_add (latticeCoboundary)]
  rw [hzeroSurface, hdoubleSurface]
  simp

theorem integerDualFieldWeight_respectsGauge_internal
    (R : RectBox4) (β : ℝ) (hβ : 0 < β)
    (α α' : IntegerDualField R)
    (hα : sourceIntegerGaugeRelation R α α') :
    integerDualFieldWeight R β hβ α = integerDualFieldWeight R β hβ α' := by
  unfold integerDualFieldWeight
  rw [integerLatticeCurl_respectsGauge R α α' hα]


end FroehlichSpencer.FS82.Surface
end
