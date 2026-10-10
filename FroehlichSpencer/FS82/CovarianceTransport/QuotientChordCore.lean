module
public import FroehlichSpencer.FS82.SourceInterface.SourceTheorems
public import FroehlichSpencer.FS82.SourceInterface.GaussianExistence
public import FroehlichSpencer.FS82.Root.SourceMoment
@[expose] public section
open scoped BigOperators
open FroehlichSpencer.FS82.Surface
open FroehlichSpencer.FS82.SourceModels.IntegerDualModel
open FroehlichSpencer.FS82.Moment.SourceConstructor
open FroehlichSpencer.FS82.Poisson
open FroehlichSpencer.FS82.Gaussian
open FroehlichSpencer.FS82.Surface.IntegerGaugeTransport
namespace FroehlichSpencer.FS82.SourceCovarianceBridge
open Classical

theorem integerTreePotential_cast {V E : Type*} [DecidableEq V] [DecidableEq E]
    (T : RootedTreeGauge V E) (a : E → ℤ) (x : V) :
    ((RootedTreeGauge.treePotential T a x : ℤ) : ℝ) =
      RootedTreeGauge.treePotential T (fun e => (a e : ℝ)) x := by
  have hdepth : ∀ n, ∀ x, T.depth x = n →
      ((RootedTreeGauge.treePotential T a x : ℤ) : ℝ) =
        RootedTreeGauge.treePotential T (fun e => (a e : ℝ)) x := by
    intro n
    induction n with
    | zero =>
        intro x hx
        by_cases hroot : x = T.root
        · subst x
          simp
        · have hpos := T.depth_pos hroot
          omega
    | succ n ih =>
        intro x hx
        by_cases hroot : x = T.root
        · subst x
          have hbad : T.depth T.root = Nat.succ n := by simpa using hx
          rw [T.depth_root] at hbad
          omega
        · rw [RootedTreeGauge.treePotential_parent T a hroot,
            RootedTreeGauge.treePotential_parent T (fun e => (a e : ℝ)) hroot]
          push_cast
          have hparent : T.depth (T.parent x) = n := by
            have h := T.depth_parent hroot
            omega
          rw [ih (T.parent x) hparent]
  exact hdepth (T.depth x) x rfl

variable (R : RectBox4)

noncomputable def rootNormalizeSource (α : IntegerDualField R) :
    SourcePoissonEdge R.side → ℤ :=
  RootedTreeGauge.normalize (sourceRootedTree R.side)
    (fun e => α ((IntegerGaugeTransport.linksEquivSource R).symm e))

noncomputable def rootNormalize (α : IntegerDualField R) : IntegerDualField R :=
  fun e => rootNormalizeSource R α (IntegerGaugeTransport.linksEquivSource R e)

noncomputable def rootPotentialReal (α : IntegerDualField R) :
    SourcePoissonVertex R.side → ℝ :=
  RootedTreeGauge.treePotential (sourceRootedTree R.side)
    (fun e => (α ((IntegerGaugeTransport.linksEquivSource R).symm e) : ℝ))

lemma rootPotentialReal_root (α : IntegerDualField R) :
    rootPotentialReal R α none = 0 := by
  change ((RootedTreeGauge.treePotential (sourceRootedTree R.side)
    (fun e => (α e : ℝ)) (sourceRootedTree R.side).root) = 0)
  exact RootedTreeGauge.treePotential_root _ _

theorem rootNormalize_treeGauge (α : IntegerDualField R) :
    RootedTreeGauge.InTreeGauge (sourceRootedTree R.side)
      (rootNormalizeSource R α) :=
  RootedTreeGauge.normalize_mem _

private theorem rootNormalize_rawField (α : IntegerDualField R) :
    IntegerGaugeTransport.literalFieldRealVector R (rootNormalize R α) =
      IntegerGaugeTransport.literalFieldRealVector R α -
        sourceGraphField (rootPotentialReal R α) := by
  ext e
  change (rootNormalizeSource R α e : ℝ) =
    (α ((IntegerGaugeTransport.linksEquivSource R).symm e) : ℝ) -
    sourceTreeCoboundary R.side (rootPotentialReal R α) e
  simp only [rootNormalizeSource, RootedTreeGauge.normalize,
    RootedTreeGauge.coboundary, sourceTreeCoboundary, rootPotentialReal]
  rw [show (sourceRootedTree R.side).edgeTarget e =
      sourcePoissonEdgeUpperVertex e by rfl]
  rw [show (sourceRootedTree R.side).edgeSource e =
      sourcePoissonEdgeLowerVertex e by rfl]
  push_cast
  rw [integerTreePotential_cast (sourceRootedTree R.side)
    (fun e => α ((IntegerGaugeTransport.linksEquivSource R).symm e))
    (sourcePoissonEdgeUpperVertex e)]
  rw [integerTreePotential_cast (sourceRootedTree R.side)
    (fun e => α ((IntegerGaugeTransport.linksEquivSource R).symm e))
    (sourcePoissonEdgeLowerVertex e)]

private theorem sourceTreeVertexPotential_rootPotential (α : IntegerDualField R) :
    sourceTreeZeroPotential R.side
      (sourceTreeVertexPotential R.side (rootPotentialReal R α)) =
        rootPotentialReal R α := by
  have hp : sourceNormalizePotential (rootPotentialReal R α) =
      rootPotentialReal R α := by
    funext v
    simp [sourceNormalizePotential, rootPotentialReal_root]
  rw [← hp]
  exact sourceTreeVertexPotential_normalize (rootPotentialReal R α)

private theorem rootNormalize_sourceCurlInput (α : IntegerDualField R) :
    IntegerGaugeTransport.sourceCurlInput R (rootNormalize R α) =
      IntegerGaugeTransport.sourceCurlInput R α -
        sourceDualTLinear (sourceGraphField (rootPotentialReal R α)) := by
  unfold IntegerGaugeTransport.sourceCurlInput
  rw [rootNormalize_rawField]
  simp only [map_sub]

private theorem rootNormalize_d1_eq (α : IntegerDualField R) :
    sourceDualD₁ (IntegerGaugeTransport.sourceCurlInput R (rootNormalize R α)) =
      sourceDualD₁ (IntegerGaugeTransport.sourceCurlInput R α) := by
  let C := latticeExactOneComplex (B := R.side) R.origin
  let u := sourceTreeVertexPotential R.side (rootPotentialReal R α)
  have hgraph : C.d₀ u = sourceGraphField (rootPotentialReal R α) := by
    rw [sourceLatticeD0_eq_sourceGraphField]
    rw [sourceTreeVertexPotential_rootPotential]
  have hzero : C.d₁ (sourceGraphField (rootPotentialReal R α)) = 0 := by
    rw [← hgraph]
    have h := congrArg (fun f :
        EuclideanSpace ℝ (SourceDualZeroCells R.side) →ₗ[ℝ]
          EuclideanSpace ℝ (SourceDualTwoCells R.side) => f u) C.complex
    simpa [C, LinearMap.comp_apply] using h
  rw [rootNormalize_sourceCurlInput]
  change sourceDualD₁ (IntegerGaugeTransport.sourceCurlInput R α -
    sourceDualTLinear (sourceGraphField (rootPotentialReal R α))) = _
  rw [map_sub]
  have hzero' : sourceDualD₁
      (sourceDualTLinear (sourceGraphField (rootPotentialReal R α))) = 0 := by
    change C.d₁ (sourceGraphField (rootPotentialReal R α)) = 0
    exact hzero
  rw [hzero', sub_zero]

theorem rootNormalize_integerCurl_eq (α : IntegerDualField R) :
    integerLatticeCurl R (rootNormalize R α) = integerLatticeCurl R α := by
  have hD₁ := rootNormalize_d1_eq R α
  have hcast : Cubical.castLatticeChain
      (integerLatticeCurl R (rootNormalize R α)) =
      Cubical.castLatticeChain (integerLatticeCurl R α) := by
    rw [IntegerGaugeTransport.literalCurl_cast_eq_sourceCurl,
      IntegerGaugeTransport.literalCurl_cast_eq_sourceCurl, hD₁]
  apply Finsupp.ext
  intro c
  have hc := congrArg (fun q : Cubical.RealLatticeChain 4 => q c) hcast
  have hc' : ((integerLatticeCurl R (rootNormalize R α) c : ℤ) : ℝ) =
      ((integerLatticeCurl R α c : ℤ) : ℝ) := by
    simpa [Cubical.castLatticeChain, Finsupp.mapRange_apply] using hc
  exact Int.cast_injective hc'

theorem rootNormalize_eq_of_relation (α α' : IntegerDualField R)
    (hrel : sourceIntegerGaugeRelation R α α') :
    rootNormalize R α = rootNormalize R α' := by
  let T := sourceRootedTree R.side
  let C := latticeExactOneComplex (B := R.side) R.origin
  let raw (a : IntegerDualField R) :=
    IntegerGaugeTransport.literalFieldRealVector R a
  have hcurl := IntegerGaugeTransport.integerLatticeCurl_respectsGauge R α α' hrel
  have hd1 := GaugeCurrentEquivalence.integerCurl_eq_implies_sourceD₁_eq
    R α α' hcurl
  have hnormd1 :
      sourceDualD₁ (IntegerGaugeTransport.sourceCurlInput R (rootNormalize R α')) =
        sourceDualD₁ (IntegerGaugeTransport.sourceCurlInput R (rootNormalize R α)) := by
    calc
      _ = sourceDualD₁ (IntegerGaugeTransport.sourceCurlInput R α') :=
        rootNormalize_d1_eq R α'
      _ = sourceDualD₁ (IntegerGaugeTransport.sourceCurlInput R α) := hd1
      _ = _ := (rootNormalize_d1_eq R α).symm
  have hinput (a : IntegerDualField R) :
      IntegerGaugeTransport.sourceCurlInput R a = sourceDualTLinear (raw a) := rfl
  have hker : raw (rootNormalize R α') - raw (rootNormalize R α) ∈ C.d₁.ker := by
    apply LinearMap.mem_ker.mpr
    change sourceDualD₁ (sourceDualTLinear
      (raw (rootNormalize R α') - raw (rootNormalize R α))) = 0
    rw [map_sub]
    rw [← hinput (rootNormalize R α'), ← hinput (rootNormalize R α)]
    rw [map_sub]
    rw [hnormd1]
    exact sub_self _
  have hrange : raw (rootNormalize R α') - raw (rootNormalize R α) ∈
      LinearMap.range C.d₀ := C.exactOne hker
  obtain ⟨u, hu⟩ := LinearMap.mem_range.mp hrange
  let p := sourceTreeZeroPotential R.side u
  have hgraph : sourceGraphField p = raw (rootNormalize R α') - raw (rootNormalize R α) := by
    have hD0 := sourceLatticeD0_eq_sourceGraphField (B := R.side) R.origin u
    exact hD0.symm.trans hu
  have hpTree : ∀ w : {x : SourcePoissonVertex R.side //
      x ≠ (sourceRootedTree R.side).root},
      RootedTreeGauge.coboundary T p (T.treeEdge w) = 0 := by
    intro w
    have he := congrArg (fun x : EuclideanSpace ℝ (SourceDualOneCells R.side) =>
      x (T.treeEdge w)) hgraph
    change RootedTreeGauge.coboundary T p (T.treeEdge w) =
      ((rootNormalizeSource R α' (T.treeEdge w) : ℤ) : ℝ) -
        ((rootNormalizeSource R α (T.treeEdge w) : ℤ) : ℝ) at he
    have htree' : rootNormalizeSource R α' (T.treeEdge w) = 0 :=
      rootNormalize_treeGauge R α' w
    have htree : rootNormalizeSource R α (T.treeEdge w) = 0 :=
      rootNormalize_treeGauge R α w
    rw [htree', htree] at he
    simpa using he
  have hpconst := T.potential_constant_of_tree_zero p hpTree
  have hpRoot : p T.root = 0 := by rfl
  have hgraphZero : sourceGraphField p = 0 := by
    ext e
    change RootedTreeGauge.coboundary T p e = 0
    unfold RootedTreeGauge.coboundary
    rw [hpconst (T.edgeTarget e), hpconst (T.edgeSource e), hpRoot]
    simp
  have hraw : raw (rootNormalize R α') = raw (rootNormalize R α) := by
    apply sub_eq_zero.mp
    rw [← hgraph]
    rw [hgraphZero]
  apply funext
  intro e
  have he := congrArg (fun x : EuclideanSpace ℝ (SourceDualOneCells R.side) =>
    x (IntegerGaugeTransport.linksEquivSource R e)) hraw
  have hsource : rootNormalizeSource R α'
      ((IntegerGaugeTransport.linksEquivSource R)
        ((IntegerGaugeTransport.linksEquivSource R).symm
          ((IntegerGaugeTransport.linksEquivSource R) e))) =
    rootNormalizeSource R α
      ((IntegerGaugeTransport.linksEquivSource R)
        ((IntegerGaugeTransport.linksEquivSource R).symm
          ((IntegerGaugeTransport.linksEquivSource R) e))) := by
    simpa [raw, rootNormalize, IntegerGaugeTransport.literalFieldRealVector,
      FroehlichSpencer.FS82.Gaussian.finsuppToEuclidean_apply,
      FroehlichSpencer.FS82.Gaussian.castIntegerFinsupp,
      IntegerGaugeTransport.sourceFieldOfLiteral_apply,
      IntegerGaugeTransport.linksEquivSource, Finsupp.mapRange_apply] using he
  have hcancel : (IntegerGaugeTransport.linksEquivSource R)
      ((IntegerGaugeTransport.linksEquivSource R).symm
        ((IntegerGaugeTransport.linksEquivSource R) e)) =
      (IntegerGaugeTransport.linksEquivSource R) e :=
    (IntegerGaugeTransport.linksEquivSource R).apply_symm_apply _
  rw [hcancel] at hsource
  change rootNormalizeSource R α ((IntegerGaugeTransport.linksEquivSource R) e) =
    rootNormalizeSource R α' ((IntegerGaugeTransport.linksEquivSource R) e)
  exact hsource.symm

end FroehlichSpencer.FS82.SourceCovarianceBridge
end
