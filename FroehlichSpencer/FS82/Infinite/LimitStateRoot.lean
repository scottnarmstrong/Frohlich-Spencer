/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Root.CubeMomentComparison
public import FroehlichSpencer.FS82.Infinite.FourierGreenEquality
public import FroehlichSpencer.FS82.Infinite.NonsummabilityMoments
public import FroehlichSpencer.FS82.Infinite.LimitStateMoments

@[expose] public section

open Filter Topology MeasureTheory
open scoped BigOperators InnerProductSpace

namespace FroehlichSpencer.FS82.Infinite

open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Gaussian
open FroehlichSpencer.FS82.Moment.SourceConstructor
open FroehlichSpencer.FS82.Poisson
open FroehlichSpencer.FS82.Root
open FroehlichSpencer.FS82.Moment.Comparison
open FroehlichSpencer.FS82.Infinite.Fourier
open FroehlichSpencer.FS82.Infinite.FourierGreenEquality
open FroehlichSpencer.FS82.Infinite.Nonsummability

/-- The physical curvature observable of a compact plaquette filling.  The
orientation sign converts the source dual plaquette coordinate to the
physical lattice plaquette coordinate used by `globalBoundary`. -/
noncomputable def sourceFillingCurvaturePairing (σ : GlobalPlaquetteField)
    (x : fillingCurvatureIndexSet σ → ℤ) : ℝ :=
  ∑ p : fillingCurvatureIndexSet σ,
    latticeCellOrientationSign p.1.1 * fillingPlaquetteCoeff σ p * (x p : ℝ)

private theorem fillingCurvatureIndexSet_sum (σ : GlobalPlaquetteField)
    (f : GlobalIntegerPlaquette → ℝ) :
    ∑ p : fillingCurvatureIndexSet σ, f p.1 =
      ∑ q : (σ : RealLatticeChain 4).support,
        f (fillingPlaquetteEmbedding σ q) := by
  classical
  let S := (σ : RealLatticeChain 4).support
  let g : LatticeCell 4 → ℝ := fun c =>
    if hc : c ∈ S then f (fillingPlaquetteEmbedding σ ⟨c, hc⟩) else 0
  have hattach :
      (∑ q ∈ S.attach, f (fillingPlaquetteEmbedding σ q)) =
        ∑ q : S, f (fillingPlaquetteEmbedding σ q) := by
    calc
      _ = ∑ q ∈ S.attach, g q.1 := by
        apply Finset.sum_congr rfl
        intro q hq
        have hqS : q.1 ∈ S := q.2
        simp only [g, dite_eq_left hqS]
        exact congrArg f (congrArg (fillingPlaquetteEmbedding σ) (Subtype.ext rfl))
      _ = ∑ q : S, g q.1 := by
        calc
          _ = ∑ q ∈ S, g q := Finset.sum_attach S g
          _ = _ := (Finset.sum_coe_sort S g).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro q hq
        simp only [g, dite_eq_left q.2]
        rfl
  calc
    _ = ∑ p ∈ fillingCurvatureIndexSet σ, f p := Finset.sum_coe_sort _ _
    _ = ∑ q ∈ S.attach, f (fillingPlaquetteEmbedding σ q) := by
      rw [fillingCurvatureIndexSet, Finset.sum_map]
    _ = _ := hattach

/-- A source dual plaquette test pairs with a physical boundary coefficient
with the orientation sign of the physical plaquette. -/
private theorem sourcePlaquetteTest_boundary_sign (N : ℕ)
    (q : SourceDualTwoCells (cube N))
    (e : (sourceRootedTree (cube N)).Chord) :
    sourceChordTest (sourcePlaquetteTest q) e =
      latticeCellOrientationSign (cubePlaquetteEmbedding N q) *
        globalBoundary (Finsupp.single (cubePlaquetteEmbedding N q) (1 : ℝ))
          (lambdaStarEmbedding (B := cube N) (cubeOrigin N) e.1) := by
  rw [sourcePlaquetteTest_chordValue]
  let x : EuclideanSpace ℝ (SourceDualOneCells (cube N)) := EuclideanSpace.single e.1 1
  have hsingle : sourceDualD₁ (EuclideanSpace.single e.1 1) q =
      sourceCurlCoefficient q e.1 := by
    rw [sourceDualD₁_eq_sourceCurl_sum]
    simp
  rw [← hsingle]
  change (sourceDualT e.1 : ℝ) * sourceDualD₁ x q = _
  rw [sourceDualD₁_physical_coefficient (cubeOrigin N) x q]
  have hT : (sourceDualT e.1 : ℝ) = dualCellOrientationSign e.1.1 :=
    sourceDualT_cast_eq_orientationSign e.1
  have hsignq : latticeCellOrientationSign (cubePlaquetteEmbedding N q) =
      dualCellOrientationSign q.1 := by
    change latticeCellOrientationSign (dualCellEmbedding (cubeOrigin N) q.1) = _
    exact latticeCellOrientationSign_physical (cubeOrigin N) q.1
  have hext : lambdaStarRealZeroExtension (B := cube N) (cubeOrigin N)
        (sourceDualTMap (euclideanToFinsupp x)) =
      Finsupp.single (lambdaStarEmbedding (B := cube N) (cubeOrigin N) e.1)
        (sourceDualT e.1 : ℝ) := by
    simp [x, sourceDualTMap, euclideanToFinsupp, lambdaStarRealZeroExtension,
      Finsupp.linearCombination_single, hT]
  rw [hsignq, hext]
  have hsq : (sourceDualT e.1 : ℝ) ^ 2 = 1 := by
    rw [hT]
    exact dualCellOrientationSign_sq (B := cube N) e.1
  have hEval (z : RealLatticeChain 4) (c : LatticeCell 4) :
      globalPairing z (Finsupp.single c (1 : ℝ)) = z c := by
    rw [globalPairing_symm]
    simp [globalPairing]
  have hAdj' : globalBoundary (Finsupp.single (cubePlaquetteEmbedding N q) (1 : ℝ))
      (lambdaStarEmbedding (B := cube N) (cubeOrigin N) e.1) =
    globalCoboundary (Finsupp.single (lambdaStarEmbedding (B := cube N) (cubeOrigin N) e.1)
      (1 : ℝ)) (cubePlaquetteEmbedding N q) := by
    calc
      _ = globalPairing (globalBoundary
          (Finsupp.single (cubePlaquetteEmbedding N q) (1 : ℝ)))
          (Finsupp.single (lambdaStarEmbedding (B := cube N) (cubeOrigin N) e.1) 1) :=
        (hEval _ _).symm
      _ = globalPairing (Finsupp.single (cubePlaquetteEmbedding N q) 1)
          (globalCoboundary (Finsupp.single
            (lambdaStarEmbedding (B := cube N) (cubeOrigin N) e.1) 1)) :=
        globalPairing_boundary_coboundary _ _
      _ = _ := by simp [globalPairing]
  rw [hAdj']
  rw [globalCoboundary]
  rw [sourceRealLatticeCoboundary_single, sourceRealLatticeCoboundary_single]
  simp only [smul_eq_mul, Finsupp.smul_apply]
  rw [← hsq]
  have hcell : cubePlaquetteEmbedding N q =
      dualCellEmbedding (cubeOrigin N) q.1 := rfl
  rw [hcell]
  ring_nf

private theorem sourceChordTest_cubeRestriction_eq_globalPairing
    (μ : GlobalLinkField) (N : ℕ)
    (hμ : globallyCoClosed μ)
    (hsupp : ∀ c ∈ (μ : RealLatticeChain 4).support,
      c ∈ Set.range (lambdaStarEmbedding (B := cube N) (cubeOrigin N)))
    (e : (sourceRootedTree (cube N)).Chord) :
    sourceChordTest
        (⟨cubeLinkRestriction N (μ : RealLatticeChain 4),
          cubeLinkRestriction_mem_cubeSourceW_of_support μ hμ N hsupp⟩)
        e =
      globalPairing (μ : RealLatticeChain 4)
    (Finsupp.single (lambdaStarEmbedding (B := cube N) (cubeOrigin N) e.1) 1) := by
  let μN : cubeSourceW N :=
    ⟨cubeLinkRestriction N (μ : RealLatticeChain 4),
      cubeLinkRestriction_mem_cubeSourceW_of_support μ hμ N hsupp⟩
  have hsingle :
      lambdaStarRealCompression (B := cube N) (cubeOrigin N)
        (Finsupp.single (lambdaStarEmbedding (B := cube N) (cubeOrigin N) e.1) (1 : ℝ)) =
      Finsupp.single e.1 1 := by
    ext f
    simp [lambdaStarRealCompression]
  have hcoord : sourceChordTest μN e =
      inner ℝ (finsuppToEuclidean (Finsupp.single e.1 (1 : ℝ)))
        (μN : EuclideanSpace ℝ (SourceDualOneCells (cube N))) := by
    simp [sourceChordTest, sourceLinkValues, RootedTreeGauge.restrictChord,
      real_inner_comm, inner_finsuppToEuclidean_single]
  rw [← congrArg finsuppToEuclidean hsingle] at hcoord
  rw [cubeLinkRestriction_inner_eq_globalPairing μ N hsupp
    (Finsupp.single (lambdaStarEmbedding (B := cube N) (cubeOrigin N) e.1) 1)] at hcoord
  exact hcoord

private theorem globalCoboundary_single_apply_eq_globalBoundary_single_apply
    (c e : LatticeCell 4) :
    globalCoboundary (Finsupp.single e (1 : ℝ)) c =
      globalBoundary (Finsupp.single c (1 : ℝ)) e := by
  have hEval (z : RealLatticeChain 4) (a : LatticeCell 4) :
      globalPairing z (Finsupp.single a (1 : ℝ)) = z a := by
    rw [globalPairing_symm]
    simp [globalPairing]
  have h := globalPairing_boundary_coboundary
    (Finsupp.single c (1 : ℝ)) (Finsupp.single e (1 : ℝ))
  have hleft : globalPairing (globalBoundary
      (Finsupp.single c (1 : ℝ))) (Finsupp.single e (1 : ℝ)) =
      globalBoundary (Finsupp.single c (1 : ℝ)) e := hEval _ _
  have hright : globalPairing (Finsupp.single c (1 : ℝ))
      (globalCoboundary (Finsupp.single e (1 : ℝ))) =
      globalCoboundary (Finsupp.single e (1 : ℝ)) c := by
    rw [globalPairing_symm]
    exact hEval _ _
  rw [hleft, hright] at h
  exact h.symm

private theorem sourceChordTest_filling_expansion
    (μ : GlobalLinkField) (hμ : globallyCoClosed μ)
    (σ : GlobalPlaquetteField)
    (hfill : globalBoundary (σ : RealLatticeChain 4) =
      (μ : RealLatticeChain 4))
    (N : ℕ)
    (hsupp : ∀ c ∈ (μ : RealLatticeChain 4).support,
      c ∈ Set.range (lambdaStarEmbedding (B := cube N) (cubeOrigin N)))
    (hP : ∀ p ∈ fillingCurvatureIndexSet σ, PlaquetteInCube N p)
    (e : (sourceRootedTree (cube N)).Chord) :
    sourceChordTest
        (⟨cubeLinkRestriction N (μ : RealLatticeChain 4),
          cubeLinkRestriction_mem_cubeSourceW_of_support μ hμ N hsupp⟩)
        e =
      ∑ p : fillingCurvatureIndexSet σ,
        (latticeCellOrientationSign p.1.1 * fillingPlaquetteCoeff σ p) *
          sourceChordTest
            (sourcePlaquetteTest
              (cubePlaquettePreimage N p.1 (hP p.1 p.2))) e := by
  classical
  let link := lambdaStarEmbedding (B := cube N) (cubeOrigin N) e.1
  let μN : cubeSourceW N :=
    ⟨cubeLinkRestriction N (μ : RealLatticeChain 4),
      cubeLinkRestriction_mem_cubeSourceW_of_support μ hμ N hsupp⟩
  have hobs := sourceChordTest_cubeRestriction_eq_globalPairing μ N hμ hsupp e
  have hpair : globalPairing (μ : RealLatticeChain 4)
      (Finsupp.single link (1 : ℝ)) =
      globalPairing (σ : RealLatticeChain 4)
        (globalCoboundary (Finsupp.single link (1 : ℝ))) := by
    rw [← hfill]
    exact globalPairing_boundary_coboundary _ _
  have hpairSum : globalPairing (σ : RealLatticeChain 4)
      (globalCoboundary (Finsupp.single link (1 : ℝ))) =
      ∑ c ∈ (σ : RealLatticeChain 4).support,
        (σ : RealLatticeChain 4) c *
          globalCoboundary (Finsupp.single link (1 : ℝ)) c := by
    rfl
  let P := fillingCurvatureIndexSet σ
  let f : GlobalIntegerPlaquette → ℝ := fun p =>
    if hp : p ∈ P then
      latticeCellOrientationSign p.1 * (σ : RealLatticeChain 4) p.1 *
        sourceChordTest (sourcePlaquetteTest
          (cubePlaquettePreimage N p (hP p hp))) e
    else 0
  have hterms : ∀ c (hc : c ∈ (σ : RealLatticeChain 4).support),
      (σ : RealLatticeChain 4) c *
          globalCoboundary (Finsupp.single link (1 : ℝ)) c =
        f (fillingPlaquetteEmbedding σ ⟨c, hc⟩) := by
    intro c hc
    let qP : GlobalIntegerPlaquette := fillingPlaquetteEmbedding σ ⟨c, hc⟩
    have hmem : qP ∈ fillingCurvatureIndexSet σ := by
      change qP ∈ (σ : RealLatticeChain 4).support.attach.map
        (fillingPlaquetteEmbedding σ)
      exact Finset.mem_map.mpr ⟨⟨c, hc⟩, Finset.mem_attach _ _, rfl⟩
    have hcube : PlaquetteInCube N qP := hP qP hmem
    let qN : SourceDualTwoCells (cube N) := cubePlaquettePreimage N qP hcube
    have hsign := sourcePlaquetteTest_boundary_sign N qN e
    have hembed : cubePlaquetteEmbedding N qN = qP.1 :=
      cubePlaquetteEmbedding_preimage N qP hcube
    have hsq : latticeCellOrientationSign qP.1 ^ 2 = 1 :=
      latticeCellOrientationSign_sq qP.1
    have hAdj := globalCoboundary_single_apply_eq_globalBoundary_single_apply
      qP.1 link
    have htest : sourceChordTest (sourcePlaquetteTest qN) e =
        latticeCellOrientationSign qP.1 *
          globalBoundary (Finsupp.single qP.1 (1 : ℝ)) link := by
      simpa [qP, qN, hembed] using hsign
    have hsqMul : latticeCellOrientationSign qP.1 *
        latticeCellOrientationSign qP.1 = 1 := by
      simpa [pow_two] using hsq
    change (σ : RealLatticeChain 4) c *
        globalCoboundary (Finsupp.single link (1 : ℝ)) c = f qP
    have hFq : f qP =
        latticeCellOrientationSign qP.1 * (σ : RealLatticeChain 4) c *
          sourceChordTest (sourcePlaquetteTest qN) e := by
      dsimp [f, P]
      rw [dite_eq_left hmem]
      rfl
    rw [hFq]
    calc
      (σ : RealLatticeChain 4) c *
          globalCoboundary (Finsupp.single link (1 : ℝ)) c =
        (σ : RealLatticeChain 4) c *
          globalBoundary (Finsupp.single qP.1 (1 : ℝ)) link := by
            rw [globalCoboundary_single_apply_eq_globalBoundary_single_apply c link]
            rfl
      _ = (latticeCellOrientationSign qP.1 *
            latticeCellOrientationSign qP.1) *
          ((σ : RealLatticeChain 4) c *
            globalBoundary (Finsupp.single qP.1 (1 : ℝ)) link) := by
              rw [hsqMul]
              ring
      _ = (latticeCellOrientationSign qP.1 *
            (σ : RealLatticeChain 4) c) *
          (latticeCellOrientationSign qP.1 *
            globalBoundary (Finsupp.single qP.1 (1 : ℝ)) link) := by ring
      _ = _ := by rw [← htest]
  have hsum := fillingCurvatureIndexSet_sum σ f
  have hFpoint (p : fillingCurvatureIndexSet σ) :
      f p.1 =
        (latticeCellOrientationSign p.1.1 * fillingPlaquetteCoeff σ p) *
          sourceChordTest
            (sourcePlaquetteTest
              (cubePlaquettePreimage N p.1 (hP p.1 p.2))) e := by
    simp [f, P, p.2, fillingPlaquetteCoeff]
  have hFsum :
      (∑ p : fillingCurvatureIndexSet σ, f p.1) =
        ∑ p : fillingCurvatureIndexSet σ,
          (latticeCellOrientationSign p.1.1 * fillingPlaquetteCoeff σ p) *
            sourceChordTest (sourcePlaquetteTest
              (cubePlaquettePreimage N p.1 (hP p.1 p.2))) e := by
    apply Finset.sum_congr rfl
    intro p hp
    exact hFpoint p
  have htermsSub :
      (∑ c : (σ : RealLatticeChain 4).support,
        (σ : RealLatticeChain 4) c.1 *
          globalCoboundary (Finsupp.single link (1 : ℝ)) c.1) =
      ∑ c : (σ : RealLatticeChain 4).support,
        f (fillingPlaquetteEmbedding σ c) := by
    apply Finset.sum_congr rfl
    intro c hc
    exact hterms c.1 c.2
  calc
    sourceChordTest μN e =
        globalPairing (μ : RealLatticeChain 4)
          (Finsupp.single link (1 : ℝ)) := by
            simpa [μN, link] using hobs
    _ = globalPairing (σ : RealLatticeChain 4)
          (globalCoboundary (Finsupp.single link (1 : ℝ))) := hpair
    _ = ∑ c ∈ (σ : RealLatticeChain 4).support,
          (σ : RealLatticeChain 4) c *
            globalCoboundary (Finsupp.single link (1 : ℝ)) c := hpairSum
    _ = ∑ c : (σ : RealLatticeChain 4).support,
          (σ : RealLatticeChain 4) c.1 *
            globalCoboundary (Finsupp.single link (1 : ℝ)) c.1 := by
              exact (Finset.sum_coe_sort _ _).symm
    _ = ∑ c : (σ : RealLatticeChain 4).support,
          f (fillingPlaquetteEmbedding σ c) := htermsSub
    _ = ∑ p : fillingCurvatureIndexSet σ, f p.1 := hsum.symm
    _ = _ := by
      exact hFsum

private theorem sourceFillingCurvaturePairing_cubeMap_eq_sourceChordPairing
    (μ : GlobalLinkField) (hμ : globallyCoClosed μ)
    (σ : GlobalPlaquetteField)
    (hfill : globalBoundary (σ : RealLatticeChain 4) =
      (μ : RealLatticeChain 4))
    (N : ℕ)
    (hsupp : ∀ c ∈ (μ : RealLatticeChain 4).support,
      c ∈ Set.range (lambdaStarEmbedding (B := cube N) (cubeOrigin N)))
    (hP : ∀ p ∈ fillingCurvatureIndexSet σ, PlaquetteInCube N p)
    (n : (sourceRootedTree (cube N)).Chord → ℤ) :
    sourceFillingCurvaturePairing σ (cubeCurvatureMap N
      (fillingCurvatureIndexSet σ) hP n) =
      ∑ e, sourceChordTest
        (⟨cubeLinkRestriction N (μ : RealLatticeChain 4),
          cubeLinkRestriction_mem_cubeSourceW_of_support μ hμ N hsupp⟩) e *
        (n e : ℝ) := by
  classical
  let P := fillingCurvatureIndexSet σ
  let μN : cubeSourceW N :=
    ⟨cubeLinkRestriction N (μ : RealLatticeChain 4),
      cubeLinkRestriction_mem_cubeSourceW_of_support μ hμ N hsupp⟩
  have hcurv (p : P) :
      ((cubeCurvatureMap N P hP n p : ℤ) : ℝ) =
        ∑ e, sourceChordTest
          (sourcePlaquetteTest
            (cubePlaquettePreimage N p.1 (hP p.1 p.2))) e * (n e : ℝ) := by
    change ((cubeIntegerCurvatureAt N n p.1 (hP p.1 p.2) : ℤ) : ℝ) = _
    rw [cubeIntegerCurvatureAt, integerChordCurvature_eq_sourceTest]
  have hpairP :
      sourceFillingCurvaturePairing σ (cubeCurvatureMap N P hP n) =
        ∑ p : P, ∑ e,
          ((latticeCellOrientationSign p.1.1 * fillingPlaquetteCoeff σ p) *
            sourceChordTest
              (sourcePlaquetteTest
                (cubePlaquettePreimage N p.1 (hP p.1 p.2))) e) * (n e : ℝ) := by
    unfold sourceFillingCurvaturePairing
    apply Finset.sum_congr rfl
    intro p hp
    rw [hcurv p, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e he
    ring
  calc
    sourceFillingCurvaturePairing σ (cubeCurvatureMap N P hP n) =
        ∑ p : P, ∑ e,
          ((latticeCellOrientationSign p.1.1 * fillingPlaquetteCoeff σ p) *
            sourceChordTest
              (sourcePlaquetteTest
                (cubePlaquettePreimage N p.1 (hP p.1 p.2))) e) * (n e : ℝ) := hpairP
    _ = ∑ e, ∑ p : P,
          ((latticeCellOrientationSign p.1.1 * fillingPlaquetteCoeff σ p) *
            sourceChordTest
              (sourcePlaquetteTest
                (cubePlaquettePreimage N p.1 (hP p.1 p.2))) e) * (n e : ℝ) := by
      exact Finset.sum_comm
    _ = ∑ e,
          (∑ p : P,
            (latticeCellOrientationSign p.1.1 * fillingPlaquetteCoeff σ p) *
              sourceChordTest
                (sourcePlaquetteTest
                  (cubePlaquettePreimage N p.1 (hP p.1 p.2))) e) * (n e : ℝ) := by
      apply Finset.sum_congr rfl
      intro e he
      rw [Finset.sum_mul]
    _ = ∑ e, sourceChordTest μN e * (n e : ℝ) := by
      apply Finset.sum_congr rfl
      intro e he
      rw [sourceChordTest_filling_expansion μ hμ σ hfill N hsupp hP e]

private theorem cubeCurvaturePMFTotal_sourceFilling_expMoment
    (μ : GlobalLinkField) (hμ : globallyCoClosed μ)
    (σ : GlobalPlaquetteField)
    (hfill : globalBoundary (σ : RealLatticeChain 4) =
      (μ : RealLatticeChain 4))
    (N : ℕ) (β t : ℝ) (hβ : 0 < β)
    (hsupp : ∀ c ∈ (μ : RealLatticeChain 4).support,
      c ∈ Set.range (lambdaStarEmbedding (B := cube N) (cubeOrigin N)))
    (hP : ∀ p ∈ fillingCurvatureIndexSet σ, PlaquetteInCube N p) :
    ∫ x, Real.exp (t * sourceFillingCurvaturePairing σ x) ∂
      (cubeCurvaturePMFTotal N β hβ (fillingCurvatureIndexSet σ)).toMeasure =
        sourceDualMoment β
          (⟨cubeLinkRestriction N (μ : RealLatticeChain 4),
            cubeLinkRestriction_mem_cubeSourceW_of_support μ hμ N hsupp⟩) t := by
  classical
  let P := fillingCurvatureIndexSet σ
  let μN : cubeSourceW N :=
    ⟨cubeLinkRestriction N (μ : RealLatticeChain 4),
      cubeLinkRestriction_mem_cubeSourceW_of_support μ hμ N hsupp⟩
  let c : ((sourceRootedTree (cube N)).Chord → ℤ) → (P → ℤ) :=
    cubeCurvatureMap N P hP
  let g : (P → ℤ) → ℝ := fun x =>
    Real.exp (t * sourceFillingCurvaturePairing σ x)
  let A := sourceChordMatrix (B := cube N) β
  have hA : A.PosDef := scaledChordMatrix_posDef _ _ hβ
  have hc : Measurable c := by
    fun_prop (disch := aesop) [cubeCurvatureMap, cubeIntegerCurvatureAt,
      integerChordCurvature]
  have hg : Measurable g := by fun_prop
  have hcomp (n : (sourceRootedTree (cube N)).Chord → ℤ) :
      g (c n) = Real.exp (t * ∑ e,
        sourceChordTest μN e * (n e : ℝ)) := by
    change Real.exp (t * sourceFillingCurvaturePairing σ
      (cubeCurvatureMap N P hP n)) = _
    rw [sourceFillingCurvaturePairing_cubeMap_eq_sourceChordPairing
      μ hμ σ hfill N hsupp hP n]
  have hs0 := dualChordPMF_exp_linear_weighted_summable A hA
    (sourceChordTest μN) t
  have hs : Summable (fun n : (sourceRootedTree (cube N)).Chord → ℤ =>
      (cubeDualChordPMF N β hβ n).toReal * ‖g (c n)‖) := by
    refine hs0.congr ?_
    intro n
    rw [cubeDualChordPMF, ← hcomp n]
  have hmap := pmf_map_integral (cubeDualChordPMF N β hβ) c g hc hg hs
  rw [cubeCurvaturePMFTotal, dite_eq_left hP, cubeLocalCurvaturePMF, hmap]
  calc
    ∫ n, g (c n) ∂(cubeDualChordPMF N β hβ).toMeasure =
        ∫ n, Real.exp (t * ∑ e,
          sourceChordTest μN e * (n e : ℝ)) ∂
            (cubeDualChordPMF N β hβ).toMeasure := by
              apply MeasureTheory.integral_congr_ae
              exact MeasureTheory.ae_of_all _ hcomp
    _ = dualMoment A (sourceChordTest μN) t := by
      rw [cubeDualChordPMF]
      exact dualChordPMF_exp_linear_integral A hA (sourceChordTest μN) t
    _ = sourceDualMoment β μN t := by rfl

/-- Every cube curvature limit state satisfies the FS82 root Gaussian bounds
for the source observable paired through a compact filling. The orientation
sign makes this finite observable equal to the source chord test. -/
theorem cubeCurvatureLimitState_sourceFilling_mgf_bounds
    {β : ℝ} (hβ : rootBetaThreshold ≤ β)
    (L : CubeCurvatureLimitState β (rootBeta_pos hβ))
    (μ : GlobalLinkField) (hμ : globallyCoClosed μ)
    (σ : GlobalPlaquetteField)
    (hfill : globalBoundary (σ : RealLatticeChain 4) =
      (μ : RealLatticeChain 4)) (t : ℝ) :
    Real.exp ((t ^ 2 * betaDoublePrime rootPackingCoefficient β / 2) *
        fourierGreenQuadratic μ) ≤
      ∫ x, Real.exp (t * sourceFillingCurvaturePairing
        σ x) ∂ (L.law (fillingCurvatureIndexSet σ)).toMeasure ∧
    (∫ x, Real.exp (t * sourceFillingCurvaturePairing
        σ x) ∂ (L.law (fillingCurvatureIndexSet σ)).toMeasure) ≤
      Real.exp ((t ^ 2 * β / 2) * fourierGreenQuadratic μ) := by
  classical
  let P := fillingCurvatureIndexSet σ
  obtain ⟨NW, hWbase⟩ := eventually_cube_sourceW μ hμ
  obtain ⟨NP, hPbase⟩ := exists_cube_threshold_for_plaquettes P
  let Rμ : ℕ :=
    ∑ c ∈ (μ : RealLatticeChain 4).support, cubeCellRadius c
  let K := max (Rμ + 2) (max 1 (max NW NP))
  have hK1 : 1 ≤ K := by simp [K]
  have hKNW : NW ≤ K := by simp [K]
  have hKNP : NP ≤ K := by simp [K]
  have hKR : Rμ + 2 ≤ K := by simp [K]
  have hW : ∀ N ≥ K,
      cubeLinkRestriction N (μ : RealLatticeChain 4) ∈ cubeSourceW N := by
    intro N hN
    exact hWbase N (le_trans hKNW hN)
  have hP : ∀ N ≥ K, ∀ p ∈ P, PlaquetteInCube N p := by
    intro N hN
    exact hPbase N (le_trans hKNP hN)
  have hsupp : ∀ N ≥ K,
      ∀ c ∈ (μ : RealLatticeChain 4).support,
        c ∈ Set.range (lambdaStarEmbedding (B := cube N) (cubeOrigin N)) := by
    intro N hN
    apply cubeLinkSupport_subset_of_radius μ N
    simpa [Rμ] using le_trans hKR hN
  have hsubseqLower (n : ℕ) : n ≤ L.subsequence n := by
    induction n with
    | zero => exact Nat.zero_le _
    | succ n ih =>
        exact Nat.succ_le_of_lt
          (lt_of_le_of_lt ih (L.strictMono_subsequence (Nat.lt_succ_self n)))
  have hshift : StrictMono (fun k : ℕ => K + k) := by
    intro a b hab
    exact Nat.add_lt_add_left hab K
  have hidx : StrictMono (fun k : ℕ => L.subsequence (K + k)) :=
    L.strictMono_subsequence.comp hshift
  let E : ℕ → {N : ℕ // K ≤ N} := fun k =>
    ⟨L.subsequence (K + k), by
      exact le_trans (Nat.le_add_right K k) (hsubseqLower (K + k))⟩
  have hE : Tendsto E atTop atTop := by
    apply Filter.tendsto_atTop.2
    intro n
    have hev := (Filter.tendsto_atTop.1 hidx.tendsto_atTop) n.1
    filter_upwards [hev] with k hk
    exact hk
  let cov : ℕ → ℝ := fun k =>
    quotientCovarianceQuadratic (sourceLatticeComplex
      (B := cube (L.subsequence (K + k))))
      ⟨cubeLinkRestriction (L.subsequence (K + k)) (μ : RealLatticeChain 4),
        hW _ (E k).2⟩
  have hcov : Tendsto cov atTop (nhds (globalVariationalCovariance μ)) := by
    have hgate := cubeCovariance_tendsto_fourierGreen μ K hW
    have hcomp := hgate.comp hE
    simpa [cov, E, Function.comp_def] using hcomp
  let coeff : P → ℝ := fun p =>
    latticeCellOrientationSign p.1.1 * fillingPlaquetteCoeff σ p
  let M : ℕ → ℝ := fun k =>
    ∫ x, Real.exp (t * sourceFillingCurvaturePairing σ x) ∂
      (cubeCurvaturePMFTotal (L.subsequence (K + k)) β
        (rootBeta_pos hβ) P).toMeasure
  have hM : Tendsto M atTop (nhds
      (∫ x, Real.exp (t * sourceFillingCurvaturePairing σ x) ∂
        (L.law P).toMeasure)) := by
    have hconv := cubeCurvatureLimitState_expLinear_integral_tendsto
      β (rootBeta_pos hβ) L P coeff t
    have hshiftLimit := hconv.comp hshift.tendsto_atTop
    simpa [M, sourceFillingCurvaturePairing, coeff, Function.comp_def] using hshiftLimit
  have hfinite : ∀ k,
      Real.exp ((t ^ 2 * betaDoublePrime rootPackingCoefficient β / 2) * cov k) ≤ M k ∧
        M k ≤ Real.exp ((t ^ 2 * β / 2) * cov k) := by
    intro k
    let N := L.subsequence (K + k)
    have hNK : K ≤ N := (E k).2
    have hN1 : 1 ≤ N := le_trans hK1 hNK
    let μN : cubeSourceW N :=
      ⟨cubeLinkRestriction N (μ : RealLatticeChain 4), hW N hNK⟩
    have hroot := fs82_cube_moment_comparison hβ N hN1 μN t
    have hmoment := cubeCurvaturePMFTotal_sourceFilling_expMoment
      μ hμ σ hfill N β t (rootBeta_pos hβ) (hsupp N hNK) (hP N hNK)
    constructor
    · calc
        Real.exp ((t ^ 2 * betaDoublePrime rootPackingCoefficient β / 2) * cov k) =
            Real.exp ((t ^ 2 * betaDoublePrime rootPackingCoefficient β / 2) *
              quotientCovarianceQuadratic (sourceLatticeComplex (B := cube N)) μN) := by
                rfl
        _ ≤ sourceDualMoment β μN t := hroot.1
        _ = M k := by
          simpa [M, N, P, μN] using hmoment.symm
    · calc
        M k = sourceDualMoment β μN t := by
          simpa [M, N, P, μN] using hmoment
        _ ≤ Real.exp ((t ^ 2 * β / 2) *
            quotientCovarianceQuadratic (sourceLatticeComplex (B := cube N)) μN) := hroot.2
        _ = Real.exp ((t ^ 2 * β / 2) * cov k) := by rfl
  have hlower :
      Real.exp ((t ^ 2 * betaDoublePrime rootPackingCoefficient β / 2) *
          globalVariationalCovariance μ) ≤
        ∫ x, Real.exp (t * sourceFillingCurvaturePairing σ x) ∂
          (L.law P).toMeasure := by
    let a := t ^ 2 * betaDoublePrime rootPackingCoefficient β / 2
    have hexp : Tendsto (fun k => Real.exp (a * cov k)) atTop
        (nhds (Real.exp (a * globalVariationalCovariance μ))) :=
      (Real.continuous_exp.comp
        (continuous_const.mul continuous_id)).continuousAt.tendsto.comp hcov
    exact le_of_tendsto_of_tendsto' hexp hM (fun k => (hfinite k).1)
  have hupper :
      (∫ x, Real.exp (t * sourceFillingCurvaturePairing σ x) ∂
          (L.law P).toMeasure) ≤
        Real.exp ((t ^ 2 * β / 2) * globalVariationalCovariance μ) := by
    let b := t ^ 2 * β / 2
    have hexp : Tendsto (fun k => Real.exp (b * cov k)) atTop
        (nhds (Real.exp (b * globalVariationalCovariance μ))) :=
      (Real.continuous_exp.comp
        (continuous_const.mul continuous_id)).continuousAt.tendsto.comp hcov
    exact le_of_tendsto_of_tendsto' hM hexp (fun k => (hfinite k).2)
  rw [← globallyCoClosed_fourier_green_eq_covariance μ hμ]
  exact ⟨hlower, hupper⟩


noncomputable def cubeCurvatureObservableFilling
    (μ : GlobalLinkField) (hμ : globallyCoClosed μ) : GlobalPlaquetteField :=
  Classical.choose (compactFilling_exists μ hμ)

theorem cubeCurvatureObservableFilling_boundary
    (μ : GlobalLinkField) (hμ : globallyCoClosed μ) :
    globalBoundary (cubeCurvatureObservableFilling μ hμ : RealLatticeChain 4) =
      (μ : RealLatticeChain 4) :=
  Classical.choose_spec (compactFilling_exists μ hμ)

/-- Direct MGF statement for every compactly supported globally co-closed
test, using the fixed filling selected above to represent `α(μ)`. -/
theorem cubeCurvatureLimitState_mgf_bounds
    {β : ℝ} (hβ : rootBetaThreshold ≤ β)
    (L : CubeCurvatureLimitState β (rootBeta_pos hβ))
    (μ : GlobalLinkField) (hμ : globallyCoClosed μ) (t : ℝ) :
    Real.exp ((t ^ 2 * betaDoublePrime rootPackingCoefficient β / 2) *
        fourierGreenQuadratic μ) ≤
      ∫ x, Real.exp (t * sourceFillingCurvaturePairing
        (cubeCurvatureObservableFilling μ hμ) x) ∂
          (L.law (fillingCurvatureIndexSet
            (cubeCurvatureObservableFilling μ hμ))).toMeasure ∧
    (∫ x, Real.exp (t * sourceFillingCurvaturePairing
        (cubeCurvatureObservableFilling μ hμ) x) ∂
          (L.law (fillingCurvatureIndexSet
            (cubeCurvatureObservableFilling μ hμ))).toMeasure) ≤
      Real.exp ((t ^ 2 * β / 2) * fourierGreenQuadratic μ) := by
  exact cubeCurvatureLimitState_sourceFilling_mgf_bounds hβ L μ hμ
    (cubeCurvatureObservableFilling μ hμ)
    (cubeCurvatureObservableFilling_boundary μ hμ) t


theorem exists_cubeCurvatureLimitState_rootBeta
    {β : ℝ} (hβ : rootBetaThreshold ≤ β) :
    Nonempty (CubeCurvatureLimitState β (rootBeta_pos hβ)) :=
  exists_cubeCurvatureLimitState β (rootBeta_pos hβ)

private theorem iv5_pmf_mass_summable {α : Type*} [Countable α]
    (p : PMF α) : Summable (fun x => (p x).toReal) := by
  apply ENNReal.summable_toReal
  rw [p.tsum_coe]
  exact ENNReal.one_ne_top

private theorem cubeCurvatureLimitState_expLinear_integrable
    (β : ℝ) (hβ : 0 < β) (L : CubeCurvatureLimitState β hβ)
    (P : Finset GlobalIntegerPlaquette) (c : P → ℝ) (s : ℝ) :
    Integrable
      (fun x : P → ℤ => Real.exp (s * ∑ p : P, c p * (x p : ℝ)))
      (L.law P).toMeasure := by
  classical
  let pn : ℕ → PMF (P → ℤ) := fun k =>
    cubeCurvaturePMFTotal (L.subsequence k) β hβ P
  let p : PMF (P → ℤ) := L.law P
  let f : (P → ℤ) → ℝ := fun x => Real.exp (s * ∑ q : P, c q * (x q : ℝ))
  have hpoint : ∀ x, Tendsto (fun k => (pn k x).toReal) atTop
      (𝓝 ((p x).toReal)) := by
    intro x
    exact L.pointwise P x
  let C : ℝ := 1 + ∑ q : P,
    Real.exp (((2 * s * (Fintype.card P : ℝ) * c q) ^ 2 * β) / 2)
  have hsq : ∀ k, Summable (fun x =>
      (pn k x).toReal * (f x) ^ 2) := by
    intro k
    exact (cubeCurvaturePMFTotal_exp_linear_secondMoment
      (L.subsequence k) β hβ P c s).1
  have hsqBound : ∀ k, ∑' x, (pn k x).toReal * (f x) ^ 2 ≤ C := by
    intro k
    exact cubeCurvaturePMFTotal_exp_linear_secondMoment
      (L.subsequence k) β hβ P c s |>.2
  have hlimSq := pmf_secondMoment_bound_of_pointwise
    pn p f C hpoint hsq hsqBound
  have hmass := iv5_pmf_mass_summable p
  have hYoung (x : P → ℤ) : f x ≤ 1 + (f x) ^ 2 := by
    nlinarith [sq_nonneg (f x - 1 / 2)]
  have hweight : Summable (fun x => (p x).toReal * f x) := by
    apply Summable.of_nonneg_of_le
      (fun x => mul_nonneg ENNReal.toReal_nonneg (Real.exp_pos _).le)
    · intro x
      have hm := ENNReal.toReal_nonneg (a := p x)
      exact mul_le_mul_of_nonneg_left (hYoung x) hm
    · simpa [mul_add] using hmass.add hlimSq.1
  have hnorm : Summable (fun x => (p x).toReal * ‖f x‖) := by
    refine hweight.congr ?_
    intro x
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact pmf_integrable_of_summable_norm hnorm

/-- The real observable law induced by a cylinder limit state and a compact
plaquette filling. -/
noncomputable def cubeCurvatureLimitState_sourceObservableMeasure
    {β : ℝ} {hβ : 0 < β} (L : CubeCurvatureLimitState β hβ)
    (σ : GlobalPlaquetteField) : Measure ℝ :=
  Measure.map (sourceFillingCurvaturePairing σ)
    (L.law (fillingCurvatureIndexSet σ)).toMeasure

/--
The observable's second moment lies between the two Gaussian rates.
-/
theorem cubeCurvatureLimitState_sourceFilling_secondMoment_bounds
    {β : ℝ} (hβ : rootBetaThreshold ≤ β)
    (L : CubeCurvatureLimitState β (rootBeta_pos hβ))
    (μ : GlobalLinkField) (hμ : globallyCoClosed μ)
    (σ : GlobalPlaquetteField)
    (hfill : globalBoundary (σ : RealLatticeChain 4) =
      (μ : RealLatticeChain 4)) :
    betaDoublePrime rootPackingCoefficient β * fourierGreenQuadratic μ ≤
        ∫ x, (sourceFillingCurvaturePairing σ x) ^ 2 ∂
          (L.law (fillingCurvatureIndexSet σ)).toMeasure ∧
      (∫ x, (sourceFillingCurvaturePairing σ x) ^ 2 ∂
          (L.law (fillingCurvatureIndexSet σ)).toMeasure) ≤
        β * fourierGreenQuadratic μ := by
  classical
  let P := fillingCurvatureIndexSet σ
  let α : (P → ℤ) → ℝ := sourceFillingCurvaturePairing σ
  let ρ : Measure ℝ := cubeCurvatureLimitState_sourceObservableMeasure L σ
  have hα : Measurable α := by fun_prop
  have hρ : IsProbabilityMeasure ρ := by
    constructor
    change (Measure.map α (L.law P).toMeasure) Set.univ = 1
    rw [Measure.map_apply hα MeasurableSet.univ]
    simp
  have hExp : ∀ s : ℝ, Integrable (fun x : ℝ => Real.exp (s * x)) ρ := by
    intro s
    have hsource := cubeCurvatureLimitState_expLinear_integrable
      β (rootBeta_pos hβ) L P
      (fun p => latticeCellOrientationSign p.1.1 * fillingPlaquetteCoeff σ p) s
    have hmeas : Measurable (fun x : P → ℤ => Real.exp (s * α x)) := by fun_prop
    have hsource' : Integrable (fun x : P → ℤ => Real.exp (s * α x))
        (L.law P).toMeasure := by
      let coeff : P → ℝ := fun p =>
        latticeCellOrientationSign p.1.1 * fillingPlaquetteCoeff σ p
      have hαpoint (x : P → ℤ) : α x =
          ∑ p : P, coeff p * (x p : ℝ) := by
        dsimp [α, sourceFillingCurvaturePairing, coeff, P]
      have heq : (fun x : P → ℤ => Real.exp (s * α x)) =
          (fun x => Real.exp (s * ∑ p : P, coeff p * (x p : ℝ))) := by
        funext x
        rw [hαpoint]
      rw [heq]
      exact hsource
    have hmapExp : Integrable (fun x : ℝ => Real.exp (s * x))
        (Measure.map α (L.law P).toMeasure) := by
      exact (MeasureTheory.integrable_map_measure
        (by fun_prop : AEStronglyMeasurable
          (fun x : ℝ => Real.exp (s * x)) (Measure.map α (L.law P).toMeasure))
        hα.aemeasurable).2 hsource'
    change Integrable (fun x : ℝ => Real.exp (s * x)) ρ
    exact hmapExp
  have hmgfEq (s : ℝ) : ProbabilityTheory.mgf id ρ s =
      ∫ x, Real.exp (s * α x) ∂(L.law P).toMeasure := by
    change (∫ y, Real.exp (s * y) ∂
      Measure.map α (L.law P).toMeasure) = _
    exact MeasureTheory.integral_map_of_stronglyMeasurable hα (by fun_prop)
  let a := betaDoublePrime rootPackingCoefficient β * fourierGreenQuadratic μ
  let b := β * fourierGreenQuadratic μ
  have hM : ∀ s : ℝ,
      Real.exp (a * s ^ 2 / 2) ≤ ProbabilityTheory.mgf id ρ s ∧
        ProbabilityTheory.mgf id ρ s ≤ Real.exp (b * s ^ 2 / 2) := by
    intro s
    have h := cubeCurvatureLimitState_sourceFilling_mgf_bounds
      hβ L μ hμ σ hfill s
    rw [hmgfEq s]
    constructor
    ·
      rw [show a * s ^ 2 / 2 =
          (s ^ 2 * betaDoublePrime rootPackingCoefficient β / 2) *
            fourierGreenQuadratic μ by dsimp [a]; ring_nf]
      exact h.1
    ·
      rw [show b * s ^ 2 / 2 =
          (s ^ 2 * β / 2) * fourierGreenQuadratic μ by dsimp [b]; ring_nf]
      exact h.2
  have hsecond := variance_mem_Icc_of_mgf_quadratic_bounds ρ a b hExp hM
  have hzero : ∫ x : ℝ, x ∂ρ = 0 := by
    let f := ProbabilityTheory.mgf id ρ
    have hloc : IsLocalMax
        (fun s => f s - Real.exp (b * s ^ 2 / 2)) 0 := by
      change ∀ᶠ s in 𝓝 (0 : ℝ),
        f s - Real.exp (b * s ^ 2 / 2) ≤
          f 0 - Real.exp (b * 0 ^ 2 / 2)
      filter_upwards [Filter.Eventually.of_forall fun s => (hM s).2] with s hs
      have hf0 : f 0 = 1 := by simp [f]
      rw [hf0]
      simp only [zero_pow (by decide : 2 ≠ 0), mul_zero, zero_div,
        Real.exp_zero]
      linarith
    have hset : ProbabilityTheory.integrableExpSet id ρ = Set.univ := by
      ext s
      simp [ProbabilityTheory.integrableExpSet, hExp s]
    have h0 : (0 : ℝ) ∈ interior (ProbabilityTheory.integrableExpSet id ρ) := by
      rw [hset, interior_univ]
      simp
    have hmgf : HasDerivAt f (∫ x : ℝ, x ∂ρ) 0 := by
      simpa [f] using ProbabilityTheory.hasDerivAt_mgf
        (X := id) (μ := ρ) h0
    have hinner : HasDerivAt (fun s : ℝ => b * s ^ 2 / 2) 0 0 := by
      have hmul := ((hasDerivAt_id (0 : ℝ)).pow 2).const_mul (b / 2)
      convert hmul using 1
      · funext s
        dsimp
        ring_nf
      · simp
    have hquad : HasDerivAt (fun s : ℝ => Real.exp (b * s ^ 2 / 2)) 0 0 := by
      have hcomp := (Real.hasDerivAt_exp (b * (0 : ℝ) ^ 2 / 2)).comp 0 hinner
      simpa [Function.comp_def] using hcomp
    have hz := hloc.hasDerivAt_eq_zero (hmgf.sub hquad)
    simpa using hz
  have hvarEq : ProbabilityTheory.variance id ρ = ∫ x : ℝ, x ^ 2 ∂ρ := by
    rw [ProbabilityTheory.variance_eq_integral
      (μ := ρ) (X := id) measurable_id.aemeasurable]
    simp [hzero]
  have hmapSq : ∫ x : ℝ, x ^ 2 ∂ρ =
      ∫ x, (α x) ^ 2 ∂(L.law P).toMeasure := by
    change (∫ x : ℝ, x ^ 2 ∂Measure.map α (L.law P).toMeasure) = _
    exact MeasureTheory.integral_map_of_stronglyMeasurable hα (by fun_prop)
  rw [hvarEq, hmapSq] at hsecond
  exact hsecond


end FroehlichSpencer.FS82.Infinite

end
