/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Infinite.NonsummabilityState
public import FroehlichSpencer.FS82.Infinite.NonsummabilitySpectrum
public import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Corrected spectral localization interface for photon nonsummability

This file constructs finite
Fourier-polynomial tests by uniformly approximating even shrinking bumps.

The resulting squared weights localize against integrable tests continuous at
the target point.
-/

@[expose] public section

open Filter Topology MeasureTheory
open FroehlichSpencer.FS82.Infinite.Nonsummability
open FroehlichSpencer.FS82.Infinite.Fourier
open FroehlichSpencer.FS82.Infinite.FourierApproximation
open FroehlichSpencer.FS82.Infinite.FourierVariational
open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Root
open FroehlichSpencer.FS82.Moment.Comparison
open scoped ComplexConjugate

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
local instance : BorelSpace (AddCircle (1 : ℝ) ×
    (AddCircle (1 : ℝ) × AddCircle (1 : ℝ))) := by infer_instance
local instance : BorelSpace Torus4 := by
  dsimp [Torus4]
  infer_instance
local instance : IsFiniteMeasure torus4Haar := by
  dsimp [torus4Haar]
  infer_instance
local instance : IsProbabilityMeasure torus4Haar := by
  dsimp [torus4Haar]
  infer_instance
local instance : MeasureTheory.Measure.IsOpenPosMeasure torus4Haar := by
  dsimp [torus4Haar]
  infer_instance

namespace FroehlichSpencer.FS82.Infinite.Nonsummability

/-- The coordinate-oriented dual plaquette in the `0,1` plane based at the
lattice point `x`. Under C4 it is dual to the primal `2,3` plaquette at `x`. -/
def spectralPlaquetteCell (x : LatticePoint) : LatticeCell 4 :=
  fun i => if i = 0 ∨ i = 1 then
    Sum.inr (latticePointCoordinate x i)
  else Sum.inl (latticePointCoordinate x i)

theorem spectralPlaquetteCell_axes (x : LatticePoint) :
    Fourier.latticeCellAxes (spectralPlaquetteCell x) = {0, 1} := by
  classical
  ext i
  change i ∈ Finset.univ.filter (fun j : Fin 4 =>
    latticeIsEdge (spectralPlaquetteCell x j)) ↔ i ∈ ({0, 1} : Finset (Fin 4))
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton]
  by_cases hi : i = 0 ∨ i = 1
  · simp [spectralPlaquetteCell, hi, latticeIsEdge]
  · simp [spectralPlaquetteCell, hi, latticeIsEdge]

theorem spectralPlaquetteCell_degree (x : LatticePoint) :
    latticeCellDegree (spectralPlaquetteCell x) = 2 := by
  classical
  change (Fourier.latticeCellAxes (spectralPlaquetteCell x)).card = 2
  rw [spectralPlaquetteCell_axes]
  decide

theorem spectralPlaquetteCell_point (x : LatticePoint) :
    latticeCellPoint (spectralPlaquetteCell x) = x := by
  apply Prod.ext
  · simp [latticeCellPoint, spectralPlaquetteCell, latticeCellBaseCoordinate,
      latticePointCoordinate]
  · apply Prod.ext
    · simp [latticeCellPoint, spectralPlaquetteCell, latticeCellBaseCoordinate,
        latticePointCoordinate]
    · apply Prod.ext
      · simp [latticeCellPoint, spectralPlaquetteCell, latticeCellBaseCoordinate,
          latticePointCoordinate]
      · simp [latticeCellPoint, spectralPlaquetteCell, latticeCellBaseCoordinate,
          latticePointCoordinate]

noncomputable def spectralPlaquetteAt (x : LatticePoint) : GlobalIntegerPlaquette :=
  ⟨spectralPlaquetteCell x, spectralPlaquetteCell_degree x⟩

theorem spectralPlaquetteAt_injective : Function.Injective spectralPlaquetteAt := by
  intro x y h
  have hcell : spectralPlaquetteCell x = spectralPlaquetteCell y := congrArg Subtype.val h
  have hp := congrArg latticeCellPoint hcell
  simpa only [spectralPlaquetteCell_point] using hp

noncomputable def spectralPlaquetteCellEmbedding : LatticePoint ↪ LatticeCell 4 where
  toFun := spectralPlaquetteCell
  inj' := by
    intro x y h
    have hp := congrArg latticeCellPoint h
    simpa only [spectralPlaquetteCell_point] using hp


noncomputable def spectralCurvatureWindow (a : LatticePoint →₀ ℝ) : GlobalPlaquetteField :=
  ⟨Finsupp.embDomain spectralPlaquetteCellEmbedding a, by
    classical
    intro c hc
    rw [Finsupp.support_embDomain] at hc
    rcases Finset.mem_map.mp hc with ⟨x, hx, rfl⟩
    exact spectralPlaquetteCell_degree x⟩


def spectralPointShift (x : LatticePoint) : LatticeShift :=
  fun i => latticePointCoordinate x i


theorem spectralPlaquetteCell_translate_point (a : LatticeShift) (x : LatticePoint) :
    translateLatticeCell a (spectralPlaquetteCell x) =
      spectralPlaquetteCell (x + latticeShiftPoint a) := by
  funext i
  fin_cases i <;>
    simp [translateLatticeCell, translateLatticeCoord, spectralPlaquetteCell,
      latticeShiftPoint, latticePointCoordinate]


theorem spectralPlaquetteAt_translate_point (a : LatticeShift) (x : LatticePoint) :
    translatePlaquetteEquiv a (spectralPlaquetteAt x) =
      spectralPlaquetteAt (x + latticeShiftPoint a) := by
  apply Subtype.ext
  exact spectralPlaquetteCell_translate_point a x

noncomputable def spectralPairPlaquettes (x y : LatticePoint) : Finset GlobalIntegerPlaquette :=
  insert (spectralPlaquetteAt x) {spectralPlaquetteAt y}

theorem spectralPairPlaquettes_translate (a : LatticeShift) (x y : LatticePoint) :
    translatePlaquettes a (spectralPairPlaquettes x y) =
      spectralPairPlaquettes (x + latticeShiftPoint a) (y + latticeShiftPoint a) := by
  classical
  simp [translatePlaquettes, spectralPairPlaquettes, spectralPlaquetteAt_translate_point]

noncomputable def spectralPairIndex (x y : LatticePoint) (z : LatticePoint)
    (hz : spectralPlaquetteAt z ∈ spectralPairPlaquettes x y) :
    spectralPairPlaquettes x y :=
  ⟨spectralPlaquetteAt z, hz⟩

private theorem spectralPlaquetteCell_rankBefore_one (x : LatticePoint) :
    latticeRankBefore (spectralPlaquetteCell x) 1 = 1 := by
  classical
  unfold latticeRankBefore
  have hset : Finset.univ.filter (fun j : Fin 4 =>
      j < 1 ∧ latticeIsEdge (spectralPlaquetteCell x j)) = {0} := by
    ext j
    fin_cases j <;> simp [spectralPlaquetteCell, latticeIsEdge]
  rw [hset]
  simp

private theorem spectralPlaquetteCell_boundaryBasis (x : LatticePoint) :
    latticeBoundaryBasis (spectralPlaquetteCell x) =
      latticeBasis (latticeUpperFace (spectralPlaquetteCell x) 0
          (latticePointCoordinate x 0)) -
        latticeBasis (latticeLowerFace (spectralPlaquetteCell x) 0
          (latticePointCoordinate x 0)) -
        latticeBasis (latticeUpperFace (spectralPlaquetteCell x) 1
          (latticePointCoordinate x 1)) +
        latticeBasis (latticeLowerFace (spectralPlaquetteCell x) 1
          (latticePointCoordinate x 1)) := by
  classical
  have hrank0 : latticeRankBefore (spectralPlaquetteCell x) 0 = 0 := by
    unfold latticeRankBefore
    have hset : Finset.univ.filter (fun j : Fin 4 =>
        j < 0 ∧ latticeIsEdge (spectralPlaquetteCell x j)) = ∅ := by
      ext j
      simp
    rw [hset]
    simp
  unfold latticeBoundaryBasis
  rw [Fin.sum_univ_four]
  simp [spectralPlaquetteCell, hrank0, spectralPlaquetteCell_rankBefore_one]
  abel

private theorem spectralPlaquetteEdgeAxis_upper0 (x : LatticePoint) :
    latticeLinkAxisCell
      (latticeUpperFace (spectralPlaquetteCell x) 0 (latticePointCoordinate x 0)) 1 := by
  constructor
  · simp [latticeIsEdge, spectralPlaquetteCell, latticeUpperFace]
  · intro j hj
    fin_cases j <;> simp_all [latticeIsEdge, spectralPlaquetteCell, latticeUpperFace]

private theorem spectralPlaquetteEdgeAxis_lower0 (x : LatticePoint) :
    latticeLinkAxisCell
      (latticeLowerFace (spectralPlaquetteCell x) 0 (latticePointCoordinate x 0)) 1 := by
  constructor
  · simp [latticeIsEdge, spectralPlaquetteCell, latticeLowerFace]
  · intro j hj
    fin_cases j <;> simp_all [latticeIsEdge, spectralPlaquetteCell, latticeLowerFace]

private theorem spectralPlaquetteEdgeAxis_upper1 (x : LatticePoint) :
    latticeLinkAxisCell
      (latticeUpperFace (spectralPlaquetteCell x) 1 (latticePointCoordinate x 1)) 0 := by
  constructor
  · simp [latticeIsEdge, spectralPlaquetteCell, latticeUpperFace]
  · intro j hj
    fin_cases j <;> simp_all [latticeIsEdge, spectralPlaquetteCell, latticeUpperFace]

private theorem spectralPlaquetteEdgeAxis_lower1 (x : LatticePoint) :
    latticeLinkAxisCell
      (latticeLowerFace (spectralPlaquetteCell x) 1 (latticePointCoordinate x 1)) 0 := by
  constructor
  · simp [latticeIsEdge, spectralPlaquetteCell, latticeLowerFace]
  · intro j hj
    fin_cases j <;> simp_all [latticeIsEdge, spectralPlaquetteCell, latticeLowerFace]

private theorem spectralDegree_eq_one_of_linkAxis (c : LatticeCell 4) (i : Fin 4)
    (h : latticeLinkAxisCell c i) : latticeCellDegree c = 1 := by
  classical
  change (Fourier.latticeCellAxes c).card = 1
  have haxes : Fourier.latticeCellAxes c = {i} := by
    ext j
    simp only [Fourier.latticeCellAxes, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_singleton]
    by_cases hji : j = i
    · subst j
      simp [h.1]
    · simpa [hji] using h.2 j hji
  rw [haxes]
  simp

private theorem spectralPlaquetteBoundary_apply_zero_of_degree_ne_one
    (x : LatticePoint) (c : LatticeCell 4) (hc : latticeCellDegree c ≠ 1) :
    globalBoundary (Finsupp.single (spectralPlaquetteCell x) (1 : ℝ)) c = 0 := by
  change Gaussian.realLatticeBoundary
    (Finsupp.single (spectralPlaquetteCell x) (1 : ℝ)) c = 0
  rw [Gaussian.realLatticeBoundary_basis, spectralPlaquetteCell_boundaryBasis]
  have hedges :
      latticeCellDegree
          (latticeUpperFace (spectralPlaquetteCell x) 0 (latticePointCoordinate x 0)) = 1 ∧
      latticeCellDegree
          (latticeLowerFace (spectralPlaquetteCell x) 0 (latticePointCoordinate x 0)) = 1 ∧
      latticeCellDegree
          (latticeUpperFace (spectralPlaquetteCell x) 1 (latticePointCoordinate x 1)) = 1 ∧
      latticeCellDegree
          (latticeLowerFace (spectralPlaquetteCell x) 1 (latticePointCoordinate x 1)) = 1 := by
    exact ⟨spectralDegree_eq_one_of_linkAxis _ _ (spectralPlaquetteEdgeAxis_upper0 x),
      spectralDegree_eq_one_of_linkAxis _ _ (spectralPlaquetteEdgeAxis_lower0 x),
      spectralDegree_eq_one_of_linkAxis _ _ (spectralPlaquetteEdgeAxis_upper1 x),
      spectralDegree_eq_one_of_linkAxis _ _ (spectralPlaquetteEdgeAxis_lower1 x)⟩
  simp only [latticeBasis, castLatticeChain]
  rcases hedges with ⟨hu0, hl0, hu1, hl1⟩
  have hne0 : latticeUpperFace (spectralPlaquetteCell x) 0
      (latticePointCoordinate x 0) ≠ c := by
    intro heq
    subst c
    exact hc hu0
  have hne1 : latticeLowerFace (spectralPlaquetteCell x) 0
      (latticePointCoordinate x 0) ≠ c := by
    intro heq
    subst c
    exact hc hl0
  have hne2 : latticeUpperFace (spectralPlaquetteCell x) 1
      (latticePointCoordinate x 1) ≠ c := by
    intro heq
    subst c
    exact hc hu1
  have hne3 : latticeLowerFace (spectralPlaquetteCell x) 1
      (latticePointCoordinate x 1) ≠ c := by
    intro heq
    subst c
    exact hc hl1
  simp [hne0, hne1, hne2, hne3]

private theorem spectralPlaquetteGlobalBoundary_support_degree_one (x : LatticePoint) :
    ∀ c ∈ (globalBoundary
      (Finsupp.single (spectralPlaquetteCell x) (1 : ℝ))).support,
      latticeCellDegree c = 1 := by
  intro c hc
  by_contra hdegree
  have hzero := spectralPlaquetteBoundary_apply_zero_of_degree_ne_one x c hdegree
  exact (Finsupp.mem_support_iff.mp hc) hzero

private theorem spectralPlaquetteBoundaryBoundary (x : LatticePoint) :
    latticeBoundary (latticeBoundaryBasis (spectralPlaquetteCell x)) = 0 := by
  rw [spectralPlaquetteCell_boundaryBasis]
  simp only [map_sub, map_add, latticeBoundary_basis]
  rw [latticeBoundaryBasis_link _ _ (spectralPlaquetteEdgeAxis_upper0 x),
      latticeBoundaryBasis_link _ _ (spectralPlaquetteEdgeAxis_lower0 x),
      latticeBoundaryBasis_link _ _ (spectralPlaquetteEdgeAxis_upper1 x),
      latticeBoundaryBasis_link _ _ (spectralPlaquetteEdgeAxis_lower1 x)]
  have hUU :
      latticeUpperFace (latticeUpperFace (spectralPlaquetteCell x) 0
          (latticePointCoordinate x 0)) 1
        (Sum.elim id id
          (latticeUpperFace (spectralPlaquetteCell x) 0 (latticePointCoordinate x 0) 1)) =
      latticeUpperFace (latticeUpperFace (spectralPlaquetteCell x) 1
          (latticePointCoordinate x 1)) 0
        (Sum.elim id id
          (latticeUpperFace (spectralPlaquetteCell x) 1 (latticePointCoordinate x 1) 0)) := by
    funext i
    fin_cases i <;> simp [latticeUpperFace, spectralPlaquetteCell, latticePointCoordinate]
  have hUL :
      latticeLowerFace (latticeUpperFace (spectralPlaquetteCell x) 0
          (latticePointCoordinate x 0)) 1
        (Sum.elim id id
          (latticeUpperFace (spectralPlaquetteCell x) 0 (latticePointCoordinate x 0) 1)) =
      latticeUpperFace (latticeLowerFace (spectralPlaquetteCell x) 1
          (latticePointCoordinate x 1)) 0
        (Sum.elim id id
          (latticeLowerFace (spectralPlaquetteCell x) 1 (latticePointCoordinate x 1) 0)) := by
    funext i
    fin_cases i <;>
      simp [latticeUpperFace, latticeLowerFace, spectralPlaquetteCell,
        latticePointCoordinate]
  have hLU :
      latticeUpperFace (latticeLowerFace (spectralPlaquetteCell x) 0
          (latticePointCoordinate x 0)) 1
        (Sum.elim id id
          (latticeLowerFace (spectralPlaquetteCell x) 0 (latticePointCoordinate x 0) 1)) =
      latticeLowerFace (latticeUpperFace (spectralPlaquetteCell x) 1
          (latticePointCoordinate x 1)) 0
        (Sum.elim id id
          (latticeUpperFace (spectralPlaquetteCell x) 1 (latticePointCoordinate x 1) 0)) := by
    funext i
    fin_cases i <;>
      simp [latticeUpperFace, latticeLowerFace, spectralPlaquetteCell,
        latticePointCoordinate]
  have hLL :
      latticeLowerFace (latticeLowerFace (spectralPlaquetteCell x) 0
          (latticePointCoordinate x 0)) 1
        (Sum.elim id id
          (latticeLowerFace (spectralPlaquetteCell x) 0 (latticePointCoordinate x 0) 1)) =
      latticeLowerFace (latticeLowerFace (spectralPlaquetteCell x) 1
          (latticePointCoordinate x 1)) 0
        (Sum.elim id id
          (latticeLowerFace (spectralPlaquetteCell x) 1 (latticePointCoordinate x 1) 0)) := by
    funext i
    fin_cases i <;>
      simp [latticeLowerFace, spectralPlaquetteCell, latticePointCoordinate]
  rw [hUU, hUL, hLU, hLL]
  ext v
  simp [latticeBasis, Finsupp.single_apply]
  ring_nf

private theorem spectralCastBoundary_add (q r : LatticeChain 4) :
    castLatticeChain (q + r) = castLatticeChain q + castLatticeChain r := by
  ext c
  simp [castLatticeChain]

private theorem spectralCastBoundary_zsmul (z : ℤ) (q : LatticeChain 4) :
    castLatticeChain (z • q) = (z : ℝ) • castLatticeChain q := by
  ext c
  simp [castLatticeChain]

private theorem spectralCastBoundary_sub (q r : LatticeChain 4) :
    castLatticeChain (q - r) = castLatticeChain q - castLatticeChain r := by
  ext c
  simp [castLatticeChain]

private theorem spectralCastBoundary_basis (c : LatticeCell 4) :
    castLatticeChain (latticeBasis c) = Finsupp.single c (1 : ℝ) := by
  ext d
  simp [castLatticeChain, latticeBasis]

private theorem spectralRealBoundary_cast (q : LatticeChain 4) :
    Gaussian.realLatticeBoundary (castLatticeChain q) =
      castLatticeChain (latticeBoundary q) := by
  classical
  induction q using Finsupp.induction_linear with
  | zero => simp [castLatticeChain]
  | add q r hq hr =>
      rw [spectralCastBoundary_add, map_add, hq, hr,
        latticeBoundary.map_add, spectralCastBoundary_add]
  | single c z =>
      have hsingle : Finsupp.single c z = z • Finsupp.single c (1 : ℤ) := by
        ext d
        by_cases h : d = c <;> simp [h]
      rw [hsingle, map_smul, spectralCastBoundary_zsmul,
        map_smul, spectralCastBoundary_zsmul]
      simp [Gaussian.realLatticeBoundary_basis, latticeBoundary,
        castLatticeChain]

private theorem spectralPlaquetteGlobalBoundaryBoundary (x : LatticePoint) :
    globalBoundary (globalBoundary
      (Finsupp.single (spectralPlaquetteCell x) (1 : ℝ))) = 0 := by
  change Gaussian.realLatticeBoundary (Gaussian.realLatticeBoundary
    (Finsupp.single (spectralPlaquetteCell x) (1 : ℝ))) = 0
  rw [Gaussian.realLatticeBoundary_basis, spectralRealBoundary_cast]
  have h := spectralPlaquetteBoundaryBoundary x
  rw [h]
  simp [castLatticeChain]

private theorem spectralCurvatureWindow_boundaryBoundary (a : LatticePoint →₀ ℝ) :
    globalBoundary (globalBoundary
      (Finsupp.embDomain spectralPlaquetteCellEmbedding a)) = 0 := by
  classical
  induction a using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb =>
      rw [Finsupp.embDomain_add]
      simp only [map_add, ha, hb]
      simp
  | single x z =>
      have hsingle : Finsupp.single (spectralPlaquetteCell x) z =
          z • Finsupp.single (spectralPlaquetteCell x) (1 : ℝ) := by
        ext c
        by_cases h : c = spectralPlaquetteCell x <;> simp [h]
      simp only [Finsupp.embDomain_single]
      change globalBoundary (globalBoundary
        (Finsupp.single (spectralPlaquetteCell x) z)) = 0
      rw [hsingle]
      simp only [map_smul]
      simp [spectralPlaquetteGlobalBoundaryBoundary]

theorem spectralCurvatureWindow_boundary_support (a : LatticePoint →₀ ℝ) :
    ∀ c ∈ (globalBoundary
      (Finsupp.embDomain spectralPlaquetteCellEmbedding a)).support,
      latticeCellDegree c = 1 := by
  classical
  induction a using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb =>
      intro c hc
      rw [Finsupp.embDomain_add, map_add] at hc
      have hsub :
          (globalBoundary (Finsupp.embDomain spectralPlaquetteCellEmbedding a) +
            globalBoundary (Finsupp.embDomain spectralPlaquetteCellEmbedding b)).support ⊆
            (globalBoundary (Finsupp.embDomain spectralPlaquetteCellEmbedding a)).support ∪
              (globalBoundary (Finsupp.embDomain spectralPlaquetteCellEmbedding b)).support :=
        Finsupp.support_add
      rcases Finset.mem_union.mp (hsub hc) with hca | hcb
      · exact ha c hca
      · exact hb c hcb
  | single x z =>
      intro c hc
      simp only [Finsupp.embDomain_single] at hc
      change c ∈ (globalBoundary
        (Finsupp.single (spectralPlaquetteCell x) z)).support at hc
      have hsingle : Finsupp.single (spectralPlaquetteCell x) z =
          z • Finsupp.single (spectralPlaquetteCell x) (1 : ℝ) := by
        ext d
        by_cases h : d = spectralPlaquetteCell x <;> simp [h]
      rw [hsingle, map_smul] at hc
      exact spectralPlaquetteGlobalBoundary_support_degree_one x c
        ((Finsupp.support_smul : (z •
          globalBoundary (Finsupp.single (spectralPlaquetteCell x) (1 : ℝ))).support ⊆
            (globalBoundary (Finsupp.single (spectralPlaquetteCell x) (1 : ℝ))).support) hc)

noncomputable def spectralCurvatureWindowSource
    (a : LatticePoint →₀ ℝ) : GlobalLinkField :=
  ⟨globalBoundary (Finsupp.embDomain spectralPlaquetteCellEmbedding a),
    spectralCurvatureWindow_boundary_support a⟩

theorem spectralCurvatureWindowSource_coClosed (a : LatticePoint →₀ ℝ) :
    globallyCoClosed (spectralCurvatureWindowSource a) := by
  change globalBoundary (globalBoundary
    (Finsupp.embDomain spectralPlaquetteCellEmbedding a)) = 0
  exact spectralCurvatureWindow_boundaryBoundary a

private theorem spectralLinkAxes_iff_singleton (c : LatticeCell 4) (i : Fin 4) :
    latticeLinkAxisCell c i ↔ Fourier.latticeCellAxes c = {i} := by
  constructor
  · exact latticeLinkAxis_singleton c i
  · intro haxes
    constructor
    · have hi : i ∈ Fourier.latticeCellAxes c := by rw [haxes]; simp
      simpa [Fourier.latticeCellAxes] using hi
    · intro j hji hj
      have hjmem : j ∈ Fourier.latticeCellAxes c := by
        simpa [Fourier.latticeCellAxes] using hj
      rw [haxes] at hjmem
      exact hji (Finset.mem_singleton.mp hjmem)

private theorem spectralGlobalLinkFourierComponent_eq_chain
    (μ : GlobalLinkField) (i : Fin 4) (k : Torus4) :
    globalLinkFourierComponent μ i k =
      Fourier.latticeChainFourierComponent (μ : RealLatticeChain 4) {i} k := by
  classical
  have hfilter : globalLinkAxisSupport μ i =
      μ.1.support.filter (fun c => Fourier.latticeCellAxes c = {i}) := by
    ext c
    simp only [globalLinkAxisSupport, Finset.mem_filter]
    constructor
    · rintro ⟨hc, ha⟩
      exact ⟨hc, (spectralLinkAxes_iff_singleton c i).mp ha⟩
    · rintro ⟨hc, ha⟩
      exact ⟨hc, (spectralLinkAxes_iff_singleton c i).mpr ha⟩
  unfold globalLinkFourierComponent Fourier.latticeChainFourierComponent
  rw [hfilter]

private theorem spectralFourierFunctional_basis
    (i : Fin 4) (k : Torus4) (c : LatticeCell 4) :
    Fourier.latticeChainFourierFunctional {i} k (Finsupp.single c (1 : ℝ)) =
      if Fourier.latticeCellAxes c = {i} then
        latticeCharacter (latticeCellPoint c) k else 0 := by
  simp [Fourier.latticeChainFourierFunctional, Finsupp.linearCombination_apply]


private theorem spectralPlaquetteBoundary_fourier_component
    (x : LatticePoint) (k : Torus4) (i : Fin 4) :
    globalLinkFourierComponent
      (spectralCurvatureWindowSource (Finsupp.single x (1 : ℝ))) i k =
      if i = 0 then
        -((fourier (-1) (torus4Coord k 1) - 1) * latticeCharacter x k)
      else if i = 1 then
        (fourier (-1) (torus4Coord k 0) - 1) * latticeCharacter x k
      else 0 := by
  rw [spectralGlobalLinkFourierComponent_eq_chain,
    Fourier.latticeChainFourierComponent_eq_functional]
  change Fourier.latticeChainFourierFunctional {i} k
    (globalBoundary (Finsupp.embDomain spectralPlaquetteCellEmbedding
      (Finsupp.single x (1 : ℝ)))) = _
  rw [Finsupp.embDomain_single]
  change Fourier.latticeChainFourierFunctional {i} k
    (Gaussian.realLatticeBoundary (Finsupp.single (spectralPlaquetteCell x) (1 : ℝ))) = _
  rw [Gaussian.realLatticeBoundary_basis, spectralPlaquetteCell_boundaryBasis]
  simp only [spectralCastBoundary_add, spectralCastBoundary_sub, map_add, map_sub]
  have haxesU0 : Fourier.latticeCellAxes
      (latticeUpperFace (spectralPlaquetteCell x) 0 (latticePointCoordinate x 0)) = {1} :=
    latticeLinkAxis_singleton _ _ (spectralPlaquetteEdgeAxis_upper0 x)
  have haxesL0 : Fourier.latticeCellAxes
      (latticeLowerFace (spectralPlaquetteCell x) 0 (latticePointCoordinate x 0)) = {1} :=
    latticeLinkAxis_singleton _ _ (spectralPlaquetteEdgeAxis_lower0 x)
  have haxesU1 : Fourier.latticeCellAxes
      (latticeUpperFace (spectralPlaquetteCell x) 1 (latticePointCoordinate x 1)) = {0} :=
    latticeLinkAxis_singleton _ _ (spectralPlaquetteEdgeAxis_upper1 x)
  have haxesL1 : Fourier.latticeCellAxes
      (latticeLowerFace (spectralPlaquetteCell x) 1 (latticePointCoordinate x 1)) = {0} :=
    latticeLinkAxis_singleton _ _ (spectralPlaquetteEdgeAxis_lower1 x)
  rw [spectralCastBoundary_basis, spectralCastBoundary_basis,
    spectralCastBoundary_basis, spectralCastBoundary_basis]
  rw [spectralFourierFunctional_basis, spectralFourierFunctional_basis,
    spectralFourierFunctional_basis, spectralFourierFunctional_basis]
  simp only [haxesU0, haxesL0, haxesU1, haxesL1]
  have hcoord0 : (spectralPlaquetteCell x) 0 = Sum.inr (latticePointCoordinate x 0) := by
    simp [spectralPlaquetteCell]
  have hcoord1 : (spectralPlaquetteCell x) 1 = Sum.inr (latticePointCoordinate x 1) := by
    simp [spectralPlaquetteCell]
  rw [char_upperFace _ 0 _ hcoord0, char_lowerFace _ 0 _ hcoord0,
    char_upperFace _ 1 _ hcoord1, char_lowerFace _ 1 _ hcoord1]
  simp only [spectralPlaquetteCell_point]
  fin_cases i <;> norm_num <;> ring

private noncomputable def spectralScalarFourier (a : LatticePoint →₀ ℝ)
    (k : Torus4) : ℂ :=
  a.sum fun x r => (r : ℂ) * latticeCharacter x k

private theorem spectralScalarFourier_realPartCoefficients
    (f : FiniteRealTest) (k : Torus4) :
    spectralScalarFourier (realPartCoefficients f) k = realFourierPoly f k := by
  classical
  let a := realPartCoefficients f
  have hpoly : realFourierPoly f k =
      ∑ x ∈ a.support, (a x : ℂ) * latticeCharacter x k := by
    dsimp [a, realFourierPoly]
    simp only [ContinuousMap.sum_apply, ContinuousMap.smul_apply,
      Complex.real_smul, charMap]
    calc
      (∑ x ∈ f.support, (f x).re * latticeCharacter x k) =
          ∑ x ∈ f.support, (a x : ℂ) * latticeCharacter x k := by
        apply Finset.sum_congr rfl
        intro x hx
        simp [a, realPartCoefficients_apply]
      _ = ∑ x ∈ a.support, (a x : ℂ) * latticeCharacter x k := by
        symm
        apply Finset.sum_subset (realPartCoefficients_support_subset f)
        intro x hx hnot
        have hzero : a x = 0 := Finsupp.notMem_support_iff.mp hnot
        simp [hzero]
  calc
    spectralScalarFourier (realPartCoefficients f) k =
        ∑ x ∈ a.support, (a x : ℂ) * latticeCharacter x k := by
      unfold spectralScalarFourier
      rfl
    _ = realFourierPoly f k := hpoly.symm

private theorem spectralScalarFourier_add (a b : LatticePoint →₀ ℝ) (k : Torus4) :
    spectralScalarFourier (a + b) k = spectralScalarFourier a k + spectralScalarFourier b k := by
  unfold spectralScalarFourier
  rw [Finsupp.sum_add_index' (by intro x; simp)
    (by intro x r s; simp [add_mul])]

private theorem spectralScalarFourier_smul (r : ℝ) (a : LatticePoint →₀ ℝ)
    (k : Torus4) :
    spectralScalarFourier (r • a) k = (r : ℂ) * spectralScalarFourier a k := by
  unfold spectralScalarFourier
  rw [Finsupp.sum_smul_index (by intro x; simp)]
  change (∑ x ∈ a.support, ((r * a x : ℝ) : ℂ) * latticeCharacter x k) =
    (r : ℂ) * ∑ x ∈ a.support, (a x : ℂ) * latticeCharacter x k
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  push_cast
  ring


private theorem spectralCurvatureWindowSource_smul (r : ℝ)
    (a : LatticePoint →₀ ℝ) :
  (spectralCurvatureWindowSource (r • a) : RealLatticeChain 4) =
      r • (spectralCurvatureWindowSource a : RealLatticeChain 4) := by
  change globalBoundary (Finsupp.embDomain spectralPlaquetteCellEmbedding (r • a)) =
    r • globalBoundary (Finsupp.embDomain spectralPlaquetteCellEmbedding a)
  have hemb : Finsupp.embDomain spectralPlaquetteCellEmbedding (r • a) =
      r • Finsupp.embDomain spectralPlaquetteCellEmbedding a := by
    ext c
    simp [Finsupp.embDomain_apply]
  rw [hemb, map_smul]

private noncomputable def spectralPlaquetteCurlSymbol (i : Fin 4) (k : Torus4) : ℂ :=
  if i = 0 then
    -((fourier (-1) (torus4Coord k 1) - 1))
  else if i = 1 then
    fourier (-1) (torus4Coord k 0) - 1
  else 0

private theorem spectralSourceFourier_eq_functional
    (a : LatticePoint →₀ ℝ) (i : Fin 4) (k : Torus4) :
    globalLinkFourierComponent (spectralCurvatureWindowSource a) i k =
      Fourier.latticeChainFourierFunctional {i} k
        (globalBoundary (Finsupp.embDomain spectralPlaquetteCellEmbedding a)) := by
  rw [spectralGlobalLinkFourierComponent_eq_chain,
    Fourier.latticeChainFourierComponent_eq_functional]
  rfl

private theorem spectralSourceFourierComponent_smul (r : ℝ)
    (a : LatticePoint →₀ ℝ) (i : Fin 4) (k : Torus4) :
    globalLinkFourierComponent (spectralCurvatureWindowSource (r • a)) i k =
      (r : ℂ) * globalLinkFourierComponent (spectralCurvatureWindowSource a) i k := by
  rw [spectralSourceFourier_eq_functional (r • a) i k,
    spectralSourceFourier_eq_functional a i k]
  change Fourier.latticeChainFourierFunctional {i} k
      (spectralCurvatureWindowSource (r • a) : RealLatticeChain 4) =
      (r : ℂ) * Fourier.latticeChainFourierFunctional {i} k
        (spectralCurvatureWindowSource a : RealLatticeChain 4)
  rw [spectralCurvatureWindowSource_smul, map_smul, Complex.real_smul]

private theorem spectralScalarFourier_single (x : LatticePoint) (r : ℝ) (k : Torus4) :
    spectralScalarFourier (Finsupp.single x r) k = (r : ℂ) * latticeCharacter x k := by
  simp [spectralScalarFourier]

private theorem spectralSourceFourierComponent_formula
    (a : LatticePoint →₀ ℝ) (i : Fin 4) (k : Torus4) :
    globalLinkFourierComponent (spectralCurvatureWindowSource a) i k =
      spectralPlaquetteCurlSymbol i k * spectralScalarFourier a k := by
  classical
  induction a using Finsupp.induction_linear with
  | zero =>
      rw [spectralSourceFourier_eq_functional 0 i k]
      simp [Finsupp.embDomain_zero, spectralScalarFourier, spectralPlaquetteCurlSymbol]
  | add a b ha hb =>
      have hcomp : globalLinkFourierComponent
          (spectralCurvatureWindowSource (a + b)) i k =
          globalLinkFourierComponent (spectralCurvatureWindowSource a) i k +
            globalLinkFourierComponent (spectralCurvatureWindowSource b) i k := by
        rw [spectralSourceFourier_eq_functional (a + b) i k,
          spectralSourceFourier_eq_functional a i k,
          spectralSourceFourier_eq_functional b i k]
        rw [Finsupp.embDomain_add, map_add, map_add]
      rw [hcomp, ha, hb, spectralScalarFourier_add]
      ring
  | single x r =>
      have hsingle : Finsupp.single x r = r • Finsupp.single x (1 : ℝ) := by
        ext z
        by_cases hz : z = x <;> simp [hz]
      rw [hsingle, spectralSourceFourierComponent_smul,
        spectralPlaquetteBoundary_fourier_component, spectralScalarFourier_smul,
        spectralScalarFourier_single]
      simp [spectralPlaquetteCurlSymbol]
      ring_nf

private theorem spectralFourierNegative_one_conj (t : AddCircle (1 : ℝ)) :
    conj (fourier 1 t) = fourier (-1) t := by
  rw [← fourier_neg]

private theorem spectralCurlSymbol_normSq_zero (k : Torus4) :
    Complex.normSq (spectralPlaquetteCurlSymbol 0 k) = torusChordSquared k 1 := by
  have hsym : spectralPlaquetteCurlSymbol 0 k =
      conj (1 - fourier 1 (torus4Coord k 1)) := by
    have hconj := spectralFourierNegative_one_conj (torus4Coord k 1)
    change -((fourier (-1) (torus4Coord k 1)) - 1) = _
    rw [← hconj]
    simp only [map_sub, map_one]
    ring
  rw [hsym, Complex.normSq_conj]
  rfl

private theorem spectralCurlSymbol_normSq_one (k : Torus4) :
    Complex.normSq (spectralPlaquetteCurlSymbol 1 k) = torusChordSquared k 0 := by
  have hsym : spectralPlaquetteCurlSymbol 1 k =
      -conj (1 - fourier 1 (torus4Coord k 0)) := by
    have hconj := spectralFourierNegative_one_conj (torus4Coord k 0)
    change fourier (-1) (torus4Coord k 0) - 1 = _
    rw [← hconj]
    simp only [map_sub, map_one]
    ring
  rw [hsym, Complex.normSq_neg, Complex.normSq_conj]
  rfl

private theorem spectralFourierGreenDensity_source_test
    (f : FiniteRealTest) (k : Torus4) (hk : k ≠ 0) :
    fourierGreenDensity
        (spectralCurvatureWindowSource (realPartCoefficients f)) k =
      torusCurlMultiplier 0 1 k * finiteTestFourierWeight f k := by
  let a := realPartCoefficients f
  let p := realFourierPoly f k
  have hscalar : spectralScalarFourier a k = p :=
    spectralScalarFourier_realPartCoefficients f k
  have hden : fourierLaplacianSymbol k =
      ∑ i : Fin 4, torusChordSquared k i := by
    unfold fourierLaplacianSymbol torusChordSquared
    simp [Complex.normSq_eq_norm_sq]
  have hdenpos : 0 < fourierLaplacianSymbol k := by
    rw [hden]
    exact torusCurlDenominator_pos hk
  have hweight : finiteTestFourierWeight f k = Complex.normSq p := by
    simp [finiteTestFourierWeight, p, Complex.normSq_eq_norm_sq]
  have hterm0 :
      ‖globalLinkFourierComponent (spectralCurvatureWindowSource a) 0 k‖ ^ 2 =
        torusChordSquared k 1 * finiteTestFourierWeight f k := by
    rw [spectralSourceFourierComponent_formula, hscalar]
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_mul,
      spectralCurlSymbol_normSq_zero, hweight]
  have hterm1 :
      ‖globalLinkFourierComponent (spectralCurvatureWindowSource a) 1 k‖ ^ 2 =
        torusChordSquared k 0 * finiteTestFourierWeight f k := by
    rw [spectralSourceFourierComponent_formula, hscalar]
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_mul,
      spectralCurlSymbol_normSq_one, hweight]
  have hterm2 :
      ‖globalLinkFourierComponent (spectralCurvatureWindowSource a) 2 k‖ ^ 2 = 0 := by
    rw [spectralSourceFourierComponent_formula]
    simp [spectralPlaquetteCurlSymbol]
  have hterm3 :
      ‖globalLinkFourierComponent (spectralCurvatureWindowSource a) 3 k‖ ^ 2 = 0 := by
    rw [spectralSourceFourierComponent_formula]
    simp [spectralPlaquetteCurlSymbol]
  have hmult : torusCurlMultiplier 0 1 k =
      (torusChordSquared k 0 + torusChordSquared k 1) /
        (∑ i : Fin 4, torusChordSquared k i) := by
    unfold torusCurlMultiplier
    have hsum : (∑ i : Fin 4, torusChordSquared k i) ≠ 0 :=
      (torusCurlDenominator_pos hk).ne'
    simp [hsum]
  rw [fourierGreenDensity, Fin.sum_univ_four, hterm0, hterm1, hterm2, hterm3]
  rw [hden, hmult]
  have hsumNe : (∑ i : Fin 4, torusChordSquared k i) ≠ 0 :=
    (torusCurlDenominator_pos hk).ne'
  field_simp [hsumNe]
  ring

private theorem spectralFourierGreenQuadratic_source_test (f : FiniteRealTest) :
    fourierGreenQuadratic
        (spectralCurvatureWindowSource (realPartCoefficients f)) =
      ∫ k, torusCurlMultiplier 0 1 k * finiteTestFourierWeight f k ∂torus4Haar := by
  have hne : ∀ᵐ k ∂torus4Haar, k ≠ 0 := by
    filter_upwards [ae_torus4Coord_ne_zero 0] with k hk
    intro hzero
    apply hk
    simp [hzero, torus4Coord]
  have hEq : (fun k : Torus4 =>
      fourierGreenDensity
        (spectralCurvatureWindowSource (realPartCoefficients f)) k) =ᵐ[torus4Haar]
      fun k => torusCurlMultiplier 0 1 k * finiteTestFourierWeight f k := by
    filter_upwards [hne] with k hk
    exact spectralFourierGreenDensity_source_test f k hk
  unfold fourierGreenQuadratic
  exact integral_congr_ae hEq

theorem spectralCurvatureWindow_secondMoment_bounds
    {β : ℝ} (hβ : rootBetaThreshold ≤ β)
    (L : CubeCurvatureLimitState β (rootBeta_pos hβ))
    (s : ℕ → ℕ) (S : CurvatureCylinderState)
    (hpoint : ∀ P x, Tendsto
      (fun k => (averagedCylinderLaw (cubeStateToCylinderState L) (s k) P x).toReal)
      atTop (𝓝 ((S.law P x).toReal)))
    (a : LatticePoint →₀ ℝ) :
    betaDoublePrime rootPackingCoefficient β *
        fourierGreenQuadratic (spectralCurvatureWindowSource a) ≤
      ∫ x, (sourceFillingCurvaturePairing (spectralCurvatureWindow a) x) ^ 2 ∂
        (S.law (fillingCurvatureIndexSet (spectralCurvatureWindow a))).toMeasure ∧
      (∫ x, (sourceFillingCurvaturePairing (spectralCurvatureWindow a) x) ^ 2 ∂
        (S.law (fillingCurvatureIndexSet (spectralCurvatureWindow a))).toMeasure) ≤
        β * fourierGreenQuadratic (spectralCurvatureWindowSource a) := by
  have hfill : globalBoundary (spectralCurvatureWindow a : RealLatticeChain 4) =
      (spectralCurvatureWindowSource a : RealLatticeChain 4) := rfl
  exact (FroehlichSpencer.FS82.Infinite.Nonsummability.projectiveAveragedCylinderLimit_sourceFilling_secondMoment_bounds
    hβ L s S hpoint (spectralCurvatureWindowSource a)
    (spectralCurvatureWindowSource_coClosed a) (spectralCurvatureWindow a) hfill).2

theorem spectralCurvatureWindow_pairing_square_integrable
    {β : ℝ} (hβ : rootBetaThreshold ≤ β)
    (L : CubeCurvatureLimitState β (rootBeta_pos hβ))
    (s : ℕ → ℕ) (S : CurvatureCylinderState)
    (hpoint : ∀ P x, Tendsto
      (fun k => (averagedCylinderLaw (cubeStateToCylinderState L) (s k) P x).toReal)
      atTop (𝓝 ((S.law P x).toReal)))
    (a : LatticePoint →₀ ℝ) :
    Integrable
      (fun x => (sourceFillingCurvaturePairing (spectralCurvatureWindow a) x) ^ 2)
      (S.law (fillingCurvatureIndexSet (spectralCurvatureWindow a))).toMeasure := by
  have hfill : globalBoundary (spectralCurvatureWindow a : RealLatticeChain 4) =
      (spectralCurvatureWindowSource a : RealLatticeChain 4) := rfl
  exact (projectiveAveragedCylinderLimit_sourceFilling_secondMoment_bounds
    hβ L s S hpoint (spectralCurvatureWindowSource a)
    (spectralCurvatureWindowSource_coClosed a) (spectralCurvatureWindow a) hfill).1

theorem spectralPlaquetteOrientation (x : LatticePoint) :
    Gaussian.latticeCellOrientationSign (spectralPlaquetteCell x) = -1 := by
  have haxes : Gaussian.latticeCellAxes (spectralPlaquetteCell x) = {0, 1} := by
    change Fourier.latticeCellAxes (spectralPlaquetteCell x) = _
    exact spectralPlaquetteCell_axes x
  rw [Gaussian.latticeCellOrientationSign, haxes, Gaussian.axisSetOrientationSign]
  norm_num [Finset.sum_pair, Finset.card_pair]

theorem spectralWindowIndex_mem (a : LatticePoint →₀ ℝ) (x : LatticePoint)
    (hx : x ∈ a.support) :
    spectralPlaquetteAt x ∈ fillingCurvatureIndexSet (spectralCurvatureWindow a) := by
  classical
  change spectralPlaquetteAt x ∈
    ((Finsupp.embDomain spectralPlaquetteCellEmbedding a).support.attach).map
      (fillingPlaquetteEmbedding (spectralCurvatureWindow a))
  have hcell : spectralPlaquetteCell x ∈
      (Finsupp.embDomain spectralPlaquetteCellEmbedding a).support := by
    rw [Finsupp.support_embDomain]
    exact Finset.mem_map.mpr ⟨x, hx, rfl⟩
  refine Finset.mem_map.mpr ⟨⟨spectralPlaquetteCell x, hcell⟩,
    Finset.mem_attach _ _, ?_⟩
  apply Subtype.ext
  rfl

noncomputable def spectralWindowIndex (a : LatticePoint →₀ ℝ)
    (x : {x : LatticePoint // x ∈ a.support}) :
    fillingCurvatureIndexSet (spectralCurvatureWindow a) :=
  ⟨spectralPlaquetteAt x.1, spectralWindowIndex_mem a x.1 x.2⟩

noncomputable def spectralWindowPlaquetteEmbedding (a : LatticePoint →₀ ℝ) :
    {x : LatticePoint // x ∈ a.support} ↪ GlobalIntegerPlaquette where
  toFun x := spectralPlaquetteAt x.1
  inj' := by
    intro x y h
    apply Subtype.ext
    exact spectralPlaquetteAt_injective h

theorem spectralWindowCoordinates_eq (a : LatticePoint →₀ ℝ) :
    fillingCurvatureIndexSet (spectralCurvatureWindow a) =
      a.support.attach.map (spectralWindowPlaquetteEmbedding a) := by
  classical
  let σ := spectralCurvatureWindow a
  let C := (σ : RealLatticeChain 4).support
  have hC : C = a.support.map spectralPlaquetteCellEmbedding := by
    change (Finsupp.embDomain spectralPlaquetteCellEmbedding a).support = _
    exact Finsupp.support_embDomain spectralPlaquetteCellEmbedding a
  let E : {x : LatticePoint // x ∈ a.support} ↪ C := {
    toFun := fun x => ⟨spectralPlaquetteCell x.1, by
      rw [hC]
      exact Finset.mem_map.mpr ⟨x.1, x.2, rfl⟩⟩
    inj' := by
      intro x y h
      apply Subtype.ext
      apply spectralPlaquetteCellEmbedding.injective
      exact congrArg Subtype.val h }
  have hE : C.attach = a.support.attach.map E := by
    ext q
    constructor
    · intro hq
      have hqMap : (q.1 : LatticeCell 4) ∈
          a.support.map spectralPlaquetteCellEmbedding := by
        simpa only [hC] using q.2
      rcases Finset.mem_map.mp hqMap with ⟨x, hx, hcell⟩
      refine Finset.mem_map.mpr ⟨⟨x, hx⟩, Finset.mem_attach _ _, ?_⟩
      apply Subtype.ext
      exact hcell
    · intro hq
      exact Finset.mem_attach _ _
  have hcomp : E.trans (fillingPlaquetteEmbedding σ) =
      spectralWindowPlaquetteEmbedding a := by
    ext x i
    rfl
  calc
    fillingCurvatureIndexSet σ = C.attach.map (fillingPlaquetteEmbedding σ) := rfl
    _ = (a.support.attach.map E).map (fillingPlaquetteEmbedding σ) := by rw [hE]
    _ = a.support.attach.map (E.trans (fillingPlaquetteEmbedding σ)) := by
          rw [Finset.map_map]
    _ = a.support.attach.map (spectralWindowPlaquetteEmbedding a) := by rw [hcomp]

private theorem spectralWindow_sum (a : LatticePoint →₀ ℝ)
    (f : GlobalIntegerPlaquette → ℝ) :
    ∑ p : fillingCurvatureIndexSet (spectralCurvatureWindow a), f p.1 =
      ∑ x ∈ a.support.attach, f (spectralPlaquetteAt x.1) := by
  classical
  let σ := spectralCurvatureWindow a
  let C := (σ : RealLatticeChain 4).support
  have hC : C = a.support.map spectralPlaquetteCellEmbedding := by
    change (Finsupp.embDomain spectralPlaquetteCellEmbedding a).support = _
    exact Finsupp.support_embDomain spectralPlaquetteCellEmbedding a
  let E : {x : LatticePoint // x ∈ a.support} ↪ C := {
    toFun := fun x => ⟨spectralPlaquetteCell x.1, by
      rw [hC]
      exact Finset.mem_map.mpr ⟨x.1, x.2, rfl⟩⟩
    inj' := by
      intro x y h
      apply Subtype.ext
      apply spectralPlaquetteCellEmbedding.injective
      exact congrArg Subtype.val h }
  have hE : C.attach = a.support.attach.map E := by
    ext q
    constructor
    · intro hq
      have hqC : (q.1 : LatticeCell 4) ∈ C := q.2
      have hqMap : (q.1 : LatticeCell 4) ∈
          a.support.map spectralPlaquetteCellEmbedding := by
        simpa only [hC] using hqC
      rcases Finset.mem_map.mp hqMap with ⟨x, hx, hcell⟩
      refine Finset.mem_map.mpr ⟨⟨x, hx⟩, Finset.mem_attach _ _, ?_⟩
      apply Subtype.ext
      exact hcell
    · intro hq
      rcases Finset.mem_map.mp hq with ⟨x, hx, hqE⟩
      exact Finset.mem_attach _ _
  calc
    ∑ p : fillingCurvatureIndexSet σ, f p.1 =
        ∑ p ∈ fillingCurvatureIndexSet σ, f p := Finset.sum_coe_sort _ _
    _ = ∑ q ∈ C.attach, f (fillingPlaquetteEmbedding σ q) := by
          rw [fillingCurvatureIndexSet, Finset.sum_map]
    _ = ∑ q ∈ a.support.attach, f (fillingPlaquetteEmbedding σ (E q)) := by
          rw [hE, Finset.sum_map]
    _ = ∑ q ∈ a.support.attach, f (spectralPlaquetteAt q.1) := by
          apply Finset.sum_congr rfl
          intro q hq
          rfl

theorem spectralWindowIndex_pairing (a : LatticePoint →₀ ℝ)
    (ω : fillingCurvatureIndexSet (spectralCurvatureWindow a) → ℤ) :
    sourceFillingCurvaturePairing (spectralCurvatureWindow a) ω =
      -∑ x ∈ a.support.attach, a x.1 * (ω (spectralWindowIndex a x) : ℝ) := by
  classical
  let σ := spectralCurvatureWindow a
  let P := fillingCurvatureIndexSet σ
  let f : GlobalIntegerPlaquette → ℝ := fun p =>
    if hp : p ∈ P then
      Gaussian.latticeCellOrientationSign p.1 *
        fillingPlaquetteCoeff σ ⟨p, hp⟩ * (ω ⟨p, hp⟩ : ℝ)
    else 0
  have hsum : sourceFillingCurvaturePairing σ ω =
      ∑ p : P, f p.1 := by
    unfold sourceFillingCurvaturePairing
    apply Finset.sum_congr rfl
    intro p hp
    simp [f, P]
  rw [hsum, spectralWindow_sum]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  have hmem : spectralPlaquetteAt x.1 ∈ P := spectralWindowIndex_mem a x.1 x.2
  have hindex : spectralWindowIndex a x = ⟨spectralPlaquetteAt x.1, hmem⟩ := by
    apply Subtype.ext
    rfl
  simp only [f, dite_eq_left hmem]
  rw [hindex]
  rw [show Gaussian.latticeCellOrientationSign
      (spectralPlaquetteAt x.1).1 = -1 by exact spectralPlaquetteOrientation x.1]
  change (-1 : ℝ) *
    (Finsupp.embDomain spectralPlaquetteCellEmbedding a) (spectralPlaquetteCell x.1) *
      (ω (⟨spectralPlaquetteAt x.1, hmem⟩ : fillingCurvatureIndexSet σ) : ℝ) = _
  have hcoeff :
      (Finsupp.embDomain spectralPlaquetteCellEmbedding a) (spectralPlaquetteCell x.1) =
        a x.1 := by
    simpa [spectralPlaquetteCellEmbedding] using
      (Finsupp.embDomain_apply_self spectralPlaquetteCellEmbedding a x.1)
  rw [hcoeff]
  ring

noncomputable def spectralPairSumTest (x y : LatticePoint) : LatticePoint →₀ ℝ :=
  Finsupp.single x 1 + Finsupp.single y 1

noncomputable def spectralPairDifferenceTest (x y : LatticePoint) : LatticePoint →₀ ℝ :=
  Finsupp.single x 1 - Finsupp.single y 1

theorem spectralPairSumTest_support {x y : LatticePoint} (hxy : x ≠ y) :
    (spectralPairSumTest x y).support = {x, y} := by
  classical
  ext z
  by_cases hx : z = x
  · subst z
    simp [spectralPairSumTest, hxy]
  · by_cases hy : z = y
    · subst z
      simp [spectralPairSumTest, hxy]
    · simp [spectralPairSumTest, hx, hy]

theorem spectralPairDifferenceTest_support {x y : LatticePoint} (hxy : x ≠ y) :
    (spectralPairDifferenceTest x y).support = {x, y} := by
  classical
  ext z
  by_cases hx : z = x
  · subst z
    simp [spectralPairDifferenceTest, hxy]
  · by_cases hy : z = y
    · subst z
      simp [spectralPairDifferenceTest, hxy]
    · simp [spectralPairDifferenceTest, hx, hy]

theorem spectralPairWindow_coordinates_eq {x y : LatticePoint} (hxy : x ≠ y) :
    fillingCurvatureIndexSet
        (spectralCurvatureWindow (spectralPairSumTest x y)) = spectralPairPlaquettes x y := by
  classical
  calc
    fillingCurvatureIndexSet (spectralCurvatureWindow (spectralPairSumTest x y)) =
        (spectralPairSumTest x y).support.attach.map
          (spectralWindowPlaquetteEmbedding (spectralPairSumTest x y)) :=
      spectralWindowCoordinates_eq _
    _ = spectralPairPlaquettes x y := by
      ext p
      constructor
      · intro hp
        rcases Finset.mem_map.mp hp with ⟨z, hz, hpz⟩
        change spectralPlaquetteAt z.1 = p at hpz
        subst p
        have hzval : (spectralPairSumTest x y) z.1 ≠ 0 :=
          Finsupp.mem_support_iff.mp z.2
        by_cases hzx : z.1 = x
        · simp [spectralPairPlaquettes, hzx]
        · by_cases hzy : z.1 = y
          · simp [spectralPairPlaquettes, hzy]
          · simp [spectralPairSumTest, hzx, hzy] at hzval
      · intro hp
        simp [spectralPairPlaquettes] at hp
        rcases hp with hp | hp
        · subst p
          refine Finset.mem_map.mpr ⟨⟨x, ?_⟩, Finset.mem_attach _ _, rfl⟩
          apply Finsupp.mem_support_iff.mpr
          simp [spectralPairSumTest, hxy]
        · subst p
          refine Finset.mem_map.mpr ⟨⟨y, ?_⟩, Finset.mem_attach _ _, rfl⟩
          apply Finsupp.mem_support_iff.mpr
          simp [spectralPairSumTest, hxy]

theorem spectralPairDifferenceWindow_coordinates_eq {x y : LatticePoint}
    (hxy : x ≠ y) :
    fillingCurvatureIndexSet
        (spectralCurvatureWindow (spectralPairDifferenceTest x y)) = spectralPairPlaquettes x y := by
  classical
  calc
    fillingCurvatureIndexSet (spectralCurvatureWindow (spectralPairDifferenceTest x y)) =
        (spectralPairDifferenceTest x y).support.attach.map
          (spectralWindowPlaquetteEmbedding (spectralPairDifferenceTest x y)) :=
      spectralWindowCoordinates_eq _
    _ = spectralPairPlaquettes x y := by
      ext p
      constructor
      · intro hp
        rcases Finset.mem_map.mp hp with ⟨z, hz, hpz⟩
        change spectralPlaquetteAt z.1 = p at hpz
        subst p
        have hzval : (spectralPairDifferenceTest x y) z.1 ≠ 0 :=
          Finsupp.mem_support_iff.mp z.2
        by_cases hzx : z.1 = x
        · simp [spectralPairPlaquettes, hzx]
        · by_cases hzy : z.1 = y
          · simp [spectralPairPlaquettes, hzy]
          · simp [spectralPairDifferenceTest, hzx, hzy] at hzval
      · intro hp
        simp [spectralPairPlaquettes] at hp
        rcases hp with hp | hp
        · subst p
          refine Finset.mem_map.mpr ⟨⟨x, ?_⟩, Finset.mem_attach _ _, rfl⟩
          apply Finsupp.mem_support_iff.mpr
          simp [spectralPairDifferenceTest, hxy]
        · subst p
          refine Finset.mem_map.mpr ⟨⟨y, ?_⟩, Finset.mem_attach _ _, rfl⟩
          apply Finsupp.mem_support_iff.mpr
          simp [spectralPairDifferenceTest, hxy]

noncomputable def spectralPairProduct (x y : LatticePoint)
    (ω : spectralPairPlaquettes x y → ℤ) : ℝ :=
  (ω (spectralPairIndex x y x (by simp [spectralPairPlaquettes])) : ℝ) *
  (ω (spectralPairIndex x y y (by simp [spectralPairPlaquettes])) : ℝ)

private theorem spectralSubtypeSum_pair {α : Type*} [DecidableEq α]
    (x y : α) (hxy : x ≠ y) (s : Finset α) (hs : s = {x, y})
    (f : {z // z ∈ s} → ℝ) :
    (∑ z : s, f z) = f ⟨x, by rw [hs]; simp⟩ + f ⟨y, by rw [hs]; simp⟩ := by
  classical
  let e : {z // z ∈ s} ≃ {z // z ∈ ({x, y} : Finset α)} :=
    Equiv.subtypeEquivRight (fun z => by rw [hs])
  let g : α → ℝ := fun z =>
    if hz : z ∈ ({x, y} : Finset α) then f (e.symm ⟨z, hz⟩) else 0
  calc
    (∑ z : s, f z) =
        ∑ z : {z // z ∈ ({x, y} : Finset α)}, f (e.symm z) := by
          exact Fintype.sum_equiv e _ _ (by
            intro z
            change f z = f (e.symm (e z))
            rw [Equiv.symm_apply_apply])
    _ = ∑ z ∈ ({x, y} : Finset α), g z := by
          have hfun : (fun z : {z // z ∈ ({x, y} : Finset α)} =>
              f (e.symm z)) = fun z => g z.1 := by
            funext z
            change f (e.symm z) =
              (if hz : z.1 ∈ ({x, y} : Finset α) then
                f (e.symm ⟨z.1, hz⟩) else 0)
            rw [dite_eq_left z.2]
          rw [hfun]
          exact (Finset.sum_subtype ({x, y} : Finset α)
            (fun _ => Iff.rfl) g).symm
    _ = f ⟨x, by rw [hs]; simp⟩ + f ⟨y, by rw [hs]; simp⟩ := by
          have heX : e.symm ⟨x, by simp⟩ = ⟨x, by rw [hs]; simp⟩ := by
            apply Subtype.ext
            rfl
          have heY : e.symm ⟨y, by simp⟩ = ⟨y, by rw [hs]; simp⟩ := by
            apply Subtype.ext
            rfl
          simp [g, hxy, heX, heY]

private theorem spectralSubtypeSum_single {α : Type*} [DecidableEq α]
    (x : α) (s : Finset α) (hs : s = {x}) (f : {z // z ∈ s} → ℝ) :
    (∑ z : s, f z) = f ⟨x, by rw [hs]; simp⟩ := by
  classical
  let e : {z // z ∈ s} ≃ {z // z ∈ ({x} : Finset α)} :=
    Equiv.subtypeEquivRight (fun z => by rw [hs])
  let g : α → ℝ := fun z =>
    if hz : z ∈ ({x} : Finset α) then f (e.symm ⟨z, hz⟩) else 0
  calc
    (∑ z : s, f z) =
        ∑ z : {z // z ∈ ({x} : Finset α)}, f (e.symm z) := by
          exact Fintype.sum_equiv e _ _ (by
            intro z
            change f z = f (e.symm (e z))
            rw [Equiv.symm_apply_apply])
    _ = ∑ z ∈ ({x} : Finset α), g z := by
          have hfun : (fun z : {z // z ∈ ({x} : Finset α)} =>
              f (e.symm z)) = fun z => g z.1 := by
            funext z
            change f (e.symm z) =
              (if hz : z.1 ∈ ({x} : Finset α) then
                f (e.symm ⟨z.1, hz⟩) else 0)
            rw [dite_eq_left z.2]
          rw [hfun]
          exact (Finset.sum_subtype ({x} : Finset α)
            (fun _ => Iff.rfl) g).symm
    _ = f ⟨x, by rw [hs]; simp⟩ := by
          have heX : e.symm ⟨x, by simp⟩ = ⟨x, by rw [hs]; simp⟩ := by
            apply Subtype.ext
            rfl
          simp [g, heX]

theorem spectralIntegrable_finsetEq
    (S : CurvatureCylinderState) {P Q : Finset GlobalIntegerPlaquette}
    (hPQ : P = Q) (f : (P → ℤ) → ℝ)
    (hf : Integrable f (S.law P).toMeasure) :
    Integrable (fun ω : Q → ℤ =>
      f ((curvatureAssignmentCastEquiv hPQ).symm ω)) (S.law Q).toMeasure := by
  let e := curvatureAssignmentCastEquiv hPQ
  have hmap : PMF.map e (S.law P) = S.law Q :=
    curvatureCylinderLaw_map_finsetEq S hPQ
  rw [← hmap, ← PMF.toMeasure_map e (S.law P) (by fun_prop : Measurable e)]
  apply (MeasureTheory.integrable_map_measure
    (by fun_prop : AEStronglyMeasurable
      (fun ω : Q → ℤ => f (e.symm ω)) ((S.law P).toMeasure.map e))
    (by fun_prop : AEMeasurable e (S.law P).toMeasure)).2
  change Integrable (fun ω : P → ℤ => f (e.symm (e ω))) (S.law P).toMeasure
  simp only [Equiv.symm_apply_apply]
  exact hf

theorem spectralPairProduct_integrable
    {β : ℝ} (hβ : rootBetaThreshold ≤ β)
    (L : CubeCurvatureLimitState β (rootBeta_pos hβ))
    (s : ℕ → ℕ) (S : CurvatureCylinderState)
    (hpoint : ∀ P x, Tendsto
      (fun k => (averagedCylinderLaw (cubeStateToCylinderState L) (s k) P x).toReal)
      atTop (𝓝 ((S.law P x).toReal)))
    (x y : LatticePoint) :
    Integrable (spectralPairProduct x y) (S.law (spectralPairPlaquettes x y)).toMeasure := by
  classical
  by_cases hxy : x = y
  · subst y
    let a : LatticePoint →₀ ℝ := Finsupp.single x 1
    have hP : fillingCurvatureIndexSet (spectralCurvatureWindow a) =
        spectralPairPlaquettes x x := by
      calc
        fillingCurvatureIndexSet (spectralCurvatureWindow a) =
            a.support.attach.map (spectralWindowPlaquetteEmbedding a) :=
          spectralWindowCoordinates_eq _
        _ = spectralPairPlaquettes x x := by
          ext p
          simp [spectralPairPlaquettes, a, spectralWindowPlaquetteEmbedding, eq_comm]
    have hint := spectralCurvatureWindow_pairing_square_integrable hβ L s S hpoint a
    have htrans := spectralIntegrable_finsetEq S hP
      (fun ω => (sourceFillingCurvaturePairing (spectralCurvatureWindow a) ω) ^ 2) hint
    have hxSupport : x ∈ a.support := by simp [a]
    have hidx : curvatureIndexCastEquiv hP
        (spectralWindowIndex a ⟨x, hxSupport⟩) =
          spectralPairIndex x x x (by simp [spectralPairPlaquettes]) := by
      apply Subtype.ext
      simp [curvatureIndexCastEquiv_val, spectralWindowIndex, spectralPairIndex]
    have heq : (fun ω : spectralPairPlaquettes x x → ℤ =>
        (sourceFillingCurvaturePairing (spectralCurvatureWindow a)
          ((curvatureAssignmentCastEquiv hP).symm ω)) ^ 2) =
        spectralPairProduct x x := by
      funext ω
      rw [spectralWindowIndex_pairing]
      have hsupp : a.support = {x} := by simp [a]
      change (-(∑ z : a.support, a z.1 *
        ((curvatureAssignmentCastEquiv hP).symm ω (spectralWindowIndex a z) : ℝ))) ^ 2 = _
      rw [spectralSubtypeSum_single x a.support hsupp (fun z => a z.1 *
        ((curvatureAssignmentCastEquiv hP).symm ω (spectralWindowIndex a z) : ℝ))]
      rw [show (curvatureAssignmentCastEquiv hP).symm ω
          (spectralWindowIndex a ⟨x, hxSupport⟩) =
            ω (curvatureIndexCastEquiv hP (spectralWindowIndex a ⟨x, hxSupport⟩)) by rfl,
        hidx]
      have hval : a x = 1 := by simp [a]
      rw [hval]
      simp [spectralPairProduct]
      ring
    exact htrans.congr (ae_of_all _ fun ω => by rw [heq])
  · let aPlus := spectralPairSumTest x y
    let aMinus := spectralPairDifferenceTest x y
    have hPplus : fillingCurvatureIndexSet (spectralCurvatureWindow aPlus) =
        spectralPairPlaquettes x y := by
      exact spectralPairWindow_coordinates_eq hxy
    have hPminus : fillingCurvatureIndexSet (spectralCurvatureWindow aMinus) =
        spectralPairPlaquettes x y := by
      exact spectralPairDifferenceWindow_coordinates_eq hxy
    have hplus := spectralCurvatureWindow_pairing_square_integrable
      hβ L s S hpoint aPlus
    have hminus := spectralCurvatureWindow_pairing_square_integrable
      hβ L s S hpoint aMinus
    let X : (spectralPairPlaquettes x y → ℤ) → ℝ := fun ω =>
      (ω (spectralPairIndex x y x (by simp [spectralPairPlaquettes])) : ℝ)
    let Y : (spectralPairPlaquettes x y → ℤ) → ℝ := fun ω =>
      (ω (spectralPairIndex x y y (by simp [spectralPairPlaquettes])) : ℝ)
    have hxPlus : x ∈ aPlus.support := by
      rw [spectralPairSumTest_support hxy]
      simp
    have hyPlus : y ∈ aPlus.support := by
      rw [spectralPairSumTest_support hxy]
      simp
    have hxMinus : x ∈ aMinus.support := by
      rw [spectralPairDifferenceTest_support hxy]
      simp
    have hyMinus : y ∈ aMinus.support := by
      rw [spectralPairDifferenceTest_support hxy]
      simp
    have hidxPlusX : curvatureIndexCastEquiv hPplus
        (spectralWindowIndex aPlus ⟨x, hxPlus⟩) = spectralPairIndex x y x
          (by simp [spectralPairPlaquettes]) := by
      apply Subtype.ext
      simp [curvatureIndexCastEquiv_val, spectralWindowIndex, spectralPairIndex]
    have hidxPlusY : curvatureIndexCastEquiv hPplus
        (spectralWindowIndex aPlus ⟨y, hyPlus⟩) = spectralPairIndex x y y
          (by simp [spectralPairPlaquettes]) := by
      apply Subtype.ext
      simp [curvatureIndexCastEquiv_val, spectralWindowIndex, spectralPairIndex]
    have hidxMinusX : curvatureIndexCastEquiv hPminus
        (spectralWindowIndex aMinus ⟨x, hxMinus⟩) = spectralPairIndex x y x
          (by simp [spectralPairPlaquettes]) := by
      apply Subtype.ext
      simp [curvatureIndexCastEquiv_val, spectralWindowIndex, spectralPairIndex]
    have hidxMinusY : curvatureIndexCastEquiv hPminus
        (spectralWindowIndex aMinus ⟨y, hyMinus⟩) = spectralPairIndex x y y
          (by simp [spectralPairPlaquettes]) := by
      apply Subtype.ext
      simp [curvatureIndexCastEquiv_val, spectralWindowIndex, spectralPairIndex]
    have hplusTrans := spectralIntegrable_finsetEq S hPplus
      (fun ω => (sourceFillingCurvaturePairing (spectralCurvatureWindow aPlus) ω) ^ 2) hplus
    have hminusTrans := spectralIntegrable_finsetEq S hPminus
      (fun ω => (sourceFillingCurvaturePairing (spectralCurvatureWindow aMinus) ω) ^ 2) hminus
    have hplusEq : (fun ω : spectralPairPlaquettes x y → ℤ =>
        (sourceFillingCurvaturePairing (spectralCurvatureWindow aPlus)
          ((curvatureAssignmentCastEquiv hPplus).symm ω)) ^ 2) =
        fun ω => (X ω + Y ω) ^ 2 := by
      funext ω
      rw [spectralWindowIndex_pairing]
      have hsupp : aPlus.support = {x, y} := by
        change (spectralPairSumTest x y).support = _
        exact spectralPairSumTest_support hxy
      change (-(∑ z : aPlus.support, aPlus z.1 *
        ((curvatureAssignmentCastEquiv hPplus).symm ω
          (spectralWindowIndex aPlus z) : ℝ))) ^ 2 = _
      rw [spectralSubtypeSum_pair x y hxy aPlus.support hsupp (fun z => aPlus z.1 *
        ((curvatureAssignmentCastEquiv hPplus).symm ω
          (spectralWindowIndex aPlus z) : ℝ))]
      rw [show (curvatureAssignmentCastEquiv hPplus).symm ω
          (spectralWindowIndex aPlus ⟨x, hxPlus⟩) =
            ω (curvatureIndexCastEquiv hPplus (spectralWindowIndex aPlus ⟨x, hxPlus⟩)) by rfl,
        hidxPlusX]
      rw [show (curvatureAssignmentCastEquiv hPplus).symm ω
          (spectralWindowIndex aPlus ⟨y, hyPlus⟩) =
            ω (curvatureIndexCastEquiv hPplus (spectralWindowIndex aPlus ⟨y, hyPlus⟩)) by rfl,
        hidxPlusY]
      have hxVal : aPlus x = 1 := by simp [aPlus, spectralPairSumTest, hxy]
      have hyVal : aPlus y = 1 := by simp [aPlus, spectralPairSumTest, hxy]
      rw [hxVal, hyVal]
      simp [X, Y]
      ring
    have hminusEq : (fun ω : spectralPairPlaquettes x y → ℤ =>
        (sourceFillingCurvaturePairing (spectralCurvatureWindow aMinus)
          ((curvatureAssignmentCastEquiv hPminus).symm ω)) ^ 2) =
        fun ω => (X ω - Y ω) ^ 2 := by
      funext ω
      rw [spectralWindowIndex_pairing]
      have hsupp : aMinus.support = {x, y} := by
        change (spectralPairDifferenceTest x y).support = _
        exact spectralPairDifferenceTest_support hxy
      change (-(∑ z : aMinus.support, aMinus z.1 *
        ((curvatureAssignmentCastEquiv hPminus).symm ω
          (spectralWindowIndex aMinus z) : ℝ))) ^ 2 = _
      rw [spectralSubtypeSum_pair x y hxy aMinus.support hsupp (fun z => aMinus z.1 *
        ((curvatureAssignmentCastEquiv hPminus).symm ω
          (spectralWindowIndex aMinus z) : ℝ))]
      rw [show (curvatureAssignmentCastEquiv hPminus).symm ω
          (spectralWindowIndex aMinus ⟨x, hxMinus⟩) =
            ω (curvatureIndexCastEquiv hPminus (spectralWindowIndex aMinus ⟨x, hxMinus⟩)) by rfl,
        hidxMinusX]
      rw [show (curvatureAssignmentCastEquiv hPminus).symm ω
          (spectralWindowIndex aMinus ⟨y, hyMinus⟩) =
            ω (curvatureIndexCastEquiv hPminus (spectralWindowIndex aMinus ⟨y, hyMinus⟩)) by rfl,
        hidxMinusY]
      have hxVal : aMinus x = 1 := by simp [aMinus, spectralPairDifferenceTest, hxy]
      have hyVal : aMinus y = -1 := by simp [aMinus, spectralPairDifferenceTest, hxy]
      rw [hxVal, hyVal]
      simp [X, Y]
      ring
    have hplus' : Integrable (fun ω => (X ω + Y ω) ^ 2)
        (S.law (spectralPairPlaquettes x y)).toMeasure :=
      hplusTrans.congr (ae_of_all _ fun ω => by rw [hplusEq])
    have hminus' : Integrable (fun ω => (X ω - Y ω) ^ 2)
        (S.law (spectralPairPlaquettes x y)).toMeasure :=
      hminusTrans.congr (ae_of_all _ fun ω => by rw [hminusEq])
    have hdiff := hplus'.sub hminus'
    have hprod : Integrable
        (fun ω => (1 / 4 : ℝ) * ((X ω + Y ω) ^ 2 - (X ω - Y ω) ^ 2))
        (S.law (spectralPairPlaquettes x y)).toMeasure := hdiff.const_mul (1 / 4)
    have heq : (fun ω => (1 / 4 : ℝ) *
        ((X ω + Y ω) ^ 2 - (X ω - Y ω) ^ 2)) = spectralPairProduct x y := by
      funext ω
      dsimp [spectralPairProduct, X, Y]
      ring
    exact hprod.congr (ae_of_all _ fun ω => by rw [heq])

theorem spectralPairProduct_integral_translate
    (S : CurvatureCylinderState)
    (hinv : ∀ a P, translateCylinderLaw S a P = S.law P)
    {a : LatticeShift} {x y : LatticePoint} :
    ∫ ω, spectralPairProduct (x + latticeShiftPoint a) (y + latticeShiftPoint a) ω ∂
        (S.law (spectralPairPlaquettes (x + latticeShiftPoint a)
          (y + latticeShiftPoint a))).toMeasure =
      ∫ ω, spectralPairProduct x y ω ∂(S.law (spectralPairPlaquettes x y)).toMeasure := by
  classical
  let P := spectralPairPlaquettes x y
  let P' := spectralPairPlaquettes (x + latticeShiftPoint a) (y + latticeShiftPoint a)
  let T := translatePlaquettes a P
  let U : (T → ℤ) → (P → ℤ) := untranslateCurvatureAssignment a P
  have hT : T = P' := by
    dsimp [T, P, P']
    exact spectralPairPlaquettes_translate a x y
  let e := curvatureIndexCastEquiv hT
  let J : (T → ℤ) → (P' → ℤ) := curvatureAssignmentCastEquiv hT
  have hmapU : PMF.map U (S.law T) = S.law P := by
    simpa [translateCylinderLaw, P, T, U] using hinv a P
  have hmapJ : PMF.map J (S.law T) = S.law P' := by
    exact curvatureCylinderLaw_map_finsetEq S hT
  have hidxX :
      translatePlaquetteIndex a P (spectralPairIndex x y x (by simp [spectralPairPlaquettes])) =
        e.symm (spectralPairIndex (x + latticeShiftPoint a) (y + latticeShiftPoint a)
          (x + latticeShiftPoint a) (by simp [spectralPairPlaquettes])) := by
    apply e.injective
    simp only [Equiv.apply_symm_apply]
    apply Subtype.ext
    change (curvatureIndexCastEquiv hT
      (translatePlaquetteIndex a P
        (spectralPairIndex x y x (by simp [spectralPairPlaquettes])))).1 = _
    rw [curvatureIndexCastEquiv_val]
    change translatePlaquetteEquiv a (spectralPlaquetteAt x) = _
    exact spectralPlaquetteAt_translate_point a x
  have hidxY :
      translatePlaquetteIndex a P (spectralPairIndex x y y (by simp [spectralPairPlaquettes])) =
        e.symm (spectralPairIndex (x + latticeShiftPoint a) (y + latticeShiftPoint a)
          (y + latticeShiftPoint a) (by simp [spectralPairPlaquettes])) := by
    apply e.injective
    simp only [Equiv.apply_symm_apply]
    apply Subtype.ext
    change (curvatureIndexCastEquiv hT
      (translatePlaquetteIndex a P
        (spectralPairIndex x y y (by simp [spectralPairPlaquettes])))).1 = _
    rw [curvatureIndexCastEquiv_val]
    change translatePlaquetteEquiv a (spectralPlaquetteAt y) = _
    exact spectralPlaquetteAt_translate_point a y
  have hpair (ω : T → ℤ) :
      spectralPairProduct x y (U ω) =
        spectralPairProduct (x + latticeShiftPoint a) (y + latticeShiftPoint a) (J ω) := by
    dsimp [spectralPairProduct, U, untranslateCurvatureAssignment]
    simp_rw [hidxX, hidxY]
    rfl
  have hUmeas : Measurable U := by fun_prop
  have hJmeas : Measurable J := by fun_prop
  have hf : StronglyMeasurable (spectralPairProduct x y) := by fun_prop
  have hf' : StronglyMeasurable
      (spectralPairProduct (x + latticeShiftPoint a) (y + latticeShiftPoint a)) := by
    fun_prop
  calc
    ∫ ω, spectralPairProduct (x + latticeShiftPoint a) (y + latticeShiftPoint a) ω ∂
        (S.law P').toMeasure =
      ∫ ω, spectralPairProduct (x + latticeShiftPoint a) (y + latticeShiftPoint a) (J ω) ∂
        (S.law T).toMeasure := by
          rw [← hmapJ, ← PMF.toMeasure_map J (S.law T) hJmeas]
          exact MeasureTheory.integral_map_of_stronglyMeasurable hJmeas hf'
    _ = ∫ ω, spectralPairProduct x y (U ω) ∂(S.law T).toMeasure := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun ω => (hpair ω).symm
    _ = ∫ ω, spectralPairProduct x y ω ∂(S.law P).toMeasure := by
          rw [← hmapU, ← PMF.toMeasure_map U (S.law T) hUmeas]
          exact (MeasureTheory.integral_map_of_stronglyMeasurable hUmeas hf).symm

theorem latticeShiftPoint_spectralPointShift (x : LatticePoint) :
    latticeShiftPoint (spectralPointShift x) = x := by
  rcases x with ⟨x₀, x₁, x₂, x₃⟩
  rfl

/-- The two point function of the fixed `0,1` plaquette orientation. -/
noncomputable def spectralFieldStrengthCorrelation
    (S : CurvatureCylinderState) (d : LatticePoint) : ℝ :=
  ∫ ω, spectralPairProduct 0 d ω ∂(S.law (spectralPairPlaquettes 0 d)).toMeasure

/-- Translation invariance makes the two point function depend only on the
displacement of the two plaquettes. -/
theorem spectralPairProduct_integral_eq_correlation
    (S : CurvatureCylinderState)
    (hinv : ∀ a P, translateCylinderLaw S a P = S.law P)
    (x y : LatticePoint) :
    ∫ ω, spectralPairProduct x y ω ∂(S.law (spectralPairPlaquettes x y)).toMeasure =
      spectralFieldStrengthCorrelation S (y - x) := by
  let a := spectralPointShift x
  have hpoint : latticeShiftPoint a = x := by
    exact latticeShiftPoint_spectralPointShift x
  have hxy : (y - x) + latticeShiftPoint a = y := by
    rw [hpoint]
    exact sub_add_cancel y x
  have hzero : (0 : LatticePoint) + latticeShiftPoint a = x := by
    simp [hpoint]
  have htrans := spectralPairProduct_integral_translate S hinv
    (a := a) (x := 0) (y := y - x)
  rw [hzero, hxy] at htrans
  simpa [spectralFieldStrengthCorrelation] using htrans

theorem spectralPairProduct_integral_window
    (S : CurvatureCylinderState) (x y : LatticePoint)
    {P : Finset GlobalIntegerPlaquette} (hP : spectralPairPlaquettes x y ⊆ P) :
    ∫ ω, spectralPairProduct x y ω ∂(S.law (spectralPairPlaquettes x y)).toMeasure =
      ∫ ω, spectralPairProduct x y (restrictCurvature hP ω) ∂(S.law P).toMeasure := by
  let U := restrictCurvature hP
  have hmap : PMF.map U (S.law P) = S.law (spectralPairPlaquettes x y) :=
    S.consistent _ _ hP
  have hU : Measurable U := by fun_prop
  have hf : StronglyMeasurable (spectralPairProduct x y) := by fun_prop
  calc
    _ = ∫ ω, spectralPairProduct x y ω ∂(PMF.map U (S.law P)).toMeasure := by
      rw [hmap]
    _ = ∫ ω, spectralPairProduct x y (U ω) ∂(S.law P).toMeasure := by
      rw [← PMF.toMeasure_map U (S.law P) hU]
      exact MeasureTheory.integral_map_of_stronglyMeasurable hU hf

theorem spectralWindowSecondMoment_eq_toeplitz
    {β : ℝ} (hβ : rootBetaThreshold ≤ β)
    (L : CubeCurvatureLimitState β (rootBeta_pos hβ))
    (s : ℕ → ℕ) (S : CurvatureCylinderState)
    (hpoint : ∀ P x, Tendsto
      (fun k => (averagedCylinderLaw (cubeStateToCylinderState L) (s k) P x).toReal)
      atTop (𝓝 ((S.law P x).toReal)))
    (hinv : ∀ a P, translateCylinderLaw S a P = S.law P)
    (a : LatticePoint →₀ ℝ) :
    ∫ ω, (sourceFillingCurvaturePairing (spectralCurvatureWindow a) ω) ^ 2 ∂
        (S.law (fillingCurvatureIndexSet (spectralCurvatureWindow a))).toMeasure =
      ∑ x ∈ a.support.attach, ∑ y ∈ a.support.attach,
        spectralFieldStrengthCorrelation S (y.1 - x.1) * a x.1 * a y.1 := by
  classical
  let σ := spectralCurvatureWindow a
  let P := fillingCurvatureIndexSet σ
  let T := a.support.attach
  let coord (x : {x : LatticePoint // x ∈ a.support}) : P := spectralWindowIndex a x
  let B (ω : P → ℤ) (x : {x : LatticePoint // x ∈ a.support}) : ℝ :=
    a x.1 * (ω (coord x) : ℝ)
  have hpairSupport (x y : {x : LatticePoint // x ∈ a.support}) :
      spectralPairPlaquettes x.1 y.1 ⊆ P := by
    intro p hp
    simp only [spectralPairPlaquettes, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with hp | hp
    · subst p
      exact spectralWindowIndex_mem a x.1 x.2
    · subst p
      exact spectralWindowIndex_mem a y.1 y.2
  have hidxX (x y : {x : LatticePoint // x ∈ a.support}) (ω : P → ℤ) :
      restrictCurvature (hpairSupport x y) ω
          (spectralPairIndex x.1 y.1 x.1 (by simp [spectralPairPlaquettes])) =
        ω (coord x) := by
    apply congrArg (fun q : P => ω q)
    apply Subtype.ext
    rfl
  have hidxY (x y : {x : LatticePoint // x ∈ a.support}) (ω : P → ℤ) :
      restrictCurvature (hpairSupport x y) ω
          (spectralPairIndex x.1 y.1 y.1 (by simp [spectralPairPlaquettes])) =
        ω (coord y) := by
    apply congrArg (fun q : P => ω q)
    apply Subtype.ext
    rfl
  have hprodPoint (x y : {x : LatticePoint // x ∈ a.support}) (ω : P → ℤ) :
      spectralPairProduct x.1 y.1 (restrictCurvature (hpairSupport x y) ω) =
        (ω (coord x) : ℝ) * (ω (coord y) : ℝ) := by
    dsimp [spectralPairProduct]
    rw [hidxX x y ω, hidxY x y ω]
  have hprodIntegrable (x y : {x : LatticePoint // x ∈ a.support}) :
      Integrable (fun ω : P → ℤ => (ω (coord x) : ℝ) * (ω (coord y) : ℝ))
        (S.law P).toMeasure := by
    have hsmall := spectralPairProduct_integrable hβ L s S hpoint x.1 y.1
    have hmap : PMF.map (restrictCurvature (hpairSupport x y)) (S.law P) =
        S.law (spectralPairPlaquettes x.1 y.1) :=
      S.consistent _ _ (hpairSupport x y)
    have hmeas : Measurable (restrictCurvature (hpairSupport x y)) := by fun_prop
    have hsmall' : Integrable (spectralPairProduct x.1 y.1)
        (Measure.map (restrictCurvature (hpairSupport x y)) (S.law P).toMeasure) := by
      rw [PMF.toMeasure_map _ _ hmeas, hmap]
      exact hsmall
    have hcomp := hsmall'.comp_measurable hmeas
    exact hcomp.congr (ae_of_all _ fun ω => (hprodPoint x y ω).symm)
  have hpairIntegral (x y : {x : LatticePoint // x ∈ a.support}) :
      ∫ ω, (ω (coord x) : ℝ) * (ω (coord y) : ℝ) ∂(S.law P).toMeasure =
        spectralFieldStrengthCorrelation S (y.1 - x.1) := by
    have hwindow := spectralPairProduct_integral_window S x.1 y.1 (hpairSupport x y)
    have heq : (fun ω : P → ℤ =>
        spectralPairProduct x.1 y.1 (restrictCurvature (hpairSupport x y) ω)) =
        fun ω => (ω (coord x) : ℝ) * (ω (coord y) : ℝ) := by
      funext ω
      exact hprodPoint x y ω
    rw [← heq]
    rw [← hwindow]
    exact spectralPairProduct_integral_eq_correlation S hinv x.1 y.1
  have hα : Integrable (fun ω : P → ℤ =>
      (sourceFillingCurvaturePairing σ ω) ^ 2) (S.law P).toMeasure :=
    spectralCurvatureWindow_pairing_square_integrable hβ L s S hpoint a
  have hpointwise (ω : P → ℤ) :
      (sourceFillingCurvaturePairing σ ω) ^ 2 =
        ∑ x ∈ T, ∑ y ∈ T, B ω x * B ω y := by
    rw [spectralWindowIndex_pairing]
    change (-∑ x ∈ T, B ω x) ^ 2 = _
    rw [show (-∑ x ∈ T, B ω x) ^ 2 = (∑ x ∈ T, B ω x) ^ 2 by ring]
    rw [← Finset.sum_mul_sum]
    ring
  have htermInt (x y : {x : LatticePoint // x ∈ a.support}) :
      Integrable (fun ω : P → ℤ => B ω x * B ω y)
      (S.law P).toMeasure := by
    have h := hprodIntegrable x y
    have heq : (fun ω : P → ℤ => B ω x * B ω y) =
        fun ω => (a x.1 * a y.1) * ((ω (coord x) : ℝ) * (ω (coord y) : ℝ)) := by
      funext ω
      dsimp [B]
      ring
    rw [heq]
    simpa only [mul_comm] using h.const_mul (a x.1 * a y.1)
  have hsumInt : Integrable (fun ω : P → ℤ =>
      ∑ x ∈ T, ∑ y ∈ T, B ω x * B ω y) (S.law P).toMeasure := by
    apply integrable_finsetSum
    intro x hx
    apply integrable_finsetSum
    intro y hy
    exact htermInt x y
  calc
    _ = ∫ ω, ∑ x ∈ T, ∑ y ∈ T, B ω x * B ω y ∂(S.law P).toMeasure := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hpointwise
    _ = ∑ x ∈ T, ∑ y ∈ T,
        ∫ ω, B ω x * B ω y ∂(S.law P).toMeasure := by
      rw [integral_finsetSum T (fun x hx => by
        exact integrable_finsetSum T (fun y hy => htermInt x y))]
      apply Finset.sum_congr rfl
      intro x hx
      rw [integral_finsetSum T (fun y hy => htermInt x y)]
    _ = ∑ x ∈ T, ∑ y ∈ T,
        spectralFieldStrengthCorrelation S (y.1 - x.1) * a x.1 * a y.1 := by
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro y hy
      rw [show (fun ω : P → ℤ => B ω x * B ω y) =
        fun ω => (a x.1 * a y.1) * ((ω (coord x) : ℝ) * (ω (coord y) : ℝ)) by
          funext ω
          dsimp [B]
          ring]
      rw [integral_const_mul, hpairIntegral x y]
      ring

noncomputable def spectralBump (k : Torus4) (n : ℕ) : C(Torus4, ℝ) :=
  ⟨fun z => max 0 (1 - ((n : ℝ) + 1) * min (dist z k) (dist z (-k))), by
    fun_prop⟩

theorem spectralBump_even (k : Torus4) (n : ℕ) (z : Torus4) : spectralBump k n (-z) = spectralBump k n z := by
  have h1 : dist (-z) k = dist z (-k) := by
    simpa only [neg_neg] using (dist_neg_neg z (-k))
  have h2 : dist (-z) (-k) = dist z k := by
    exact dist_neg_neg z k
  simp [spectralBump, h1, h2, min_comm]

theorem spectralBump_nonneg (k : Torus4) (n : ℕ) (z : Torus4) : 0 ≤ spectralBump k n z := by
  simp [spectralBump]

theorem spectralBump_le_one (k : Torus4) (n : ℕ) (z : Torus4) : spectralBump k n z ≤ 1 := by
  dsimp [spectralBump]
  apply max_le
  · norm_num
  · have hm : 0 ≤ min (dist z k) (dist z (-k)) := le_min (dist_nonneg) (dist_nonneg)
    have hn : 0 ≤ (n : ℝ) + 1 := by positivity
    nlinarith

theorem spectralBump_at_center (k : Torus4) (n : ℕ) : spectralBump k n k = 1 := by
  simp [spectralBump]

private theorem continuous_integrable (f : C(Torus4, ℝ)) : Integrable f torus4Haar := by
  obtain ⟨C, hC⟩ := (isCompact_univ : IsCompact (Set.univ : Set Torus4)).exists_bound_of_continuousOn f.continuous.continuousOn
  exact Integrable.of_bound f.continuous.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun z => hC z (Set.mem_univ z))

noncomputable def spectralBumpMass (k : Torus4) (n : ℕ) : ℝ :=
  ∫ z, spectralBump k n z ^ 2 ∂torus4Haar

theorem spectralBumpMass_pos (k : Torus4) (n : ℕ) : 0 < spectralBumpMass k n := by
  have hc : Continuous (fun z : Torus4 => spectralBump k n z ^ 2) := by fun_prop
  have hi : Integrable (fun z : Torus4 => spectralBump k n z ^ 2) torus4Haar :=
    continuous_integrable ⟨_, hc⟩
  have hn : ∀ z, 0 ≤ spectralBump k n z ^ 2 := fun z => sq_nonneg _
  have hv : spectralBump k n k ^ 2 ≠ 0 := by rw [spectralBump_at_center]; norm_num
  exact MeasureTheory.integral_pos_of_integrable_nonneg_nonzero hc hi hn hv

theorem spectralBumpMass_le_one (k : Torus4) (n : ℕ) : spectralBumpMass k n ≤ 1 := by
  have hc : Integrable (fun _ : Torus4 => (1 : ℝ)) torus4Haar := integrable_const _
  have hb : Integrable (fun z : Torus4 => spectralBump k n z ^ 2) torus4Haar := by
    have hcont : Continuous (fun z : Torus4 => spectralBump k n z ^ 2) := by fun_prop
    exact continuous_integrable ⟨_, hcont⟩
  calc
    spectralBumpMass k n ≤ ∫ _ : Torus4, (1 : ℝ) ∂torus4Haar := by
      apply integral_mono hb hc
      intro z
      have h0 := spectralBump_nonneg k n z
      have h1 := spectralBump_le_one k n z
      nlinarith
    _ = 1 := by simp


noncomputable def spectralBumpComplex (k : Torus4) (n : ℕ) : C(Torus4, ℂ) :=
  ⟨fun z => (spectralBump k n z : ℂ), by fun_prop⟩

theorem spectralBumpComplex_symm (k : Torus4) (n : ℕ) (z : Torus4) :
    spectralBumpComplex k n z = star (spectralBumpComplex k n (-z)) := by
  simp [spectralBumpComplex, spectralBump_even]

theorem spectralFiniteTestWeight_close (k : Torus4) (n : ℕ) (c : FiniteRealTest)
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (happrox : ‖spectralBumpComplex k n - realFourierPoly c‖ < ε) (z : Torus4) :
    |finiteTestFourierWeight c z - spectralBump k n z ^ 2| ≤ 3 * ε := by
  let b := spectralBump k n z
  let p := realFourierPoly c z
  let r := ‖p‖
  have hb0 : 0 ≤ b := spectralBump_nonneg k n z
  have hb1 : b ≤ 1 := spectralBump_le_one k n z
  have hpb : ‖(b : ℂ) - p‖ < ε := by
    have h := (spectralBumpComplex k n - realFourierPoly c).norm_coe_le_norm z
    exact lt_of_le_of_lt (by simpa [spectralBumpComplex, p, b] using h) happrox
  have hrle : r ≤ b + ε := by
    calc
      r = ‖(p - (b : ℂ)) + (b : ℂ)‖ := by
        change ‖p‖ = _
        congr 1
        ring
      _ ≤ ‖p - (b : ℂ)‖ + ‖(b : ℂ)‖ := norm_add_le _ _
      _ = ‖(b : ℂ) - p‖ + b := by
        rw [show p - (b : ℂ) = -((b : ℂ) - p) by ring, norm_neg]
        have hbNorm : ‖(b : ℂ)‖ = b := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hb0]
        rw [hbNorm]
      _ ≤ ε + b := by linarith [hpb]
      _ = b + ε := by ring
  have hrge : b ≤ r + ε := by
    apply le_of_lt
    calc
      b = ‖((b : ℂ) - p) + p‖ := by
        have hbNorm : ‖(b : ℂ)‖ = b := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hb0]
        calc
          b = ‖(b : ℂ)‖ := hbNorm.symm
          _ = ‖((b : ℂ) - p) + p‖ := by congr 1; ring
      _ ≤ ‖(b : ℂ) - p‖ + ‖p‖ := norm_add_le _ _
      _ < ε + r := by
        have h := add_lt_add_right hpb r
        simpa [add_comm] using h
      _ = r + ε := by ring
  have hdiff : |r - b| ≤ ε := abs_le.mpr ⟨by linarith, by linarith⟩
  have hrb : r + b ≤ 3 := by linarith
  have hsq : |r ^ 2 - b ^ 2| = |r - b| * (r + b) := by
    rw [show r ^ 2 - b ^ 2 = (r - b) * (r + b) by ring, abs_mul,
      abs_of_nonneg (by positivity : 0 ≤ r + b)]
  have hweight : finiteTestFourierWeight c z = r ^ 2 := by
    dsimp [finiteTestFourierWeight, p, r]
    rw [Complex.normSq_eq_norm_sq]
  rw [hweight]
  calc
    |r ^ 2 - b ^ 2| = |r - b| * (r + b) := hsq
    _ ≤ ε * (r + b) := mul_le_mul_of_nonneg_right hdiff (by positivity)
    _ ≤ ε * 3 := mul_le_mul_of_nonneg_left hrb hε0
    _ = 3 * ε := by ring

noncomputable def spectralBumpApproxError (k : Torus4) (n : ℕ) : ℝ :=
  spectralBumpMass k n / (6 * ((n : ℝ) + 1))

theorem spectralBumpApproxError_pos (k : Torus4) (n : ℕ) : 0 < spectralBumpApproxError k n := by
  dsimp [spectralBumpApproxError]
  apply div_pos (spectralBumpMass_pos k n)
  positivity

theorem spectralBumpApproxError_le_one (k : Torus4) (n : ℕ) : spectralBumpApproxError k n ≤ 1 := by
  dsimp [spectralBumpApproxError]
  have hm := spectralBumpMass_le_one k n
  have hn : 1 ≤ (n : ℝ) + 1 := by norm_cast; omega
  apply (div_le_iff₀ (by positivity : 0 < 6 * ((n : ℝ) + 1))).2
  nlinarith

noncomputable def spectralPolynomialLocalizerTest (k : Torus4) (n : ℕ) : FiniteRealTest :=
  Classical.choose (exists_realFourierPoly_approx (spectralBumpComplex k n)
    (spectralBumpComplex_symm k n) (spectralBumpApproxError k n) (spectralBumpApproxError_pos k n))

theorem spectralPolynomialLocalizerTest_approx (k : Torus4) (n : ℕ) :
    ‖spectralBumpComplex k n - realFourierPoly (spectralPolynomialLocalizerTest k n)‖ <
      spectralBumpApproxError k n :=
  Classical.choose_spec (exists_realFourierPoly_approx (spectralBumpComplex k n)
    (spectralBumpComplex_symm k n) (spectralBumpApproxError k n) (spectralBumpApproxError_pos k n))

theorem spectralPolynomialLocalizer_mass_lower (k : Torus4) (n : ℕ) :
    spectralBumpMass k n / 2 ≤ finiteTestMass (spectralPolynomialLocalizerTest k n) := by
  let e := spectralBumpApproxError k n
  let f := spectralPolynomialLocalizerTest k n
  have he0 : 0 ≤ e := (spectralBumpApproxError_pos k n).le
  have he1 : e ≤ 1 := spectralBumpApproxError_le_one k n
  have hclose (z : Torus4) :
      |finiteTestFourierWeight f z - spectralBump k n z ^ 2| ≤ 3 * e := by
    exact spectralFiniteTestWeight_close k n f e he0 he1 (spectralPolynomialLocalizerTest_approx k n) z
  have hpoint (z : Torus4) : spectralBump k n z ^ 2 - 3 * e ≤ finiteTestFourierWeight f z := by
    have h := (abs_le.mp (hclose z)).1
    dsimp [f, e] at *
    linarith
  have hφc : Continuous (fun z : Torus4 => spectralBump k n z ^ 2 - 3 * e) := by fun_prop
  have hφi : Integrable (fun z : Torus4 => spectralBump k n z ^ 2 - 3 * e) torus4Haar :=
    continuous_integrable ⟨_, hφc⟩
  have hwc : Continuous (fun z : Torus4 => finiteTestFourierWeight f z) := by
    dsimp [finiteTestFourierWeight]
    fun_prop
  have hwi : Integrable (fun z : Torus4 => finiteTestFourierWeight f z) torus4Haar :=
    continuous_integrable ⟨_, hwc⟩
  have hint := integral_mono hφi hwi hpoint
  have hconst : ∫ _ : Torus4, (3 * e : ℝ) ∂torus4Haar = 3 * e := by simp
  have hmass : spectralBumpMass k n - 3 * e ≤ finiteTestMass f := by
    rw [finiteTestMass]
    rw [integral_sub (by
      have hcont : Continuous (fun z : Torus4 => spectralBump k n z ^ 2) := by fun_prop
      exact continuous_integrable ⟨_, hcont⟩) (integrable_const (3 * e)), hconst] at hint
    simpa [spectralBumpMass] using hint
  have hn : 1 ≤ (n : ℝ) + 1 := by norm_cast; omega
  have hebound : 3 * e ≤ spectralBumpMass k n / 2 := by
    dsimp [e, spectralBumpApproxError]
    have hm := spectralBumpMass_le_one k n
    have hm0 := spectralBumpMass_pos k n
    have hd : 0 < 6 * ((n : ℝ) + 1) := by positivity
    rw [show 3 * (spectralBumpMass k n / (6 * ((n : ℝ) + 1))) =
      (3 * spectralBumpMass k n) / (6 * ((n : ℝ) + 1)) by ring]
    apply (div_le_iff₀ hd).2
    nlinarith [hm0.le, hn]
  simpa [f] using (le_trans (by linarith : spectralBumpMass k n / 2 ≤ spectralBumpMass k n - 3 * e) hmass)

theorem spectralBump_eq_zero_of_far (k z : Torus4) (n : ℕ) (r : ℝ)
    (hr : 1 ≤ ((n : ℝ) + 1) * r)
    (h₁ : r ≤ dist z k) (h₂ : r ≤ dist z (-k)) :
    spectralBump k n z = 0 := by
  have hm : r ≤ min (dist z k) (dist z (-k)) := le_min h₁ h₂
  have harg : 1 - ((n : ℝ) + 1) * min (dist z k) (dist z (-k)) ≤ 0 := by
    have hn : 0 ≤ (n : ℝ) + 1 := by positivity
    nlinarith
  dsimp [spectralBump]
  exact max_eq_left harg

theorem spectralPolynomialLocalizer_weight_tail (k z : Torus4) (n : ℕ) (r : ℝ)
    (hr : 1 ≤ ((n : ℝ) + 1) * r)
    (h₁ : r ≤ dist z k) (h₂ : r ≤ dist z (-k)) :
    finiteTestFourierWeight (spectralPolynomialLocalizerTest k n) z ≤
      spectralBumpApproxError k n ^ 2 := by
  have hzero := spectralBump_eq_zero_of_far k z n r hr h₁ h₂
  have hp : ‖realFourierPoly (spectralPolynomialLocalizerTest k n) z‖ <
      spectralBumpApproxError k n := by
    have h := (spectralBumpComplex k n -
      realFourierPoly (spectralPolynomialLocalizerTest k n)).norm_coe_le_norm z
    have h' := lt_of_le_of_lt h (spectralPolynomialLocalizerTest_approx k n)
    simpa [spectralBumpComplex, hzero] using h'
  rw [finiteTestFourierWeight, Complex.normSq_eq_norm_sq]
  exact le_of_lt (by nlinarith [norm_nonneg (realFourierPoly (spectralPolynomialLocalizerTest k n) z)])

theorem spectralPolynomialLocalizer_average_error_bound
    (k : Torus4) (g : Torus4 → ℝ) (hg : Integrable g torus4Haar)
    (heven : ∀ z, g (-z) = g z)
    {δ r : ℝ} (hδ : 0 < δ)
    (hnear : ∀ z, dist z k < r → |g z - g k| ≤ δ)
    (n : ℕ) (hn : 1 ≤ ((n : ℝ) + 1) * r) :
    |finiteTestAverage g (spectralPolynomialLocalizerTest k n) - g k| ≤
      δ + spectralBumpApproxError k n ^ 2 *
        (∫ z, |g z - g k| ∂torus4Haar) /
          finiteTestMass (spectralPolynomialLocalizerTest k n) := by
  let f := spectralPolynomialLocalizerTest k n
  let w : Torus4 → ℝ := fun z => finiteTestFourierWeight f z
  let e := spectralBumpApproxError k n
  let d : Torus4 → ℝ := fun z => |g z - g k|
  have hwc : Continuous w := by
    dsimp [w, finiteTestFourierWeight]
    fun_prop
  have hwi : Integrable w torus4Haar := continuous_integrable ⟨w, hwc⟩
  have hw0 (z : Torus4) : 0 ≤ w z := Complex.normSq_nonneg _
  obtain ⟨C, hC⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set Torus4)).exists_bound_of_continuousOn
      hwc.continuousOn
  have hwb : ∀ᵐ z ∂torus4Haar, ‖w z‖ ≤ C :=
    Filter.Eventually.of_forall fun z => hC z (Set.mem_univ z)
  have hgw : Integrable (fun z => g z * w z) torus4Haar :=
    hg.mul_bdd hwc.aestronglyMeasurable hwb
  have hgdiff : Integrable (fun z => g z - g k) torus4Haar :=
    hg.sub (integrable_const (g k))
  have hd : Integrable d torus4Haar := by
    exact hgdiff.norm.congr (ae_of_all _ fun z => rfl)
  have hde : Integrable (fun z => d z * e ^ 2) torus4Haar := by
    exact (hd.const_mul (e ^ 2)).congr (ae_of_all _ fun z => by ring)
  have hdiff : Integrable (fun z => (g z - g k) * w z) torus4Haar :=
    hgdiff.mul_bdd hwc.aestronglyMeasurable hwb
  have hdiffnorm : Integrable (fun z => |(g z - g k) * w z|) torus4Haar :=
    hdiff.norm
  have hRHS : Integrable (fun z => δ * w z + d z * e ^ 2) torus4Haar :=
    (hwi.const_mul δ).add hde
  have hpoint (z : Torus4) :
      |(g z - g k) * w z| ≤ δ * w z + d z * e ^ 2 := by
    by_cases hz : dist z k < r
    · have hgz := hnear z hz
      rw [abs_mul, abs_of_nonneg (hw0 z)]
      calc
        |g z - g k| * w z ≤ δ * w z :=
          mul_le_mul_of_nonneg_right hgz (hw0 z)
        _ ≤ δ * w z + |g z - g k| * e ^ 2 :=
          le_add_of_nonneg_right (mul_nonneg (abs_nonneg _) (sq_nonneg _))
    · by_cases hzm : dist z (-k) < r
      · have hdist : dist (-z) k < r := by
          have heq : dist (-z) k = dist z (-k) := by
            simpa only [neg_neg] using (dist_neg_neg z (-k))
          rw [heq]
          exact hzm
        have hgz := hnear (-z) hdist
        have heq : g z = g (-z) := (heven z).symm
        have hgeq : |g z - g k| = |g (-z) - g k| := by rw [heq]
        dsimp [d]
        rw [abs_mul, abs_of_nonneg (hw0 z)]
        rw [hgeq]
        calc
          |g (-z) - g k| * w z ≤ δ * w z :=
            mul_le_mul_of_nonneg_right hgz (hw0 z)
          _ ≤ δ * w z + |g (-z) - g k| * e ^ 2 :=
            le_add_of_nonneg_right (mul_nonneg (abs_nonneg _) (sq_nonneg _))
      · have htail := spectralPolynomialLocalizer_weight_tail k z n r hn
          (le_of_not_gt hz) (le_of_not_gt hzm)
        rw [abs_mul, abs_of_nonneg (hw0 z)]
        calc
          |g z - g k| * w z ≤ |g z - g k| * e ^ 2 :=
            mul_le_mul_of_nonneg_left htail (abs_nonneg _)
          _ ≤ δ * w z + |g z - g k| * e ^ 2 :=
            le_add_of_nonneg_left (mul_nonneg (le_of_lt hδ) (hw0 z))
  have hintPoint := integral_mono hdiffnorm hRHS hpoint
  have hsumInt :
      ∫ z, δ * w z + d z * e ^ 2 ∂torus4Haar =
        δ * finiteTestMass f + e ^ 2 * (∫ z, d z ∂torus4Haar) := by
    calc
      _ = (∫ z, δ * w z ∂torus4Haar) + (∫ z, d z * e ^ 2 ∂torus4Haar) :=
        integral_add (hwi.const_mul δ) hde
      _ = δ * finiteTestMass f + e ^ 2 * (∫ z, d z ∂torus4Haar) := by
        rw [integral_const_mul, integral_mul_const]
        simp [finiteTestMass, w]
        ring
  have hIntEq :
      ∫ z, (g z - g k) * w z ∂torus4Haar =
        (∫ z, g z * w z ∂torus4Haar) - g k * finiteTestMass f := by
    calc
      _ = ∫ z, (g z * w z - g k * w z) ∂torus4Haar := by
        congr 1
        funext z
        ring
      _ = _ := by
        rw [integral_sub hgw (hwi.const_mul (g k))]
        simp [finiteTestMass, w, integral_const_mul]
  have habs : |∫ z, (g z - g k) * w z ∂torus4Haar| ≤
      δ * finiteTestMass f + e ^ 2 * (∫ z, d z ∂torus4Haar) :=
    (abs_integral_le_integral_abs).trans (by simpa [hsumInt] using hintPoint)
  have hmasspos : 0 < finiteTestMass f := by
    exact lt_of_lt_of_le (div_pos (spectralBumpMass_pos k n) (by norm_num))
      (spectralPolynomialLocalizer_mass_lower k n)
  have havg :
      finiteTestAverage g f - g k =
        ((∫ z, g z * w z ∂torus4Haar) - g k * finiteTestMass f) /
          finiteTestMass f := by
    dsimp [finiteTestAverage, w]
    field_simp [ne_of_gt hmasspos]
  rw [havg, ← hIntEq, abs_div, abs_of_pos hmasspos]
  apply (div_le_iff₀ hmasspos).2
  calc
    |∫ z, (g z - g k) * w z ∂torus4Haar| ≤
        δ * finiteTestMass f + e ^ 2 * (∫ z, d z ∂torus4Haar) := habs
    _ = (δ + e ^ 2 * (∫ z, d z ∂torus4Haar) / finiteTestMass f) *
        finiteTestMass f := by
      rw [add_mul, div_mul_cancel₀ _ hmasspos.ne']

theorem spectralPolynomialLocalizer_average_tendsto
    (k : Torus4) (g : Torus4 → ℝ) (hg : Integrable g torus4Haar)
    (heven : ∀ z, g (-z) = g z) (hgk : ContinuousAt g k) :
    Tendsto (fun n => finiteTestAverage g (spectralPolynomialLocalizerTest k n))
      atTop (𝓝 (g k)) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let δ := ε / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  obtain ⟨r, hr, hclose⟩ := Metric.continuousAt_iff.mp hgk δ hδ
  have hnear (z : Torus4) (hz : dist z k < r) :
      |g z - g k| ≤ δ := by
    have h := hclose hz
    rw [Real.dist_eq] at h
    exact h.le
  have hdiff : Integrable (fun z => |g z - g k|) torus4Haar :=
    (hg.sub (integrable_const (g k))).norm
  let A : ℝ := ∫ z, |g z - g k| ∂torus4Haar
  have hA0 : 0 ≤ A := by
    dsimp [A]
    exact integral_nonneg_of_ae (Filter.Eventually.of_forall fun z => abs_nonneg _)
  let d : ℕ → ℝ := fun n => (n : ℝ) + 1
  have hd : Tendsto d atTop atTop := by
    dsimp [d]
    exact tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have hinv : Tendsto (fun n => (d n)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hd
  have hinvSq : Tendsto (fun n => (d n)⁻¹ * (d n)⁻¹) atTop (𝓝 0) := by
    simpa using hinv.mul hinv
  have htail : Tendsto (fun n => (A / 18) *
      ((d n)⁻¹ * (d n)⁻¹)) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hinvSq)
  have htailEvent := htail.eventually (Iio_mem_nhds (by positivity : 0 < ε / 2))
  have hlarge : ∀ᶠ n : ℕ in atTop, (1 / r) ≤ d n :=
    (Filter.tendsto_atTop.1 hd) (1 / r)
  have hprod : ∀ᶠ n : ℕ in atTop, 1 ≤ d n * r := by
    filter_upwards [hlarge] with n hn
    exact (div_le_iff₀ hr).mp hn
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.1 htailEvent
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.1 hprod
  refine ⟨max N₁ N₂, ?_⟩
  intro n hn
  have hn1 : N₁ ≤ n := le_trans (Nat.le_max_left _ _) hn
  have hn2 : N₂ ≤ n := le_trans (Nat.le_max_right _ _) hn
  have htailn := hN₁ n hn1
  have hnprod := hN₂ n hn2
  have herror := spectralPolynomialLocalizer_average_error_bound k g hg heven
    hδ hnear n hnprod
  have hmass := spectralPolynomialLocalizer_mass_lower k n
  have hm : 0 < spectralBumpMass k n := spectralBumpMass_pos k n
  have hratio :
      spectralBumpApproxError k n ^ 2 * A /
          finiteTestMass (spectralPolynomialLocalizerTest k n) ≤
        (A / 18) * ((d n)⁻¹ * (d n)⁻¹) := by
    have hmasspos : 0 < finiteTestMass (spectralPolynomialLocalizerTest k n) :=
      lt_of_lt_of_le (div_pos hm (by norm_num)) hmass
    have hdpos : 0 < d n := by dsimp [d]; positivity
    have hMpos : 0 < spectralBumpMass k n := spectralBumpMass_pos k n
    have hMle : spectralBumpMass k n ≤ 1 := spectralBumpMass_le_one k n
    have hlower := spectralPolynomialLocalizer_mass_lower k n
    have hratio' : spectralBumpApproxError k n ^ 2 /
        finiteTestMass (spectralPolynomialLocalizerTest k n) ≤
          (1 / 18) * ((d n)⁻¹ * (d n)⁻¹) := by
      rw [show spectralBumpApproxError k n = spectralBumpMass k n / (6 * d n) by rfl]
      have hden : 0 < spectralBumpMass k n / 2 := by positivity
      have hdiv := div_le_div_of_nonneg_left (sq_nonneg (spectralBumpApproxError k n))
        hden hlower
      have heq : spectralBumpApproxError k n ^ 2 / (spectralBumpMass k n / 2) =
          spectralBumpMass k n / (18 * (d n) ^ 2) := by
        rw [show spectralBumpApproxError k n = spectralBumpMass k n / (6 * d n) by rfl]
        field_simp [ne_of_gt hMpos, ne_of_gt hdpos]
        ring
      rw [heq] at hdiv
      have hMbound := div_le_div_of_nonneg_right hMle
        (by positivity : 0 ≤ 18 * (d n) ^ 2)
      have hcombined := hdiv.trans hMbound
      calc
        spectralBumpApproxError k n ^ 2 /
            finiteTestMass (spectralPolynomialLocalizerTest k n) ≤
          1 / (18 * (d n) ^ 2) := hcombined
        _ = (1 / 18) * ((d n)⁻¹ * (d n)⁻¹) := by
          field_simp [ne_of_gt hdpos]
    calc
      _ = A * (spectralBumpApproxError k n ^ 2 /
          finiteTestMass (spectralPolynomialLocalizerTest k n)) := by ring
      _ ≤ A * ((1 / 18) * ((d n)⁻¹ * (d n)⁻¹)) :=
        mul_le_mul_of_nonneg_left hratio' hA0
      _ = _ := by ring
  have hsum : δ + (A / 18) * ((d n)⁻¹ * (d n)⁻¹) < ε := by
    have heq : (A / 18) * ((d n)⁻¹ * (d n)⁻¹) < ε / 2 := htailn
    dsimp [δ]
    linarith
  have herror
      : |finiteTestAverage g (spectralPolynomialLocalizerTest k n) - g k| ≤
          δ + spectralBumpApproxError k n ^ 2 * A /
            finiteTestMass (spectralPolynomialLocalizerTest k n) := by
    simpa [A] using spectralPolynomialLocalizer_average_error_bound k g hg heven
      hδ hnear n hnprod
  have hratio'' : δ + spectralBumpApproxError k n ^ 2 * A /
      finiteTestMass (spectralPolynomialLocalizerTest k n) ≤
        δ + (A / 18) * ((d n)⁻¹ * (d n)⁻¹) :=
    by simpa [add_comm] using add_le_add_left hratio δ
  have habs := le_trans herror hratio''
  rw [Real.dist_eq]
  exact lt_of_le_of_lt habs hsum


/-- Finite tests localize against even integrable functions continuous at the
frequency. The integrability condition is required because Bochner integrals
are totalized on nonintegrable functions. -/
def HasIntegrableFiniteTestLocalizers
    (tests : Torus4 → ℕ → FiniteRealTest) : Prop :=
  ∀ k : Torus4, k ≠ 0 →
    (∀ n, 0 < finiteTestMass (tests k n)) ∧
    ∀ g : Torus4 → ℝ, MeasureTheory.Integrable g torus4Haar →
      (∀ z, g (-z) = g z) → ContinuousAt g k →
      Tendsto (fun n => finiteTestAverage g (tests k n)) atTop (𝓝 (g k))


/-- Uniform polynomial approximation of symmetric shrinking bumps gives an
explicit finite-test localizer family for every integrable even observable
continuous at the selected frequency. -/
theorem spectralPolynomialLocalizerTests_localizers :
    HasIntegrableFiniteTestLocalizers spectralPolynomialLocalizerTest := by
  intro k hk
  constructor
  · intro n
    exact lt_of_lt_of_le
      (div_pos (spectralBumpMass_pos k n) (by norm_num))
      (spectralPolynomialLocalizer_mass_lower k n)
  · intro g hg heven hgk
    exact spectralPolynomialLocalizer_average_tendsto k g hg heven hgk

theorem finiteTest_sandwich_to_pointwise_of_integrable_localizers
    (βlo βhi : ℝ) (q s : Torus4 → ℝ)
    (tests : Torus4 → ℕ → FiniteRealTest)
    (hlocal : HasIntegrableFiniteTestLocalizers tests)
    (hqEven : ∀ k, q (-k) = q k)
    (hsEven : ∀ k, s (-k) = s k)
    (hqInt : MeasureTheory.Integrable q torus4Haar)
    (hsInt : MeasureTheory.Integrable s torus4Haar)
    (hq : ∀ k, k ≠ 0 → ContinuousAt q k)
    (hs : ∀ k, ContinuousAt s k)
    (hform : ∀ f : FiniteRealTest,
      βlo * (∫ k : Torus4, q k * finiteTestFourierWeight f k ∂torus4Haar) ≤
          ∫ k : Torus4, s k * finiteTestFourierWeight f k ∂torus4Haar ∧
        (∫ k : Torus4, s k * finiteTestFourierWeight f k ∂torus4Haar) ≤
          βhi * (∫ k : Torus4, q k * finiteTestFourierWeight f k ∂torus4Haar)) :
    ∀ k, k ≠ 0 → βlo * q k ≤ s k ∧ s k ≤ βhi * q k := by
  intro k hk
  obtain ⟨hmass, hloc⟩ := hlocal k hk
  have hqLim := hloc q hqInt hqEven (hq k hk)
  have hsLim := hloc s hsInt hsEven (hs k)
  have hlow : ∀ᶠ n : ℕ in atTop,
      βlo * finiteTestAverage q (tests k n) ≤
        finiteTestAverage s (tests k n) := by
    filter_upwards [Filter.Eventually.of_forall hmass] with n hn
    have h := (hform (tests k n)).1
    dsimp [finiteTestAverage]
    calc
      βlo * (_ / finiteTestMass (tests k n)) =
          (βlo * _) / finiteTestMass (tests k n) := by ring
      _ ≤ _ / finiteTestMass (tests k n) := div_le_div_of_nonneg_right h hn.le
      _ = _ := rfl
  have hupp : ∀ᶠ n : ℕ in atTop,
      finiteTestAverage s (tests k n) ≤
        βhi * finiteTestAverage q (tests k n) := by
    filter_upwards [Filter.Eventually.of_forall hmass] with n hn
    have h := (hform (tests k n)).2
    dsimp [finiteTestAverage]
    calc
      _ / finiteTestMass (tests k n) ≤
          (βhi * _) / finiteTestMass (tests k n) := div_le_div_of_nonneg_right h hn.le
      _ = βhi * (_ / finiteTestMass (tests k n)) := by ring
  constructor
  · exact le_of_tendsto_of_tendsto (tendsto_const_nhds.mul hqLim) hsLim hlow
  · exact le_of_tendsto_of_tendsto hsLim (tendsto_const_nhds.mul hqLim) hupp

theorem no_summable_spectral_density_of_integrable_finite_test_sandwich
    (G : LatticePoint → ℝ) (hG : Summable (fun x => |G x|))
    (βlo βhi : ℝ) (hβlo : 0 < βlo) (q : Torus4 → ℝ)
    (tests : Torus4 → ℕ → FiniteRealTest)
    (hlocal : HasIntegrableFiniteTestLocalizers tests)
    (hqEven : ∀ k, q (-k) = q k)
    (hqInt : MeasureTheory.Integrable q torus4Haar)
    (hq : ∀ k, k ≠ 0 → ContinuousAt q k)
    (hform : ∀ f : FiniteRealTest,
      βlo * (∫ k : Torus4, q k * finiteTestFourierWeight f k ∂torus4Haar) ≤
          ∫ k : Torus4, latticeFourierSeriesReal G k *
            finiteTestFourierWeight f k ∂torus4Haar ∧
        (∫ k : Torus4, latticeFourierSeriesReal G k *
            finiteTestFourierWeight f k ∂torus4Haar) ≤
          βhi * (∫ k : Torus4, q k * finiteTestFourierWeight f k ∂torus4Haar))
    (kin kout : ℕ → Torus4)
    (hkin : Tendsto kin atTop (𝓝 0)) (hkout : Tendsto kout atTop (𝓝 0))
    (hkinNe : ∀ n, kin n ≠ 0) (hkoutNe : ∀ n, kout n ≠ 0)
    (hqin : ∀ n, q (kin n) = 1) (hqout : ∀ n, q (kout n) = 0) :
    False := by
  have hsEven : ∀ k, latticeFourierSeriesReal G (-k) = latticeFourierSeriesReal G k := by
    intro k
    have hcomplex : latticeFourierSeries G (-k) =
        conj (latticeFourierSeries G k) := by
      change (∑' x : LatticePoint, (G x : ℂ) * latticeCharacter x (-k)) =
        conj (∑' x : LatticePoint, (G x : ℂ) * latticeCharacter x k)
      rw [Complex.conj_tsum]
      apply tsum_congr
      intro x
      rw [latticeCharacter_torusNeg]
      simp
    simp [latticeFourierSeriesReal, hcomplex]
  have hs := continuous_latticeFourierSeriesReal G hG
  have hsInt : MeasureTheory.Integrable (latticeFourierSeriesReal G) torus4Haar := by
    obtain ⟨C, hC⟩ :=
      (isCompact_univ : IsCompact (Set.univ : Set Torus4)).exists_bound_of_continuousOn
        hs.continuousOn
    exact MeasureTheory.Integrable.of_bound hs.aestronglyMeasurable C
      (Filter.Eventually.of_forall fun k => hC k (Set.mem_univ k))
  have hpoint := finiteTest_sandwich_to_pointwise_of_integrable_localizers
    βlo βhi q (latticeFourierSeriesReal G) tests hlocal hqEven hsEven
    hqInt hsInt hq (fun k => hs.continuousAt) hform
  have hsin : Tendsto (fun n => latticeFourierSeriesReal G (kin n))
      atTop (𝓝 (latticeFourierSeriesReal G 0)) := hs.continuousAt.tendsto.comp hkin
  have hsout : Tendsto (fun n => latticeFourierSeriesReal G (kout n))
      atTop (𝓝 (latticeFourierSeriesReal G 0)) := hs.continuousAt.tendsto.comp hkout
  have hin : ∀ n, βlo ≤ latticeFourierSeriesReal G (kin n) := by
    intro n
    have h := (hpoint (kin n) (hkinNe n)).1
    rw [hqin n] at h
    simpa using h
  have hout : ∀ n, latticeFourierSeriesReal G (kout n) ≤ 0 := by
    intro n
    have h := (hpoint (kout n) (hkoutNe n)).2
    rw [hqout n] at h
    simpa using h
  have hlo : βlo ≤ latticeFourierSeriesReal G 0 :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hsin
      (Filter.Eventually.of_forall hin)
  have hupp : latticeFourierSeriesReal G 0 ≤ 0 :=
    le_of_tendsto_of_tendsto hsout tendsto_const_nhds
      (Filter.Eventually.of_forall hout)
  linarith

private theorem spectralContinuousComplex_integrable (f : C(Torus4, ℂ)) :
    Integrable f torus4Haar := by
  obtain ⟨C, hC⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set Torus4)).exists_bound_of_continuousOn
      f.continuous.continuousOn
  exact Integrable.of_bound f.continuous.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun z => hC z (Set.mem_univ z))

/-- Fourier coefficient extraction for the absolutely convergent correlation
series. -/
theorem spectralIntegral_latticeFourierSeries_character
    (G : LatticePoint → ℝ) (hG : Summable (fun x => |G x|))
    (m : LatticePoint) :
    ∫ k : Torus4, latticeFourierSeries G k * latticeCharacter m k ∂torus4Haar =
      (G (-m) : ℂ) := by
  let F : LatticePoint → C(Torus4, ℂ) := fun x =>
    ⟨fun k => (G x : ℂ) * latticeCharacter (x + m) k,
      (continuous_latticeCharacter (x + m)).const_mul (G x : ℂ)⟩
  have hFint (x : LatticePoint) : Integrable (F x) torus4Haar :=
    spectralContinuousComplex_integrable (F x)
  have hFnorm (x : LatticePoint) :
      ∫ k : Torus4, ‖F x k‖ ∂torus4Haar = |G x| := by
    simp [F, latticeCharacter, torus4Haar]
  have hFsum : Summable (fun x : LatticePoint =>
      ∫ k : Torus4, ‖F x k‖ ∂torus4Haar) := hG.congr fun x => (hFnorm x).symm
  have hseries (k : Torus4) :
      latticeFourierSeries G k * latticeCharacter m k = ∑' x, F x k := by
    unfold latticeFourierSeries
    calc
      (∑' x : LatticePoint, (G x : ℂ) * latticeCharacter x k) *
          latticeCharacter m k =
        ∑' x : LatticePoint,
          ((G x : ℂ) * latticeCharacter x k) * latticeCharacter m k := by
            rw [tsum_mul_right]
      _ = ∑' x : LatticePoint, F x k := by
        apply tsum_congr
        intro x
        change ((G x : ℂ) * latticeCharacter x k) * latticeCharacter m k =
          (G x : ℂ) * latticeCharacter (x + m) k
        rw [mul_assoc, latticeCharacter_mul]
  have hswap := MeasureTheory.integral_tsum_of_summable_integral_norm
    hFint hFsum
  calc
    ∫ k : Torus4, latticeFourierSeries G k * latticeCharacter m k ∂torus4Haar =
        ∫ k : Torus4, ∑' x, F x k ∂torus4Haar := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall hseries
    _ = ∑' x, ∫ k : Torus4, F x k ∂torus4Haar := hswap.symm
    _ = ∑' x : LatticePoint,
          (G x : ℂ) * (if x + m = 0 then 1 else 0) := by
        apply tsum_congr
        intro x
        rw [show F x = fun k => (G x : ℂ) * latticeCharacter (x + m) k by rfl,
          integral_const_mul, integral_latticeCharacter]
    _ = (G (-m) : ℂ) := by
      rw [tsum_eq_single (-m)]
      · simp
      · intro x hne
        have hnot : x + m ≠ 0 := by
          intro hz
          apply hne
          exact eq_neg_of_add_eq_zero_left hz
        simp [hnot]

/-- The integral of a summable correlation spectrum against one finite test
weight is its finite Toeplitz quadratic form. -/
theorem spectralFourierSeries_finiteTest_integral
    (G : LatticePoint → ℝ) (hG : Summable (fun x => |G x|))
    (f : FiniteRealTest) :
    ∫ k : Torus4, latticeFourierSeriesReal G k * finiteTestFourierWeight f k
        ∂torus4Haar =
      ∑ x ∈ (realPartCoefficients f).support,
        ∑ y ∈ (realPartCoefficients f).support,
          G (y - x) * realPartCoefficients f x * realPartCoefficients f y := by
  classical
  let a := realPartCoefficients f
  let p : Torus4 → ℂ := fun k => realFourierPoly f k
  have hp (k : Torus4) : p k =
      ∑ x ∈ a.support, (a x : ℂ) * latticeCharacter x k := by
    dsimp [p, a, realFourierPoly]
    calc
      (∑ x ∈ f.support, (f x).re • charMap x) k =
          ∑ x ∈ f.support, ((f x).re : ℂ) * latticeCharacter x k := by
        simp only [ContinuousMap.sum_apply, ContinuousMap.smul_apply]
        simp only [Complex.real_smul, charMap]
        rfl
      _ = ∑ x ∈ a.support, (a x : ℂ) * latticeCharacter x k := by
        calc
          _ = ∑ x ∈ f.support, (a x : ℂ) * latticeCharacter x k := by
            apply Finset.sum_congr rfl
            intro x hx
            simp [a, realPartCoefficients_apply]
          _ = ∑ x ∈ a.support, (a x : ℂ) * latticeCharacter x k := by
            symm
            apply Finset.sum_subset (realPartCoefficients_support_subset f)
            intro x hx hnot
            have hzero : a x = 0 := Finsupp.notMem_support_iff.mp hnot
            simp [hzero]
  have hweight (k : Torus4) : finiteTestFourierWeight f k =
      (p k * conj (p k)).re := by
    simp [finiteTestFourierWeight, p, Complex.normSq_apply,
      Complex.mul_re, Complex.conj_re, Complex.conj_im]
  have hpoint (k : Torus4) :
      latticeFourierSeriesReal G k * finiteTestFourierWeight f k =
        (latticeFourierSeries G k * (p k * conj (p k))).re := by
    rw [hweight]
    simp [latticeFourierSeriesReal, Complex.mul_re, Complex.mul_im,
      Complex.conj_re, Complex.conj_im]
    ring
  have hpoly (k : Torus4) :
      p k * conj (p k) =
        ∑ x ∈ a.support, ∑ y ∈ a.support,
          ((a x * a y : ℝ) : ℂ) * latticeCharacter (x - y) k := by
    have hconj : conj (p k) =
        ∑ y ∈ a.support, (a y : ℂ) * conj (latticeCharacter y k) := by
      rw [hp k]
      simp only [map_sum, map_mul, Complex.conj_ofReal]
    calc
      p k * conj (p k) =
          (∑ x ∈ a.support, (a x : ℂ) * latticeCharacter x k) *
            (∑ y ∈ a.support, (a y : ℂ) * conj (latticeCharacter y k)) := by
              rw [hconj, hp k]
      _ = ∑ x ∈ a.support, ∑ y ∈ a.support,
          ((a x * a y : ℝ) : ℂ) * latticeCharacter (x - y) k := by
            rw [Finset.sum_mul_sum]
            apply Finset.sum_congr rfl
            intro x hx
            apply Finset.sum_congr rfl
            intro y hy
            calc
              ((a x : ℂ) * latticeCharacter x k) *
                  ((a y : ℂ) * conj (latticeCharacter y k)) =
                  ((a x : ℂ) * (a y : ℂ)) *
                    (latticeCharacter x k * conj (latticeCharacter y k)) := by ring
              _ = ((a x * a y : ℝ) : ℂ) * latticeCharacter (x - y) k := by
                rw [latticeCharacter_mul_conj]
                simp only [← Complex.ofReal_mul]
  have hpcont : Continuous p := by
    dsimp [p, realFourierPoly]
    fun_prop
  have hcomplexIntegrable : Integrable
      (fun k : Torus4 => latticeFourierSeries G k * (p k * conj (p k)))
      torus4Haar :=
    spectralContinuousComplex_integrable ⟨_, (continuous_latticeFourierSeries G hG).mul
      (hpcont.mul ((continuous_star.comp hpcont)))⟩
  have hcomplexIntegral :
      ∫ k : Torus4, latticeFourierSeries G k * (p k * conj (p k)) ∂torus4Haar =
        ∑ x ∈ a.support, ∑ y ∈ a.support,
          ((a x * a y : ℝ) : ℂ) * (G (y - x) : ℂ) := by
    have hsum (k : Torus4) :
        latticeFourierSeries G k * (p k * conj (p k)) =
          ∑ x ∈ a.support, ∑ y ∈ a.support,
            ((a x * a y : ℝ) : ℂ) *
              (latticeFourierSeries G k * latticeCharacter (x - y) k) := by
      rw [hpoly k]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y hy
      ring
    calc
      _ = ∫ k : Torus4,
          ∑ x ∈ a.support, ∑ y ∈ a.support,
            ((a x * a y : ℝ) : ℂ) *
              (latticeFourierSeries G k * latticeCharacter (x - y) k)
            ∂torus4Haar := by
              apply integral_congr_ae
              exact Filter.Eventually.of_forall hsum
      _ = ∑ x ∈ a.support, ∑ y ∈ a.support,
          ((a x * a y : ℝ) : ℂ) *
            (∫ k : Torus4,
              latticeFourierSeries G k * latticeCharacter (x - y) k ∂torus4Haar) := by
              rw [integral_finsetSum a.support (fun x hx =>
                integrable_finsetSum a.support (fun y hy => by
                  exact spectralContinuousComplex_integrable
                    ⟨fun k => ((a x * a y : ℝ) : ℂ) *
                      (latticeFourierSeries G k * latticeCharacter (x - y) k), by
                        exact continuous_const.mul
                          ((continuous_latticeFourierSeries G hG).mul
                            (continuous_latticeCharacter (x - y)))⟩))]
              apply Finset.sum_congr rfl
              intro x hx
              rw [integral_finsetSum a.support (fun y hy => by
                exact spectralContinuousComplex_integrable
                  ⟨fun k => ((a x * a y : ℝ) : ℂ) *
                    (latticeFourierSeries G k * latticeCharacter (x - y) k), by
                      exact continuous_const.mul
                        ((continuous_latticeFourierSeries G hG).mul
                          (continuous_latticeCharacter (x - y)))⟩)]
              apply Finset.sum_congr rfl
              intro y hy
              rw [integral_const_mul]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro x hx
        apply Finset.sum_congr rfl
        intro y hy
        rw [spectralIntegral_latticeFourierSeries_character G hG (x - y)]
        congr 1
        simp [sub_eq_add_neg]
  calc
    ∫ k : Torus4, latticeFourierSeriesReal G k * finiteTestFourierWeight f k
        ∂torus4Haar =
      (∫ k : Torus4, latticeFourierSeries G k * (p k * conj (p k))
        ∂torus4Haar).re := by
          calc
            _ = ∫ k : Torus4,
                (latticeFourierSeries G k * (p k * conj (p k))).re
                ∂torus4Haar := by
                  apply integral_congr_ae
                  exact Filter.Eventually.of_forall fun k => hpoint k
            _ = _ := integral_re hcomplexIntegrable
    _ = (∑ x ∈ a.support, ∑ y ∈ a.support,
          ((a x * a y : ℝ) : ℂ) * (G (y - x) : ℂ)).re := by
          rw [hcomplexIntegral]
    _ = ∑ x ∈ a.support, ∑ y ∈ a.support,
          G (y - x) * a x * a y := by
          simp only [Complex.re_sum, Complex.ofReal_mul]
          apply Finset.sum_congr rfl
          intro x hx
          apply Finset.sum_congr rfl
          intro y hy
          norm_cast
          ring

private theorem spectralToeplitz_attached_eq
    (G : LatticePoint → ℝ) (a : LatticePoint →₀ ℝ) :
    (∑ x ∈ a.support.attach, ∑ y ∈ a.support.attach,
        G (y.1 - x.1) * a x.1 * a y.1) =
      ∑ x ∈ a.support, ∑ y ∈ a.support,
        G (y - x) * a x * a y := by
  classical
  rw [Finset.sum_attach (s := a.support) (f := fun x =>
    ∑ y ∈ a.support.attach, G (y.1 - x) * a x * a y.1)]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.sum_attach (s := a.support) (f := fun y =>
    G (y - x) * a x * a y)]

private theorem spectralFiniteTest_moment_spectral_sandwich
    {β : ℝ} (hβ : rootBetaThreshold ≤ β)
    (L : CubeCurvatureLimitState β (rootBeta_pos hβ)
    ) (s : ℕ → ℕ) (S : CurvatureCylinderState)
    (hpoint : ∀ P x, Tendsto
      (fun k => (averagedCylinderLaw (cubeStateToCylinderState L) (s k) P x).toReal)
      atTop (𝓝 ((S.law P x).toReal)))
    (hinv : ∀ a P, translateCylinderLaw S a P = S.law P)
    (hG : Summable (fun x => |spectralFieldStrengthCorrelation S x|))
    (f : FiniteRealTest) :
    betaDoublePrime rootPackingCoefficient β *
        (∫ k, torusCurlMultiplier 0 1 k * finiteTestFourierWeight f k ∂torus4Haar) ≤
      ∫ k, latticeFourierSeriesReal (spectralFieldStrengthCorrelation S) k *
        finiteTestFourierWeight f k ∂torus4Haar ∧
    (∫ k, latticeFourierSeriesReal (spectralFieldStrengthCorrelation S) k *
        finiteTestFourierWeight f k ∂torus4Haar) ≤
      β * (∫ k, torusCurlMultiplier 0 1 k * finiteTestFourierWeight f k ∂torus4Haar) := by
  let a := realPartCoefficients f
  have hmoment := spectralCurvatureWindow_secondMoment_bounds hβ L s S hpoint a
  rw [spectralWindowSecondMoment_eq_toeplitz hβ L s S hpoint hinv a] at hmoment
  rw [spectralToeplitz_attached_eq (spectralFieldStrengthCorrelation S) a] at hmoment
  have hQ := spectralFourierGreenQuadratic_source_test f
  have hF := spectralFourierSeries_finiteTest_integral
    (spectralFieldStrengthCorrelation S) hG f
  constructor
  · calc
      _ = betaDoublePrime rootPackingCoefficient β *
          fourierGreenQuadratic
            (spectralCurvatureWindowSource (realPartCoefficients f)) := by rw [hQ]
      _ ≤ ∑ x ∈ a.support, ∑ y ∈ a.support,
          spectralFieldStrengthCorrelation S (y - x) * a x * a y := hmoment.1
      _ = _ := hF.symm
  · calc
      _ = ∑ x ∈ a.support, ∑ y ∈ a.support,
          spectralFieldStrengthCorrelation S (y - x) * a x * a y := hF
      _ ≤ β * fourierGreenQuadratic
          (spectralCurvatureWindowSource (realPartCoefficients f)) := hmoment.2
      _ = _ := by rw [hQ]

/-- The curl multiplier is a ratio of a two-term subsum of nonnegative
chord squares to their full sum. -/
theorem torusCurlMultiplier_abs_le_one (i j : SpectralIndex) (hij : i ≠ j)
    (k : Torus4) : |torusCurlMultiplier i j k| ≤ 1 := by
  let f : SpectralIndex → ℝ := fun a => torusChordSquared k a
  let d : ℝ := ∑ a : SpectralIndex, f a
  let num : ℝ := f i + f j
  have hf (a : SpectralIndex) : 0 ≤ f a := torusChordSquared_nonneg k a
  have hd0 : 0 ≤ d := by
    dsimp [d]
    exact Finset.sum_nonneg fun a ha => hf a
  have hnum0 : 0 ≤ num := by
    dsimp [num, f]
    exact add_nonneg (hf i) (hf j)
  have hnumLe : num ≤ d := by
    have hpair : ∑ a ∈ ({i, j} : Finset SpectralIndex), f a = num := by
      simp [num, hij]
    rw [← hpair]
    dsimp [d]
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    intro a ha hnot
    exact hf a
  by_cases hd : d = 0
  · simp [torusCurlMultiplier, d, f, hd]
  · have hdpos : 0 < d := lt_of_le_of_ne hd0 (Ne.symm hd)
    have hquot0 : 0 ≤ num / d := div_nonneg hnum0 hdpos.le
    have hquot1 : num / d ≤ 1 := (div_le_one₀ hdpos).2 hnumLe
    have hquot : torusCurlMultiplier i j k = num / d := by
      simp [torusCurlMultiplier, d, num, f, hd]
    rw [hquot]
    exact abs_le.mpr ⟨by linarith, hquot1⟩


theorem torusCurlMultiplier_measurable :
    Measurable (torusCurlMultiplier 0 1) := by
  classical
  let d : Torus4 → ℝ := fun k =>
    ∑ a : SpectralIndex, torusChordSquared k a
  let u : Torus4 → ℝ := fun k =>
    torusChordSquared k 0 + torusChordSquared k 1
  have hd : Measurable d := by
    dsimp [d]
    exact (continuous_finsetSum _ fun i hi => continuous_torusChordSquared i).measurable
  have hu : Measurable u := by
    dsimp [u]
    exact (continuous_torusChordSquared 0).measurable.add
      (continuous_torusChordSquared 1).measurable
  have hquot : Measurable (fun k : Torus4 => u k / d k) := hu.div hd
  have heq (k : Torus4) : torusCurlMultiplier 0 1 k = u k / d k := by
    by_cases hdk : d k = 0
    · have hcoord (i : SpectralIndex) : torusChordSquared k i = 0 := by
        have hle : torusChordSquared k i ≤ d k := by
          dsimp [d]
          exact Finset.single_le_sum (s := Finset.univ)
            (fun a ha => torusChordSquared_nonneg k a) (Finset.mem_univ i)
        nlinarith [torusChordSquared_nonneg k i]
      have hu0 : u k = 0 := by simp [u, hcoord]
      simp [torusCurlMultiplier, d, u, hdk, hu0]
    · simp [torusCurlMultiplier, d, u, hdk]
  have hfun : torusCurlMultiplier 0 1 = fun k => u k / d k := funext heq
  rw [hfun]
  exact hquot

theorem torusCurlMultiplier_integrable :
    MeasureTheory.Integrable (torusCurlMultiplier 0 1) torus4Haar := by
  exact MeasureTheory.Integrable.of_bound
    (torusCurlMultiplier_measurable.aestronglyMeasurable) 1
    (Filter.Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs]
      exact torusCurlMultiplier_abs_le_one 0 1 (by decide) z)

/--
The Fourier-form quadratic comparison and localizers remain
explicit hypotheses for the state application.
-/
theorem no_absSummable_of_integrable_curlFourierTestSandwich
    (G : LatticePoint → ℝ) (hG : Summable (fun x => |G x|))
    (βlo βhi : ℝ) (hβlo : 0 < βlo)
    (hqInt : MeasureTheory.Integrable (torusCurlMultiplier 0 1) torus4Haar)
    (hform : ∀ f : FiniteRealTest,
      βlo * (∫ k : Torus4, torusCurlMultiplier 0 1 k *
          finiteTestFourierWeight f k ∂torus4Haar) ≤
          ∫ k : Torus4, latticeFourierSeriesReal G k *
            finiteTestFourierWeight f k ∂torus4Haar ∧
        (∫ k : Torus4, latticeFourierSeriesReal G k *
            finiteTestFourierWeight f k ∂torus4Haar) ≤
          βhi * (∫ k : Torus4, torusCurlMultiplier 0 1 k *
            finiteTestFourierWeight f k ∂torus4Haar)) :
    False := by
  let kin : ℕ → Torus4 := fun n =>
    waveToTorus (axisWave 0 (directionalScale n))
  let kout : ℕ → Torus4 := fun n =>
    waveToTorus (axisWave 2 (directionalScale n))
  have hkin : Tendsto kin atTop (𝓝 0) := by
    have h := continuous_waveToTorus.continuousAt.tendsto.comp
      (axisWave_tendsto_zero 0)
    simpa only [kin, Function.comp_def, waveToTorus_zero] using h
  have hkout : Tendsto kout atTop (𝓝 0) := by
    have h := continuous_waveToTorus.continuousAt.tendsto.comp
      (axisWave_tendsto_zero 2)
    simpa only [kout, Function.comp_def, waveToTorus_zero] using h
  have hkinNe : ∀ n, kin n ≠ 0 := by
    intro n hz
    dsimp [kin] at hz
    have hc := congrArg (fun z => torusChordSquared z 0) hz
    rw [torusChordSquared_waveToTorus, torusChordSquared_zero] at hc
    exact (directionalScale_chord_ne_zero n) hc
  have hkoutNe : ∀ n, kout n ≠ 0 := by
    intro n hz
    dsimp [kout] at hz
    have hc := congrArg (fun z => torusChordSquared z 2) hz
    rw [torusChordSquared_waveToTorus, torusChordSquared_zero] at hc
    exact (directionalScale_chord_ne_zero n) hc
  exact no_summable_spectral_density_of_integrable_finite_test_sandwich
    G hG βlo βhi hβlo (torusCurlMultiplier 0 1)
    spectralPolynomialLocalizerTest spectralPolynomialLocalizerTests_localizers
    (fun k => torusCurlMultiplier_neg 0 1 k) hqInt
    (fun k hk => torusCurlMultiplier_continuousAt hk) hform kin kout
    hkin hkout hkinNe hkoutNe
    (fun n => torusCurlMultiplier_axis_in 0 1 (by decide) n)
    (fun n => torusCurlMultiplier_axis_out 0 1 2 (by decide) (by decide) n)

/-- Translation invariance plus the finite-test moment sandwich forces the
same-orientation plaquette correlation to fail absolute summability. -/
theorem spectralTranslationInvariantCorrelation_not_absSummable
    {β : ℝ} (hβ : rootBetaThreshold ≤ β)
    (L : CubeCurvatureLimitState β (rootBeta_pos hβ))
    (s : ℕ → ℕ) (S : CurvatureCylinderState)
    (hpoint : ∀ P x, Tendsto
      (fun k => (averagedCylinderLaw (cubeStateToCylinderState L) (s k) P x).toReal)
      atTop (𝓝 ((S.law P x).toReal)))
    (hinv : ∀ a P, translateCylinderLaw S a P = S.law P)
    (hβlo : 0 < betaDoublePrime rootPackingCoefficient β) :
    ¬ Summable (fun x => |spectralFieldStrengthCorrelation S x|) := by
  intro hsum
  have hform (f : FiniteRealTest) :=
    spectralFiniteTest_moment_spectral_sandwich hβ L s S hpoint hinv hsum f
  exact no_absSummable_of_integrable_curlFourierTestSandwich
    (spectralFieldStrengthCorrelation S) hsum
    (betaDoublePrime rootPackingCoefficient β) β hβlo
    torusCurlMultiplier_integrable
    hform


theorem fs82_root_nonsummable_fieldStrengthCorrelation :
    ∃ B : ℝ,
      (∀ β, B ≤ β → 0 < betaDoublePrime rootPackingCoefficient β) ∧
      ∀ (β : ℝ) (hβ : max rootBetaThreshold B ≤ β),
        ∃ L : CubeCurvatureLimitState β
            (rootBeta_pos (le_trans (le_max_left rootBetaThreshold B) hβ)),
          ∃ s : ℕ → ℕ, StrictMono s ∧
            ∃ S : CurvatureCylinderState,
              (∀ P x, Tendsto
                (fun k => (averagedCylinderLaw (cubeStateToCylinderState L) (s k) P x).toReal)
                atTop (𝓝 ((S.law P x).toReal))) ∧
              (∀ a P, translateCylinderLaw S a P = S.law P) ∧
              ¬ Summable (fun x => |spectralFieldStrengthCorrelation S x|) := by
  obtain ⟨B, hB⟩ := Filter.eventually_atTop.1
    rootBetaDoublePrime_behavior.2
  refine ⟨B, ?_, ?_⟩
  · intro β hβ
    exact (hB β hβ).1
  · intro β hβ
    have hβroot : rootBetaThreshold ≤ β :=
      le_trans (le_max_left rootBetaThreshold B) hβ
    obtain ⟨L⟩ := exists_cubeCurvatureLimitState β (rootBeta_pos hβroot)
    obtain ⟨s, hs, S, hpoint, hinv, _hmoment⟩ :=
      exists_translationInvariantCylinderLimit_with_secondMomentBounds hβroot L
    refine ⟨L, s, hs, S, hpoint, hinv, ?_⟩
    exact spectralTranslationInvariantCorrelation_not_absSummable hβroot L s S
      hpoint hinv (hB β (le_trans (le_max_right rootBetaThreshold B) hβ)).1

end FroehlichSpencer.FS82.Infinite.Nonsummability

end
