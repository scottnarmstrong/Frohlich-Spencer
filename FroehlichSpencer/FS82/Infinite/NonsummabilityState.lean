/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Infinite.LimitStateMoments
public import FroehlichSpencer.FS82.Infinite.NonsummabilityMoments
public import FroehlichSpencer.FS82.Infinite.FourierParseval
public import FroehlichSpencer.FS82.Infinite.LimitStateRoot

/-!
# Translation averages of curvature cylinder states

Translations act on the local integer-curvature coordinates by translating
the underlying plaquettes. This file develops the projective cylinder laws
and their finite Følner averages.
-/

@[expose] public section

open Filter Topology MeasureTheory
open FroehlichSpencer.FS82.Cubical

namespace FroehlichSpencer.FS82.Infinite.Nonsummability

open FroehlichSpencer.FS82.Infinite
open FroehlichSpencer.FS82.Infinite.Fourier
open FroehlichSpencer.FS82.Moment.Comparison
open FroehlichSpencer.FS82.Root
open FroehlichSpencer.FS82.Gaussian

abbrev LatticeShift := Fin 4 → ℤ

/-- Translation of one lattice coordinate, preserving vertex/edge parity. -/
def translateLatticeCoord (a : ℤ) : LatticeCoord → LatticeCoord :=
  Sum.map (fun z => z + a) (fun z => z + a)

/-- Translation of a cubical cell. -/
def translateLatticeCell (a : LatticeShift) (c : LatticeCell 4) : LatticeCell 4 :=
  fun i => translateLatticeCoord (a i) (c i)

theorem latticeCellDegree_translate (a : LatticeShift) (c : LatticeCell 4) :
    latticeCellDegree (translateLatticeCell a c) = latticeCellDegree c := by
  classical
  unfold latticeCellDegree
  apply congrArg Finset.card
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  simp [translateLatticeCell, translateLatticeCoord, latticeIsEdge, Sum.isRight_map]

theorem latticeCellAxes_translate (a : LatticeShift) (c : LatticeCell 4) :
    Fourier.latticeCellAxes (translateLatticeCell a c) = Fourier.latticeCellAxes c := by
  classical
  ext i
  simp only [Fourier.latticeCellAxes, Finset.mem_filter, Finset.mem_univ, true_and]
  change latticeIsEdge (translateLatticeCoord (a i) (c i)) ↔ latticeIsEdge (c i)
  cases h : c i <;> simp [translateLatticeCoord, latticeIsEdge]

theorem latticeRankBefore_translate (a : LatticeShift) (c : LatticeCell 4)
    (i : Fin 4) :
    latticeRankBefore (translateLatticeCell a c) i = latticeRankBefore c i := by
  have hEdge (j : Fin 4) :
      latticeIsEdge (translateLatticeCell a c j) ↔ latticeIsEdge (c j) := by
    change latticeIsEdge (translateLatticeCoord (a j) (c j)) ↔ latticeIsEdge (c j)
    cases c j <;> simp [translateLatticeCoord, latticeIsEdge]
  unfold latticeRankBefore
  congr 1
  ext j
  simp [hEdge j]

theorem latticeCellOrientationSign_translate (a : LatticeShift) (c : LatticeCell 4) :
    Gaussian.latticeCellOrientationSign (translateLatticeCell a c) =
      Gaussian.latticeCellOrientationSign c := by
  have haxes : Gaussian.latticeCellAxes (translateLatticeCell a c) =
      Gaussian.latticeCellAxes c := by
    change Fourier.latticeCellAxes (translateLatticeCell a c) = Fourier.latticeCellAxes c
    exact latticeCellAxes_translate a c
  simp [Gaussian.latticeCellOrientationSign, haxes]


/-- Lattice point represented by the displacement `a`. -/
def latticeShiftPoint (a : LatticeShift) : LatticePoint :=
  Prod.mk (a 0) (Prod.mk (a 1) (Prod.mk (a 2) (a 3)))


theorem translateLatticeCell_zero (c : LatticeCell 4) :
    translateLatticeCell 0 c = c := by
  funext i
  cases h : c i <;> simp [translateLatticeCell, translateLatticeCoord, h]

theorem translateLatticeCell_add (a b : LatticeShift) (c : LatticeCell 4) :
    translateLatticeCell a (translateLatticeCell b c) =
      translateLatticeCell (a + b) c := by
  funext i
  cases hc : c i <;>
    simp [translateLatticeCell, translateLatticeCoord, hc, Pi.add_apply,
      add_left_comm, add_comm]

/-- The equivalence of lattice cells induced by a fixed translation. -/
def translateLatticeCellEquiv (a : LatticeShift) : LatticeCell 4 ≃ LatticeCell 4 where
  toFun := translateLatticeCell a
  invFun := translateLatticeCell (-a)
  left_inv := by
    intro c
    funext i
    cases hc : c i <;> simp [translateLatticeCell, translateLatticeCoord, hc]

  right_inv := by
    intro c
    funext i
    cases hc : c i <;> simp [translateLatticeCell, translateLatticeCoord, hc]

noncomputable def translateIntegerChain (a : LatticeShift) :
    LatticeChain 4 →ₗ[ℤ] LatticeChain 4 :=
  Finsupp.lmapDomain ℤ ℤ (translateLatticeCell a)

noncomputable def translateRealChain (a : LatticeShift) :
    RealLatticeChain 4 →ₗ[ℝ] RealLatticeChain 4 :=
  Finsupp.lmapDomain ℝ ℝ (translateLatticeCell a)

@[simp] theorem translateIntegerChain_single (a : LatticeShift)
    (c : LatticeCell 4) (z : ℤ) :
    translateIntegerChain a (Finsupp.single c z) =
      Finsupp.single (translateLatticeCell a c) z := by
  simp [translateIntegerChain]

@[simp] theorem translateRealChain_single (a : LatticeShift)
    (c : LatticeCell 4) (r : ℝ) :
    translateRealChain a (Finsupp.single c r) =
      Finsupp.single (translateLatticeCell a c) r := by
  simp [translateRealChain]

theorem translateRealChain_add_action (a b : LatticeShift) (q : RealLatticeChain 4) :
    translateRealChain a (translateRealChain b q) =
      translateRealChain (a + b) q := by
  induction q using Finsupp.induction_linear with
  | zero => simp [translateRealChain]
  | add q r hq hr => simp [map_add, hq, hr]
  | single c r =>
      simp [translateRealChain_single, translateLatticeCell_add]

theorem translateRealChain_zero_action (q : RealLatticeChain 4) :
    translateRealChain 0 q = q := by
  induction q using Finsupp.induction_linear with
  | zero => simp [translateRealChain]
  | add q r hq hr => simp [map_add, hq, hr]
  | single c r => simp [translateRealChain_single, translateLatticeCell_zero]

theorem translateRealChain_support (a : LatticeShift) (q : RealLatticeChain 4) :
    (translateRealChain a q).support =
      q.support.map (translateLatticeCellEquiv a).toEmbedding := by
  classical
  ext c
  constructor
  · intro hc
    let d := translateLatticeCell (-a) c
    have hdc : translateLatticeCell a d = c :=
      (translateLatticeCellEquiv a).right_inv c
    have heval : (translateRealChain a q) c = q d := by
      change Finsupp.mapDomain (translateLatticeCell a) q c = q d
      rw [← hdc]
      exact Finsupp.mapDomain_apply_of_injective
        (translateLatticeCellEquiv a).injective q d
    have hd : d ∈ q.support := by
      apply Finsupp.mem_support_iff.mpr
      have hval : (translateRealChain a q) c ≠ 0 :=
        Finsupp.mem_support_iff.mp hc
      rw [heval] at hval
      exact hval
    exact Finset.mem_map.mpr ⟨d, hd, hdc⟩
  · intro hc
    rcases Finset.mem_map.mp hc with ⟨d, hd, hdc⟩
    rw [Finsupp.mem_support_iff]
    rw [← hdc]
    change (translateRealChain a q) (translateLatticeCell a d) ≠ 0
    have heval : (translateRealChain a q) (translateLatticeCell a d) = q d := by
      change Finsupp.mapDomain (translateLatticeCell a) q
        (translateLatticeCell a d) = q d
      exact Finsupp.mapDomain_apply_of_injective
        (translateLatticeCellEquiv a).injective q d
    rw [heval]
    exact Finsupp.mem_support_iff.mp hd

theorem castLatticeChain_add (q r : LatticeChain 4) :
    castLatticeChain (q + r) = castLatticeChain q + castLatticeChain r := by
  ext c
  simp [castLatticeChain]

theorem translateLatticeCell_update_inl (a : LatticeShift) (c : LatticeCell 4)
    (i : Fin 4) (z : ℤ) :
    translateLatticeCell a (Function.update c i (Sum.inl z)) =
      Function.update (translateLatticeCell a c) i (Sum.inl (z + a i)) := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [translateLatticeCell, translateLatticeCoord]
  · simp [translateLatticeCell, hji]

theorem translateLatticeCell_update_inr (a : LatticeShift) (c : LatticeCell 4)
    (i : Fin 4) (z : ℤ) :
    translateLatticeCell a (Function.update c i (Sum.inr z)) =
      Function.update (translateLatticeCell a c) i (Sum.inr (z + a i)) := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [translateLatticeCell, translateLatticeCoord]
  · simp [translateLatticeCell, hji]

theorem latticeBoundaryBasis_translate (a : LatticeShift) (c : LatticeCell 4) :
    translateIntegerChain a (latticeBoundaryBasis c) =
      latticeBoundaryBasis (translateLatticeCell a c) := by
  classical
  unfold latticeBoundaryBasis
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  cases hci : c i with
  | inl t => simp [hci, translateLatticeCell, translateLatticeCoord]
  | inr t =>
      simp only [map_smul, map_sub, latticeBasis, translateIntegerChain_single]
      rw [latticeRankBefore_translate]
      simp only [latticeUpperFace, latticeLowerFace]
      rw [translateLatticeCell_update_inl]
      rw [translateLatticeCell_update_inl]
      simp [translateLatticeCell, translateLatticeCoord, hci, add_assoc]
      ring_nf

theorem latticeCoboundaryBasis_translate (a : LatticeShift) (c : LatticeCell 4) :
    translateIntegerChain a (latticeCoboundaryBasis c) =
      latticeCoboundaryBasis (translateLatticeCell a c) := by
  classical
  unfold latticeCoboundaryBasis
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  cases hci : c i with
  | inl t =>
      simp only [map_smul, map_sub, latticeBasis, translateIntegerChain_single]
      rw [latticeRankBefore_translate]
      simp only [latticeEdgeCell]
      rw [translateLatticeCell_update_inr]
      rw [translateLatticeCell_update_inr]
      simp [translateLatticeCell, translateLatticeCoord, hci]
      ring_nf
  | inr t => simp [translateLatticeCell, translateLatticeCoord, hci]

theorem translateRealChain_cast (a : LatticeShift) (q : LatticeChain 4) :
    translateRealChain a (castLatticeChain q) =
      castLatticeChain (translateIntegerChain a q) := by
  induction q using Finsupp.induction_linear with
  | zero => simp [translateRealChain, translateIntegerChain, castLatticeChain]
  | add q r hq hr => simp [map_add, castLatticeChain_add, hq, hr]
  | single c z =>
      simp [translateRealChain, translateIntegerChain, castLatticeChain]

theorem globalBoundary_translate (a : LatticeShift) (q : RealLatticeChain 4) :
    translateRealChain a (globalBoundary q) =
      globalBoundary (translateRealChain a q) := by
  have hsingle (c : LatticeCell 4) (r : ℝ) :
      globalBoundary (Finsupp.single c r) =
        r • castLatticeChain (latticeBoundaryBasis c) := by
    calc
      globalBoundary (Finsupp.single c r) =
          r • globalBoundary (Finsupp.single c 1) := by
            rw [show Finsupp.single c r = r • Finsupp.single c (1 : ℝ) by
              ext d
              simp]
            exact map_smul (globalBoundary) r (Finsupp.single c (1 : ℝ))
      _ = r • castLatticeChain (latticeBoundaryBasis c) := by
          rw [globalBoundary, realLatticeBoundary_basis]
  induction q using Finsupp.induction_linear with
  | zero => simp [translateRealChain]
  | add q r hq hr => simp [map_add, hq, hr]
  | single c r =>
      rw [hsingle c r, map_smul, translateRealChain_cast,
        latticeBoundaryBasis_translate, translateRealChain_single,
        hsingle (translateLatticeCell a c) r]

theorem globalCoboundary_translate (a : LatticeShift) (q : RealLatticeChain 4) :
    translateRealChain a (globalCoboundary q) =
      globalCoboundary (translateRealChain a q) := by
  have hsingle (c : LatticeCell 4) (r : ℝ) :
      globalCoboundary (Finsupp.single c r) =
        r • castLatticeChain (latticeCoboundaryBasis c) := by
    change Gaussian.sourceRealLatticeCoboundary (Finsupp.single c r) = _
    exact Gaussian.sourceRealLatticeCoboundary_single c r
  induction q using Finsupp.induction_linear with
  | zero => simp [translateRealChain]
  | add q r hq hr => simp [map_add, hq, hr]
  | single c r =>
      rw [hsingle c r, map_smul, translateRealChain_cast,
        latticeCoboundaryBasis_translate, translateRealChain_single,
        hsingle (translateLatticeCell a c) r]

noncomputable def translateGlobalLinkField (a : LatticeShift) (μ : GlobalLinkField) :
    GlobalLinkField where
  val := translateRealChain a μ.1
  property := by
    intro c hc
    let d := translateLatticeCell (-a) c
    have hdc : translateLatticeCell a d = c := by
      exact (translateLatticeCellEquiv a).right_inv c
    have heval : (translateRealChain a μ.1) c = μ.1 d := by
      change Finsupp.mapDomain (translateLatticeCell a) μ.1 c = μ.1 d
      rw [← hdc]
      exact Finsupp.mapDomain_apply_of_injective
        (translateLatticeCellEquiv a).injective μ.1 d
    have hd : d ∈ μ.1.support := by
      apply Finsupp.mem_support_iff.mpr
      have hval : (translateRealChain a μ.1) c ≠ 0 :=
        Finsupp.mem_support_iff.mp hc
      rw [heval] at hval
      exact hval
    calc
      latticeCellDegree c = latticeCellDegree (translateLatticeCell a d) := by rw [hdc]
      _ = latticeCellDegree d := latticeCellDegree_translate a d
      _ = 1 := μ.2 d hd

theorem translateGlobalLinkField_coClosed (a : LatticeShift) (μ : GlobalLinkField)
    (hμ : globallyCoClosed μ) :
    globallyCoClosed (translateGlobalLinkField a μ) := by
  change globalBoundary (translateRealChain a (μ : RealLatticeChain 4)) = 0
  rw [← globalBoundary_translate]
  rw [hμ]
  simp

theorem translateGlobalLinkField_add (a b : LatticeShift) (μ : GlobalLinkField) :
    translateGlobalLinkField a (translateGlobalLinkField b μ) =
      translateGlobalLinkField (a + b) μ := by
  apply Subtype.ext
  exact translateRealChain_add_action a b μ.1

theorem translateGlobalLinkField_zero (μ : GlobalLinkField) :
    translateGlobalLinkField 0 μ = μ := by
  apply Subtype.ext
  exact translateRealChain_zero_action μ.1

noncomputable def translateGlobalPlaquetteField (a : LatticeShift)
    (σ : GlobalPlaquetteField) : GlobalPlaquetteField where
  val := translateRealChain a σ.1
  property := by
    intro c hc
    let d := translateLatticeCell (-a) c
    have hdc : translateLatticeCell a d = c :=
      (translateLatticeCellEquiv a).right_inv c
    have heval : (translateRealChain a σ.1) c = σ.1 d := by
      change Finsupp.mapDomain (translateLatticeCell a) σ.1 c = σ.1 d
      rw [← hdc]
      exact Finsupp.mapDomain_apply_of_injective
        (translateLatticeCellEquiv a).injective σ.1 d
    have hd : d ∈ σ.1.support := by
      apply Finsupp.mem_support_iff.mpr
      have hval : (translateRealChain a σ.1) c ≠ 0 :=
        Finsupp.mem_support_iff.mp hc
      rw [heval] at hval
      exact hval
    calc
      latticeCellDegree c = latticeCellDegree (translateLatticeCell a d) := by rw [hdc]
      _ = latticeCellDegree d := latticeCellDegree_translate a d
      _ = 2 := σ.2 d hd

theorem globalBoundary_translateGlobalPlaquetteField (a : LatticeShift)
    (σ : GlobalPlaquetteField) :
    globalBoundary (translateGlobalPlaquetteField a σ) =
      translateRealChain a (globalBoundary σ) := by
  exact (globalBoundary_translate a σ.1).symm

theorem globalPairing_single (c d : LatticeCell 4) (x y : ℝ) :
    globalPairing (Finsupp.single c x) (Finsupp.single d y) =
      if c = d then x * y else 0 := by
  by_cases h : c = d
  · subst d
    simp [globalPairing]
  · simp [globalPairing, h]

theorem globalPairing_translate (a : LatticeShift) (q r : RealLatticeChain 4) :
    globalPairing (translateRealChain a q) (translateRealChain a r) =
      globalPairing q r := by
  induction q using Finsupp.induction_linear with
  | zero => simp [globalPairing]
  | add q₁ q₂ hq₁ hq₂ =>
      simp [map_add, globalPairing_add_left, hq₁, hq₂]
  | single c x =>
      induction r using Finsupp.induction_linear with
      | zero => simp [globalPairing]
      | add r₁ r₂ hr₁ hr₂ =>
          rw [map_add, globalPairing_add_right, globalPairing_add_right, hr₁, hr₂]
      | single d y =>
          have heq : translateLatticeCell a c = translateLatticeCell a d ↔ c = d := by
            constructor
            · intro h
              exact (translateLatticeCellEquiv a).injective h
            · intro h
              rw [h]
          simp [translateRealChain_single, globalPairing_single, heq]

theorem globalNormSq_translate (a : LatticeShift) (q : RealLatticeChain 4) :
    globalNormSq (translateRealChain a q) = globalNormSq q := by
  exact globalPairing_translate a q q

theorem globalVariationalObjective_translate (a : LatticeShift)
    (μ φ : GlobalLinkField) :
    globalVariationalObjective (translateGlobalLinkField a μ)
        (translateGlobalLinkField a φ) =
      globalVariationalObjective μ φ := by
  unfold globalVariationalObjective
  change 2 * globalPairing (translateRealChain a μ.1) (translateRealChain a φ.1) -
      globalNormSq (globalCoboundary (translateRealChain a φ.1)) =
    2 * globalPairing μ.1 φ.1 - globalNormSq (globalCoboundary φ.1)
  rw [globalPairing_translate, ← globalCoboundary_translate, globalNormSq_translate]

theorem translateGlobalLinkField_leftInverse (a : LatticeShift)
    (μ : GlobalLinkField) :
    translateGlobalLinkField a (translateGlobalLinkField (-a) μ) = μ := by
  calc
    translateGlobalLinkField a (translateGlobalLinkField (-a) μ) =
        translateGlobalLinkField (a + -a) μ := translateGlobalLinkField_add a (-a) μ
    _ = μ := by rw [show a + -a = 0 by ext i; simp, translateGlobalLinkField_zero]


theorem globalVariationalCovariance_translate (a : LatticeShift)
    (μ : GlobalLinkField) :
    globalVariationalCovariance (translateGlobalLinkField a μ) =
      globalVariationalCovariance μ := by
  have hset :
      {r : ℝ | ∃ φ : GlobalLinkField,
        globalVariationalObjective (translateGlobalLinkField a μ) φ = r} =
      {r : ℝ | ∃ φ : GlobalLinkField, globalVariationalObjective μ φ = r} := by
    ext r
    constructor
    · rintro ⟨φ, hφ⟩
      let ψ := translateGlobalLinkField (-a) φ
      have hback : translateGlobalLinkField a ψ = φ :=
        translateGlobalLinkField_leftInverse a φ
      have hobj := globalVariationalObjective_translate a μ ψ
      rw [hback] at hobj
      exact ⟨ψ, hobj.symm.trans hφ⟩
    · rintro ⟨φ, hφ⟩
      refine ⟨translateGlobalLinkField a φ, ?_⟩
      simpa using (globalVariationalObjective_translate a μ φ).trans hφ
  unfold globalVariationalCovariance
  rw [hset]

theorem fourierGreenQuadratic_translate (a : LatticeShift) (μ : GlobalLinkField)
    (hμ : globallyCoClosed μ) :
    fourierGreenQuadratic (translateGlobalLinkField a μ) =
      fourierGreenQuadratic μ := by
  let μ' := translateGlobalLinkField a μ
  have hμ' : globallyCoClosed μ' := translateGlobalLinkField_coClosed a μ hμ
  calc
    fourierGreenQuadratic μ' = globalVariationalCovariance μ' :=
      (FourierGreenEquality.globallyCoClosed_fourier_green_eq_covariance μ' hμ').symm
    _ = globalVariationalCovariance μ := globalVariationalCovariance_translate a μ
    _ = fourierGreenQuadratic μ :=
      FourierGreenEquality.globallyCoClosed_fourier_green_eq_covariance μ hμ

/-- The induced equivalence on global plaquette coordinates. -/
def translatePlaquetteEquiv (a : LatticeShift) : GlobalIntegerPlaquette ≃
    GlobalIntegerPlaquette where
  toFun p := ⟨translateLatticeCell a p.1, by
    rw [latticeCellDegree_translate]
    exact p.2⟩
  invFun p := ⟨translateLatticeCell (-a) p.1, by
    rw [latticeCellDegree_translate]
    exact p.2⟩
  left_inv := by
    intro p
    apply Subtype.ext
    exact (translateLatticeCellEquiv a).left_inv p.1
  right_inv := by
    intro p
    apply Subtype.ext
    exact (translateLatticeCellEquiv a).right_inv p.1

theorem translatePlaquetteEquiv_add (a b : LatticeShift) (p : GlobalIntegerPlaquette) :
    translatePlaquetteEquiv a (translatePlaquetteEquiv b p) =
      translatePlaquetteEquiv (a + b) p := by
  apply Subtype.ext
  exact translateLatticeCell_add a b p.1

/-- The translate of a finite plaquette-coordinate set. -/
def translatePlaquettes (a : LatticeShift) (P : Finset GlobalIntegerPlaquette) :
    Finset GlobalIntegerPlaquette := P.map (translatePlaquetteEquiv a).toEmbedding

/-- Translating a compact plaquette field translates its finite curvature
coordinate set. -/
theorem fillingCurvatureIndexSet_translate (a : LatticeShift)
    (σ : GlobalPlaquetteField) :
    fillingCurvatureIndexSet (translateGlobalPlaquetteField a σ) =
      translatePlaquettes a (fillingCurvatureIndexSet σ) := by
  classical
  ext p
  constructor
  · intro hp
    change p ∈ ((translateRealChain a σ.1).support.attach).map
      (fillingPlaquetteEmbedding (translateGlobalPlaquetteField a σ)) at hp
    rcases Finset.mem_map.mp hp with ⟨c, hc, hcp⟩
    have hcs : c.1 ∈ (translateRealChain a σ.1).support := c.2
    rw [translateRealChain_support] at hcs
    rcases Finset.mem_map.mp hcs with ⟨d, hd, hdc⟩
    have hmem : fillingPlaquetteEmbedding σ ⟨d, hd⟩ ∈
        fillingCurvatureIndexSet σ := by
      change fillingPlaquetteEmbedding σ ⟨d, hd⟩ ∈
        ((σ.1.support.attach).map (fillingPlaquetteEmbedding σ))
      exact Finset.mem_map.mpr ⟨⟨d, hd⟩, Finset.mem_attach _ _, rfl⟩
    refine Finset.mem_map.mpr ⟨fillingPlaquetteEmbedding σ ⟨d, hd⟩, hmem, ?_⟩
    apply Subtype.ext
    have hcp' := congrArg Subtype.val hcp
    change translateLatticeCell a d = p.1
    rw [← hcp']
    exact hdc
  · intro hp
    rcases Finset.mem_map.mp hp with ⟨q, hq, hpq⟩
    change q ∈ fillingCurvatureIndexSet σ at hq
    change p ∈ ((translateRealChain a σ.1).support.attach).map
      (fillingPlaquetteEmbedding (translateGlobalPlaquetteField a σ))
    rcases Finset.mem_map.mp hq with ⟨c, hc, hcq⟩
    have hsupport : translateLatticeCell a c.1 ∈
        (translateRealChain a σ.1).support := by
      rw [translateRealChain_support]
      exact Finset.mem_map.mpr ⟨c.1, c.2, rfl⟩
    apply Finset.mem_map.mpr
    refine ⟨⟨translateLatticeCell a c.1, hsupport⟩,
      Finset.mem_attach _ _, ?_⟩
    apply Subtype.ext
    have hqval : q.1 = c.1 := by
      simpa [fillingPlaquetteEmbedding] using (congrArg Subtype.val hcq).symm
    have hpval : translateLatticeCell a q.1 = p.1 := by
      simpa [translatePlaquetteEquiv] using congrArg Subtype.val hpq
    rw [hqval] at hpval
    exact hpval

theorem translateRealChain_apply_translateCell (a : LatticeShift)
    (q : RealLatticeChain 4) (c : LatticeCell 4) :
    translateRealChain a q (translateLatticeCell a c) = q c := by
  change Finsupp.mapDomain (translateLatticeCell a) q (translateLatticeCell a c) = q c
  exact Finsupp.mapDomain_apply_of_injective
    (translateLatticeCellEquiv a).injective q c

noncomputable def translateFillingIndexEquiv (a : LatticeShift)
    (σ : GlobalPlaquetteField) :
    fillingCurvatureIndexSet σ ≃
      fillingCurvatureIndexSet (translateGlobalPlaquetteField a σ) where
  toFun p := ⟨translatePlaquetteEquiv a p.1, by
    rw [fillingCurvatureIndexSet_translate]
    exact Finset.mem_map.mpr ⟨p.1, p.2, rfl⟩⟩
  invFun q := ⟨translatePlaquetteEquiv (-a) q.1, by
    have hP := fillingCurvatureIndexSet_translate a σ
    have hq : q.1 ∈ translatePlaquettes a (fillingCurvatureIndexSet σ) := by
      rw [← hP]
      exact q.2
    rcases Finset.mem_map.mp hq with ⟨p, hp, hqp⟩
    have hqval : q.1 = translatePlaquetteEquiv a p := hqp.symm
    have hinv : translatePlaquetteEquiv (-a) (translatePlaquetteEquiv a p) = p := by
      exact (translatePlaquetteEquiv a).left_inv p
    rw [hqval, hinv]
    exact hp⟩
  left_inv := by
    intro p
    apply Subtype.ext
    exact (translatePlaquetteEquiv a).left_inv p.1
  right_inv := by
    intro q
    apply Subtype.ext
    exact (translatePlaquetteEquiv a).right_inv q.1

theorem fillingPlaquetteCoeff_translate (a : LatticeShift)
    (σ : GlobalPlaquetteField) (p : fillingCurvatureIndexSet σ) :
    fillingPlaquetteCoeff (translateGlobalPlaquetteField a σ)
      (translateFillingIndexEquiv a σ p) = fillingPlaquetteCoeff σ p := by
  unfold fillingPlaquetteCoeff
  change translateRealChain a σ.1 (translateLatticeCell a p.1.1) = σ.1 p.1.1
  exact translateRealChain_apply_translateCell a σ.1 p.1.1

theorem sourceFillingCurvaturePairing_translate (a : LatticeShift)
    (σ : GlobalPlaquetteField) (x : fillingCurvatureIndexSet σ → ℤ) :
    sourceFillingCurvaturePairing (translateGlobalPlaquetteField a σ)
        (fun q => x ((translateFillingIndexEquiv a σ).symm q)) =
      sourceFillingCurvaturePairing σ x := by
  classical
  unfold sourceFillingCurvaturePairing
  rw [← (translateFillingIndexEquiv a σ).sum_comp]
  apply Finset.sum_congr rfl
  intro p hp
  simp only [Equiv.symm_apply_apply]
  have hsign : latticeCellOrientationSign
      (translateLatticeCell a p.1.1) = latticeCellOrientationSign p.1.1 :=
    latticeCellOrientationSign_translate a p.1.1
  have hsign' : latticeCellOrientationSign
      ((translateFillingIndexEquiv a σ p).1.1) = latticeCellOrientationSign p.1.1 := by
    change latticeCellOrientationSign (translateLatticeCell a p.1.1) = _
    exact hsign
  rw [hsign', fillingPlaquetteCoeff_translate]


def translatePlaquetteIndex (a : LatticeShift) (P : Finset GlobalIntegerPlaquette)
    (p : P) : translatePlaquettes a P :=
  ⟨translatePlaquetteEquiv a p.1, Finset.mem_map.mpr ⟨p.1, p.2, rfl⟩⟩

/-- Pullback of an assignment on a translated coordinate set. -/
def untranslateCurvatureAssignment (a : LatticeShift) (P : Finset GlobalIntegerPlaquette)
    (x : translatePlaquettes a P → ℤ) : P → ℤ :=
  fun p => x (translatePlaquetteIndex a P p)

theorem translatePlaquettes_mono (a : LatticeShift)
    {P₀ P₁ : Finset GlobalIntegerPlaquette} (hP : P₀ ⊆ P₁) :
    translatePlaquettes a P₀ ⊆ translatePlaquettes a P₁ := by
  intro q hq
  rcases Finset.mem_map.mp hq with ⟨p, hp, rfl⟩
  exact Finset.mem_map.mpr ⟨p, hP hp, rfl⟩

/-- Translation of a consistent projective curvature state. -/
structure CurvatureCylinderState where
  law : (P : Finset GlobalIntegerPlaquette) → PMF (P → ℤ)
  consistent : ∀ (P₀ P₁ : Finset GlobalIntegerPlaquette) (hP : P₀ ⊆ P₁),
    PMF.map (restrictCurvature hP) (law P₁) = law P₀

noncomputable def cubeStateToCylinderState {β : ℝ} {hβ : 0 < β}
    (L : CubeCurvatureLimitState β hβ) : CurvatureCylinderState where
  law := L.law
  consistent := L.consistent


theorem cubeCurvatureLimitState_coordinate_exp_bound
    {β : ℝ} (hβ : 0 < β) (L : CubeCurvatureLimitState β hβ)
    (P : Finset GlobalIntegerPlaquette) (p : P) (t : ℝ) :
    ∫ x, Real.exp (t * (x p : ℝ)) ∂ (L.law P).toMeasure ≤
      Real.exp (t ^ 2 * β / 2) := by
  classical
  let c : P → ℝ := fun q => if q = p then 1 else 0
  have hcoord (x : P → ℤ) :
      (∑ q : P, c q * (x q : ℝ)) = (x p : ℝ) := by
    simp [c]
  have hconv := cubeCurvatureLimitState_expLinear_integral_tendsto
    β hβ L P c t
  have hseqEq : (fun k =>
      ∫ x, Real.exp (t * (x p : ℝ)) ∂
        (cubeCurvaturePMFTotal (L.subsequence k) β hβ P).toMeasure) =
      (fun k =>
      ∫ x, Real.exp (t * ∑ q : P, c q * (x q : ℝ)) ∂
        (cubeCurvaturePMFTotal (L.subsequence k) β hβ P).toMeasure) := by
    funext k
    congr 1
    funext x
    rw [hcoord x]
  have hlimEq :
      ∫ x, Real.exp (t * (x p : ℝ)) ∂ (L.law P).toMeasure =
        ∫ x, Real.exp (t * ∑ q : P, c q * (x q : ℝ)) ∂
          (L.law P).toMeasure := by
    congr 1
    funext x
    rw [hcoord x]
  have hconv' : Tendsto
      (fun k => ∫ x, Real.exp (t * (x p : ℝ)) ∂
        (cubeCurvaturePMFTotal (L.subsequence k) β hβ P).toMeasure)
      atTop (𝓝 (∫ x, Real.exp (t * (x p : ℝ)) ∂ (L.law P).toMeasure)) := by
    rw [hseqEq, hlimEq]
    exact hconv
  have hbound : ∀ k : ℕ,
      (∫ x, Real.exp (t * (x p : ℝ)) ∂
        (cubeCurvaturePMFTotal (L.subsequence k) β hβ P).toMeasure) ≤
        Real.exp (t ^ 2 * β / 2) := by
    intro k
    exact cubeCurvaturePMFTotal_coordinate_exp_le
      (L.subsequence k) β t hβ P p
  exact le_of_tendsto_of_tendsto' hconv' tendsto_const_nhds
    hbound

/--
The finite-volume second-moment estimate passes to the limit by
truncation, then controls its first moment.
-/
theorem cubeCurvatureLimitState_coordinate_exp_integrable
    {β : ℝ} (hβ : 0 < β) (L : CubeCurvatureLimitState β hβ)
    (P : Finset GlobalIntegerPlaquette) (p : P) (t : ℝ) :
    Integrable (fun x : P → ℤ => Real.exp (t * (x p : ℝ)))
      (L.law P).toMeasure := by
  classical
  let pn : ℕ → PMF (P → ℤ) := fun k =>
    cubeCurvaturePMFTotal (L.subsequence k) β hβ P
  let law := L.law P
  let f : (P → ℤ) → ℝ := fun x => Real.exp (t * (x p : ℝ))
  let c : P → ℝ := fun q => if q = p then 1 else 0
  let C : ℝ := 1 + ∑ q : P,
    Real.exp (((2 * t * (Fintype.card P : ℝ) * c q) ^ 2 * β) / 2)
  have hcoord (x : P → ℤ) :
      (∑ q : P, c q * (x q : ℝ)) = (x p : ℝ) := by
    simp [c]
  have hpoint (x : P → ℤ) : Tendsto (fun k => (pn k x).toReal) atTop
      (𝓝 ((law x).toReal)) := by
    exact L.pointwise P x
  have hsq (k : ℕ) : Summable (fun x => (pn k x).toReal * (f x) ^ 2) := by
    refine (cubeCurvaturePMFTotal_exp_linear_secondMoment
      (L.subsequence k) β hβ P c t).1.congr ?_
    intro x
    simp only [pn, f]
    rw [hcoord x]
  have hsqBound (k : ℕ) : ∑' x, (pn k x).toReal * (f x) ^ 2 ≤ C := by
    simpa [C, f, c] using
      (cubeCurvaturePMFTotal_exp_linear_secondMoment
        (L.subsequence k) β hβ P c t).2
  have hlimSq := pmf_secondMoment_bound_of_pointwise pn law f C
    hpoint hsq hsqBound
  have hmass : Summable (fun x => (law x).toReal) := by
    apply ENNReal.summable_toReal
    rw [law.tsum_coe]
    exact ENNReal.one_ne_top
  have hYoung (x : P → ℤ) : f x ≤ 1 + (f x) ^ 2 := by
    nlinarith [sq_nonneg (f x - 1 / 2)]
  have hweight : Summable (fun x => (law x).toReal * f x) := by
    apply Summable.of_nonneg_of_le
      (fun x => mul_nonneg ENNReal.toReal_nonneg (Real.exp_pos _).le)
    · intro x
      have hm := ENNReal.toReal_nonneg (a := law x)
      have h := mul_le_mul_of_nonneg_left (hYoung x) hm
      simpa [mul_add] using h
    · exact hmass.add hlimSq.1
  have hnorm : Summable (fun x => (law x).toReal * ‖f x‖) := by
    refine hweight.congr ?_
    intro x
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact pmf_integrable_of_summable_norm hnorm

/--
The
bound is independent of the plaquette location.
-/
theorem cubeCurvatureLimitState_coordinate_tail
    {β : ℝ} (hβ : 0 < β) (L : CubeCurvatureLimitState β hβ)
    (P : Finset GlobalIntegerPlaquette) (p : P) (s R : ℝ) (hs : 0 < s) :
    (L.law P).toMeasure {x | R ≤ (x p : ℝ)} ≤
        ENNReal.ofReal (Real.exp (s ^ 2 * β / 2) * Real.exp (-s * R)) ∧
      (L.law P).toMeasure {x | R ≤ -(x p : ℝ)} ≤
        ENNReal.ofReal (Real.exp (s ^ 2 * β / 2) * Real.exp (-s * R)) := by
  let X : (P → ℤ) → ℝ := fun x => (x p : ℝ)
  have hX : Measurable X := by
    change Measurable (fun x : P → ℤ => (x p : ℝ))
    fun_prop
  have hXneg : Measurable (fun x : P → ℤ => -X x) := hX.neg
  have hIntPos := cubeCurvatureLimitState_coordinate_exp_integrable hβ L P p s
  have hMomPos := cubeCurvatureLimitState_coordinate_exp_bound hβ L P p s
  have htailPos := pmf_exp_tail_bound (L.law P) X s R
    (Real.exp (s ^ 2 * β / 2)) hs hX hIntPos hMomPos
  have hIntNeg0 := cubeCurvatureLimitState_coordinate_exp_integrable hβ L P p (-s)
  have hIntNeg : Integrable (fun x => Real.exp (s * -X x)) (L.law P).toMeasure := by
    have heq : (fun x : P → ℤ => Real.exp (s * -X x)) =
        (fun x => Real.exp ((-s) * (x p : ℝ))) := by
      funext x
      congr 1
      dsimp [X]
      ring
    rw [heq]
    exact hIntNeg0
  have hMomNeg0 := cubeCurvatureLimitState_coordinate_exp_bound hβ L P p (-s)
  have hMomNeg :
      ∫ x, Real.exp (s * -X x) ∂(L.law P).toMeasure ≤
        Real.exp (s ^ 2 * β / 2) := by
    have heq : (fun x : P → ℤ => Real.exp (s * -X x)) =
        (fun x => Real.exp ((-s) * (x p : ℝ))) := by
      funext x
      congr 1
      dsimp [X]
      ring
    rw [heq]
    simpa [neg_sq] using hMomNeg0
  have htailNeg := pmf_exp_tail_bound (L.law P) (fun x => -X x) s R
    (Real.exp (s ^ 2 * β / 2)) hs hXneg hIntNeg hMomNeg
  exact ⟨htailPos, htailNeg⟩

/-- A single coordinate box gives tightness uniformly over all finite
plaquette sets of a fixed cardinality. -/
theorem cubeCurvatureLimitState_uniform_box_tight
    {β : ℝ} (hβ : 0 < β) (L : CubeCurvatureLimitState β hβ)
    (P : Finset GlobalIntegerPlaquette) (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℕ, ∀ P' : Finset GlobalIntegerPlaquette,
      Fintype.card P' = Fintype.card P →
      1 - ε ≤ ∑ x ∈ (curvatureCoordinateBox_finite (P := P') K).toFinset,
        ((L.law P') x).toReal := by
  classical
  let C : ℝ := Real.exp (β / 2)
  let A : ℝ := (Fintype.card (P × Bool) : ℝ) * C
  have hA : 0 ≤ A := by positivity
  have hsum : Tendsto (fun k : ℕ => (k : ℝ) + 1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have harg : Tendsto (fun k : ℕ => -((k : ℝ) + 1)) atTop atBot :=
    tendsto_neg_atBot_iff.mpr hsum
  have hdecay : Tendsto (fun k : ℕ => Real.exp (-((k : ℝ) + 1))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp harg
  have hδ : 0 < ε / (A + 1) := by positivity
  have hev : ∀ᶠ k : ℕ in atTop,
      Real.exp (-((k : ℝ) + 1)) < ε / (A + 1) :=
    hdecay.eventually (Iio_mem_nhds hδ)
  obtain ⟨K, hK⟩ := Filter.Eventually.exists hev
  have hAexp : A * Real.exp (-((K : ℝ) + 1)) < ε := by
    calc
      A * Real.exp (-((K : ℝ) + 1)) ≤
          (A + 1) * Real.exp (-((K : ℝ) + 1)) := by
            exact mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
      _ < (ε / (A + 1)) * (A + 1) := by
        calc
          _ = Real.exp (-((K : ℝ) + 1)) * (A + 1) := by ring
          _ < (ε / (A + 1)) * (A + 1) :=
            mul_lt_mul_of_pos_right hK (show 0 < A + 1 by linarith)
      _ = ε := by field_simp
  refine ⟨K, ?_⟩
  intro P' hcard
  let box := curvatureCoordinateBox (P := P') K
  let S := (curvatureCoordinateBox_finite (P := P') K).toFinset
  have hS : (S : Set (P' → ℤ)) = box :=
    (curvatureCoordinateBox_finite (P := P') K).coe_toFinset
  have hBadCover (x : P' → ℤ) (hx : x ∈ boxᶜ) :
      x ∈ ⋃ i : P' × Bool, curvatureCoordinateBad K i := by
    have hnot : ∃ p : P',
        x p < -(K : ℤ) ∨ (K : ℤ) < x p := by
      by_contra h
      push Not at h
      apply hx
      intro p
      rw [Set.mem_Icc]
      exact ⟨h p |>.1, h p |>.2⟩
    rcases hnot with ⟨p, hlow | hhigh⟩
    · have hi : ((K + 1 : ℕ) : ℤ) ≤ -x p := by omega
      have hir : ((K + 1 : ℕ) : ℝ) ≤ -(x p : ℝ) := by exact_mod_cast hi
      refine Set.mem_iUnion.mpr ⟨(p, false), ?_⟩
      simpa [curvatureCoordinateBad] using hir
    · have hi : ((K + 1 : ℕ) : ℤ) ≤ x p := by omega
      have hir : ((K + 1 : ℕ) : ℝ) ≤ (x p : ℝ) := by exact_mod_cast hi
      refine Set.mem_iUnion.mpr ⟨(p, true), ?_⟩
      simpa [curvatureCoordinateBad] using hir
  have htail (i : P' × Bool) :
      (L.law P').toMeasure (curvatureCoordinateBad K i) ≤
        ENNReal.ofReal (C * Real.exp (-((K : ℝ) + 1))) := by
    rcases i with ⟨p, b⟩
    cases b
    · simpa [curvatureCoordinateBad, C] using
        (cubeCurvatureLimitState_coordinate_tail hβ L P' p 1
          ((K : ℝ) + 1) one_pos).2
    · simpa [curvatureCoordinateBad, C] using
        (cubeCurvatureLimitState_coordinate_tail hβ L P' p 1
          ((K : ℝ) + 1) one_pos).1
  have hunion : (L.law P').toMeasure
      (⋃ i : P' × Bool, curvatureCoordinateBad K i) ≤
        ENNReal.ofReal (A * Real.exp (-((K : ℝ) + 1))) := by
    calc
      _ ≤ ∑' i : P' × Bool,
          (L.law P').toMeasure (curvatureCoordinateBad K i) :=
        MeasureTheory.measure_iUnion_le _
      _ = ∑ i : P' × Bool,
          (L.law P').toMeasure (curvatureCoordinateBad K i) := by
        rw [tsum_fintype]
      _ ≤ ∑ i : P' × Bool,
          ENNReal.ofReal (C * Real.exp (-((K : ℝ) + 1))) :=
        Finset.sum_le_sum fun i hi => htail i
      _ = ENNReal.ofReal (A * Real.exp (-((K : ℝ) + 1))) := by
        rw [← ENNReal.ofReal_sum_of_nonneg]
        · congr 1
          simp [A, C, Finset.sum_const, nsmul_eq_mul, Fintype.card_prod, hcard]
          ring
        · intro i hi
          positivity
  have htailBox : (L.law P').toMeasure boxᶜ ≤ ENNReal.ofReal ε := by
    calc
      _ ≤ (L.law P').toMeasure
          (⋃ i : P' × Bool, curvatureCoordinateBad K i) :=
        MeasureTheory.measure_mono hBadCover
      _ ≤ ENNReal.ofReal (A * Real.exp (-((K : ℝ) + 1))) := hunion
      _ ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal hAexp.le
  have hprob : (L.law P').toMeasure box ≤ 1 := by
    calc
      _ ≤ (L.law P').toMeasure Set.univ := MeasureTheory.measure_mono (Set.subset_univ _)
      _ = 1 := by simp
  have hnotTop : (L.law P').toMeasure box ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt hprob ENNReal.one_lt_top)
  have hcompl : (L.law P').toMeasure boxᶜ =
      1 - (L.law P').toMeasure box := by
    rw [MeasureTheory.measure_compl (curvatureCoordinateBox_finite
      (P := P') K).measurableSet hnotTop]
    simp [box]
  have hcomplTop : (L.law P').toMeasure boxᶜ ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt htailBox ENNReal.ofReal_lt_top)
  have hcomplReal : ((L.law P').toMeasure boxᶜ).toReal =
      1 - ((L.law P').toMeasure box).toReal := by
    rw [hcompl, ENNReal.toReal_sub_of_le hprob ENNReal.one_ne_top]
    simp [ENNReal.toReal_one]
  have hcomplRealLe : ((L.law P').toMeasure boxᶜ).toReal ≤ ε := by
    have h := (ENNReal.toReal_le_toReal hcomplTop ENNReal.ofReal_ne_top).2 htailBox
    simpa [ENNReal.toReal_ofReal hε.le] using h
  have hmass : 1 - ε ≤ ((L.law P').toMeasure box).toReal := by
    have hle : 1 - ((L.law P').toMeasure box).toReal ≤ ε := by
      rw [← hcomplReal]
      exact hcomplRealLe
    linarith
  have hsumReal : ((L.law P').toMeasure box).toReal =
      ∑ x ∈ S, ((L.law P') x).toReal := by
    rw [← hS, PMF.toMeasure_apply_finset]
    rw [ENNReal.toReal_sum (fun x hx => (L.law P').apply_ne_top x)]
  rw [← hsumReal]
  exact hmass

private theorem pmf_toReal_measure_finset
    {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    [Countable α] [DecidableEq α] (p : PMF α) (S : Finset α) :
    (p.toMeasure (S : Set α)).toReal = ∑ x ∈ S, (p x).toReal := by
  rw [PMF.toMeasure_apply_finset, ENNReal.toReal_sum
    (fun x hx => p.apply_ne_top x)]

theorem untranslateCurvatureAssignment_box_preimage
    (a : LatticeShift) (P : Finset GlobalIntegerPlaquette) (K : ℕ) :
    untranslateCurvatureAssignment a P ⁻¹'
        curvatureCoordinateBox (P := P) K =
      curvatureCoordinateBox (P := translatePlaquettes a P) K := by
  ext x
  simp only [Set.mem_preimage, curvatureCoordinateBox]
  constructor
  · intro hx q'
    rcases Finset.mem_map.mp q'.2 with ⟨q, hq, hq'⟩
    have hindex : translatePlaquetteIndex a P ⟨q, hq⟩ = q' := by
      apply Subtype.ext
      exact hq'
    have hqbox := hx ⟨q, hq⟩
    simpa [untranslateCurvatureAssignment, hindex] using hqbox
  · intro hx q
    have hqbox := hx (translatePlaquetteIndex a P q)
    simpa [untranslateCurvatureAssignment] using hqbox

theorem translatePlaquettes_card (a : LatticeShift)
    (P : Finset GlobalIntegerPlaquette) :
    Fintype.card (translatePlaquettes a P) = Fintype.card P := by
  classical
  rw [Fintype.card_coe, Fintype.card_coe, translatePlaquettes, Finset.card_map]

noncomputable def translateCylinderLaw (ν : CurvatureCylinderState) (a : LatticeShift)
    (P : Finset GlobalIntegerPlaquette) : PMF (P → ℤ) :=
  (ν.law (translatePlaquettes a P)).map (untranslateCurvatureAssignment a P)

theorem translateCylinderLaw_box_measure
    (ν : CurvatureCylinderState) (a : LatticeShift)
    (P : Finset GlobalIntegerPlaquette) (K : ℕ) :
    (translateCylinderLaw ν a P).toMeasure
        (curvatureCoordinateBox (P := P) K) =
      (ν.law (translatePlaquettes a P)).toMeasure
        (curvatureCoordinateBox (P := translatePlaquettes a P) K) := by
  classical
  rw [translateCylinderLaw, ← PMF.toMeasure_map _ _ (by fun_prop :
    Measurable (untranslateCurvatureAssignment a P))]
  rw [MeasureTheory.Measure.map_apply (by fun_prop :
    Measurable (untranslateCurvatureAssignment a P))
    (curvatureCoordinateBox_finite (P := P) K).measurableSet]
  rw [untranslateCurvatureAssignment_box_preimage]

theorem translateCylinderLaw_consistent (ν : CurvatureCylinderState) (a : LatticeShift)
    (P₀ P₁ : Finset GlobalIntegerPlaquette) (hP : P₀ ⊆ P₁) :
    PMF.map (restrictCurvature hP) (translateCylinderLaw ν a P₁) =
      translateCylinderLaw ν a P₀ := by
  classical
  let hQ := translatePlaquettes_mono a hP
  have hfun : restrictCurvature hP ∘ untranslateCurvatureAssignment a P₁ =
      untranslateCurvatureAssignment a P₀ ∘ restrictCurvature hQ := by
    funext x p
    rfl
  change PMF.map (restrictCurvature hP)
      (PMF.map (untranslateCurvatureAssignment a P₁)
        (ν.law (translatePlaquettes a P₁))) = _
  rw [PMF.map_comp, hfun, ← PMF.map_comp, ν.consistent _ _ hQ]
  rfl

noncomputable def translateCylinderState (ν : CurvatureCylinderState) (a : LatticeShift) :
    CurvatureCylinderState where
  law := fun P => translateCylinderLaw ν a P
  consistent := translateCylinderLaw_consistent ν a

theorem translateCylinderLaw_add (ν : CurvatureCylinderState) (a b : LatticeShift)
    (P : Finset GlobalIntegerPlaquette) :
    translateCylinderLaw (translateCylinderState ν b) a P =
      translateCylinderLaw ν (b + a) P := by
  classical
  let S := translatePlaquettes b (translatePlaquettes a P)
  let T := translatePlaquettes (b + a) P
  let U := S ∪ T
  have hSU : S ⊆ U := Finset.subset_union_left
  have hTU : T ⊆ U := Finset.subset_union_right
  let f : (S → ℤ) → (P → ℤ) :=
    untranslateCurvatureAssignment a P ∘ untranslateCurvatureAssignment b (translatePlaquettes a P)
  let g : (T → ℤ) → (P → ℤ) := untranslateCurvatureAssignment (b + a) P
  let fU : (U → ℤ) → (P → ℤ) := f ∘ restrictCurvature hSU
  let gU : (U → ℤ) → (P → ℤ) := g ∘ restrictCurvature hTU
  have hleft : PMF.map f (ν.law S) = PMF.map fU (ν.law U) := by
    rw [← ν.consistent S U hSU, PMF.map_comp]
  have hright : PMF.map g (ν.law T) = PMF.map gU (ν.law U) := by
    rw [← ν.consistent T U hTU, PMF.map_comp]
  have hfun : fU = gU := by
    funext x p
    change x ⟨translatePlaquetteEquiv b (translatePlaquetteEquiv a p), _⟩ =
      x ⟨translatePlaquetteEquiv (b + a) p, _⟩
    congr 1
    apply Subtype.ext
    exact translatePlaquetteEquiv_add b a p
  change PMF.map (untranslateCurvatureAssignment a P)
      (PMF.map (untranslateCurvatureAssignment b (translatePlaquettes a P))
        (ν.law S)) = PMF.map g (ν.law T)
  rw [PMF.map_comp]
  change PMF.map f (ν.law S) = PMF.map g (ν.law T)
  rw [hleft, hright, hfun]


def latticeShiftBoxSet (n : ℕ) : Set LatticeShift :=
  {a | ∀ i, a i ∈ Set.Icc (-(n : ℤ)) (n : ℤ)}

theorem latticeShiftBoxSet_finite (n : ℕ) : (latticeShiftBoxSet n).Finite :=
  Set.Finite.pi' (fun _ : Fin 4 => Set.finite_Icc (-(n : ℤ)) (n : ℤ))

noncomputable def latticeShiftBox (n : ℕ) : Finset LatticeShift :=
  (latticeShiftBoxSet_finite n).toFinset

noncomputable def latticeShiftBoxProduct (n : ℕ) : Finset LatticeShift :=
  Fintype.piFinset fun _ : Fin 4 => Finset.Icc (-(n : ℤ)) (n : ℤ)

theorem latticeShiftBox_eq_product (n : ℕ) :
    latticeShiftBox n = latticeShiftBoxProduct n := by
  classical
  ext a
  simp [latticeShiftBox, latticeShiftBoxSet, latticeShiftBoxProduct]

theorem latticeShiftBox_card (n : ℕ) :
    (latticeShiftBox n).card = (2 * n + 1) ^ 4 := by
  have hinterval : (Finset.Icc (-(n : ℤ)) (n : ℤ)).card = 2 * n + 1 := by
    rw [Int.card_Icc]
    norm_num
    omega
  rw [latticeShiftBox_eq_product, latticeShiftBoxProduct,
    Fintype.card_piFinset]
  simp [hinterval]

def translateLatticeShift (b : LatticeShift) :
    LatticeShift ≃ LatticeShift := Equiv.addRight b

noncomputable def translatedLatticeShiftBox (b : LatticeShift) (n : ℕ) :
    Finset LatticeShift :=
  (latticeShiftBox n).map (translateLatticeShift b).toEmbedding

noncomputable def latticeShiftTranslatedProduct (b : LatticeShift) (n : ℕ) :
    Finset LatticeShift :=
  Fintype.piFinset fun i : Fin 4 =>
    Finset.Icc (-(n : ℤ) + b i) ((n : ℤ) + b i)

theorem translatedLatticeShiftBox_eq_product (b : LatticeShift) (n : ℕ) :
    translatedLatticeShiftBox b n = latticeShiftTranslatedProduct b n := by
  classical
  ext x
  simp only [translatedLatticeShiftBox, Finset.mem_map,
    latticeShiftBox_eq_product, latticeShiftBoxProduct,
    latticeShiftTranslatedProduct, Fintype.mem_piFinset]
  constructor
  · rintro ⟨y, hy, hxy⟩ i
    have hyi := hy i
    have hxi : y i + b i = x i := by
      simpa [translateLatticeShift, Equiv.coe_addRight] using congrFun hxy i
    rw [Finset.mem_Icc] at hyi ⊢
    omega
  · intro hx
    refine ⟨fun i => x i - b i, ?_, ?_⟩
    · intro i
      have hi := hx i
      rw [Finset.mem_Icc] at hi ⊢
      change -(n : ℤ) ≤ x i - b i ∧ x i - b i ≤ n
      omega
    · funext i
      simp [translateLatticeShift, Equiv.coe_addRight]

def latticeShiftUnit (i : Fin 4) : LatticeShift := Pi.single i (1 : ℤ)

noncomputable def latticeShiftUnitIntersectionProduct (n : ℕ) (i : Fin 4) :
    Finset LatticeShift :=
  Fintype.piFinset fun j : Fin 4 =>
    if j = i then Finset.Icc (-(n : ℤ) + 1) (n : ℤ)
    else Finset.Icc (-(n : ℤ)) (n : ℤ)

theorem latticeShiftBox_inter_unit_translate (n : ℕ) (i : Fin 4) :
    latticeShiftBox n ∩ translatedLatticeShiftBox (latticeShiftUnit i) n =
      latticeShiftUnitIntersectionProduct n i := by
  classical
  ext x
  simp only [Finset.mem_inter, latticeShiftBox_eq_product,
    latticeShiftBoxProduct, translatedLatticeShiftBox_eq_product,
    latticeShiftUnitIntersectionProduct]
  constructor
  · rintro ⟨hx₁, hx₂⟩
    apply Fintype.mem_piFinset.mpr
    intro j
    have h₁ := Fintype.mem_piFinset.mp hx₁ j
    have h₂ := Fintype.mem_piFinset.mp hx₂ j
    by_cases hji : j = i
    · subst j
      have h₂' : x i ∈ Finset.Icc (-(n : ℤ) + 1) ((n : ℤ) + 1) := by
        simpa [latticeShiftUnit] using h₂
      have hgoal : x i ∈ Finset.Icc (-(n : ℤ) + 1) (n : ℤ) := by
        rw [Finset.mem_Icc] at h₁ h₂' ⊢
        omega
      simpa using hgoal
    · simp [latticeShiftUnit, hji] at h₂
      simpa [hji] using h₁
  · intro hx
    constructor
    · apply Fintype.mem_piFinset.mpr
      intro j
      have hj := Fintype.mem_piFinset.mp hx j
      by_cases hji : j = i
      · subst j
        have hj' : x i ∈ Finset.Icc (-(n : ℤ) + 1) (n : ℤ) := by
          simpa using hj
        have : x i ∈ Finset.Icc (-(n : ℤ)) (n : ℤ) := by
          rw [Finset.mem_Icc] at hj' ⊢
          omega
        simpa using this
      · simpa [hji] using hj
    · apply Fintype.mem_piFinset.mpr
      intro j
      have hj := Fintype.mem_piFinset.mp hx j
      by_cases hji : j = i
      · subst j
        have hj' : x i ∈ Finset.Icc (-(n : ℤ) + 1) (n : ℤ) := by
          simpa using hj
        have : x i ∈ Finset.Icc (-(n : ℤ) + 1) ((n : ℤ) + 1) := by
          rw [Finset.mem_Icc] at hj' ⊢
          omega
        simpa [latticeShiftUnit] using this
      · simpa [hji, latticeShiftUnit] using hj

theorem latticeShiftBox_inter_unit_translate_card (n : ℕ) (i : Fin 4) :
    (latticeShiftBox n ∩ translatedLatticeShiftBox (latticeShiftUnit i) n).card =
      (2 * n) * (2 * n + 1) ^ 3 := by
  rw [latticeShiftBox_inter_unit_translate]
  rw [latticeShiftUnitIntersectionProduct, Fintype.card_piFinset]
  have hshort : (Finset.Icc (-(n : ℤ) + 1) (n : ℤ)).card = 2 * n := by
    rw [Int.card_Icc]
    norm_num
    omega
  have hlong : (Finset.Icc (-(n : ℤ)) (n : ℤ)).card = 2 * n + 1 := by
    rw [Int.card_Icc]
    norm_num
    omega
  fin_cases i <;>
    simp [Fin.prod_univ_succ, hshort, hlong] <;> ring_nf


private theorem abs_sum_sub_sum_le_sdiff_card
    {α : Type*} [DecidableEq α] (A B : Finset α) (g : α → ℝ)
    (hg₀ : ∀ x, 0 ≤ g x) (hg₁ : ∀ x, g x ≤ 1) :
    |(∑ x ∈ A, g x) - ∑ x ∈ B, g x| ≤ ((A \ B).card + (B \ A).card : ℝ) := by
  have hA : (∑ x ∈ A, g x) =
      (∑ x ∈ A ∩ B, g x) + ∑ x ∈ A \ B, g x := by
    rw [← Finset.sum_inter_add_sum_sdiff A B g]
  have hB : (∑ x ∈ B, g x) =
      (∑ x ∈ A ∩ B, g x) + ∑ x ∈ B \ A, g x := by
    rw [← Finset.sum_inter_add_sum_sdiff B A g, Finset.inter_comm]
  have hAlo : 0 ≤ ∑ x ∈ A \ B, g x := Finset.sum_nonneg fun x hx => hg₀ x
  have hAhi : (∑ x ∈ A \ B, g x) ≤ ((A \ B).card : ℝ) := by
    calc
      _ ≤ ∑ _x ∈ A \ B, (1 : ℝ) := Finset.sum_le_sum fun x hx => hg₁ x
      _ = ((A \ B).card : ℝ) := by simp
  have hBlo : 0 ≤ ∑ x ∈ B \ A, g x := Finset.sum_nonneg fun x hx => hg₀ x
  have hBhi : (∑ x ∈ B \ A, g x) ≤ ((B \ A).card : ℝ) := by
    calc
      _ ≤ ∑ _x ∈ B \ A, (1 : ℝ) := Finset.sum_le_sum fun x hx => hg₁ x
      _ = ((B \ A).card : ℝ) := by simp
  rw [hA, hB]
  simp only [add_sub_add_left_eq_sub]
  have hpos : -((B \ A).card : ℝ) ≤
      (∑ x ∈ A \ B, g x) - ∑ x ∈ B \ A, g x := by linarith
  have hneg : (∑ x ∈ A \ B, g x) - ∑ x ∈ B \ A, g x ≤
      ((A \ B).card : ℝ) := by linarith
  rw [abs_le]
  constructor <;> linarith

private theorem unit_translate_symmDiff_card (n : ℕ) (i : Fin 4) :
    (latticeShiftBox n \ translatedLatticeShiftBox (latticeShiftUnit i) n).card +
      (translatedLatticeShiftBox (latticeShiftUnit i) n \ latticeShiftBox n).card =
        2 * (2 * n + 1) ^ 3 := by
  have hA : (latticeShiftBox n).card = (2 * n + 1) ^ 4 := latticeShiftBox_card n
  have hB : (translatedLatticeShiftBox (latticeShiftUnit i) n).card =
      (2 * n + 1) ^ 4 := by
    rw [translatedLatticeShiftBox, Finset.card_map, hA]
  have hI := latticeShiftBox_inter_unit_translate_card n i
  have hAsub : (latticeShiftBox n \ translatedLatticeShiftBox (latticeShiftUnit i) n).card =
      (2 * n + 1) ^ 3 := by
    rw [Finset.card_sdiff, hA, Finset.inter_comm, hI]
    have hfactor : (2 * n + 1) ^ 4 =
        2 * n * (2 * n + 1) ^ 3 + (2 * n + 1) ^ 3 := by ring
    omega
  have hBsub : (translatedLatticeShiftBox (latticeShiftUnit i) n \ latticeShiftBox n).card =
      (2 * n + 1) ^ 3 := by
    rw [Finset.card_sdiff, hB, hI]
    have hfactor : (2 * n + 1) ^ 4 =
        2 * n * (2 * n + 1) ^ 3 + (2 * n + 1) ^ 3 := by ring
    omega
  rw [hAsub, hBsub]
  ring

private theorem sum_latticeShiftBox_translate (n : ℕ) (b : LatticeShift)
    (g : LatticeShift → ℝ) :
    (∑ a ∈ latticeShiftBox n, g (a + b)) =
      ∑ a ∈ translatedLatticeShiftBox b n, g a := by
  classical
  rw [translatedLatticeShiftBox]
  simp [Finset.sum_map, translateLatticeShift, Equiv.coe_addRight, add_comm]

private theorem latticeShiftBox_index_card (n : ℕ) :
    Fintype.card {a : LatticeShift // a ∈ latticeShiftBox n} =
      (2 * n + 1) ^ 4 := by
  simpa using latticeShiftBox_card n

theorem zero_mem_latticeShiftBox (n : ℕ) : (0 : LatticeShift) ∈ latticeShiftBox n := by
  rw [latticeShiftBox, Set.Finite.mem_toFinset (latticeShiftBoxSet_finite n)]
  intro i
  simp

/-- The uniform probability distribution on the finite Følner box of shifts. -/
noncomputable def latticeShiftUniform (n : ℕ) : PMF LatticeShift := by
  classical
  letI := (latticeShiftBoxSet_finite n).to_subtype
  let S := {a : LatticeShift // a ∈ latticeShiftBox n}
  let m := Fintype.card S
  have hm : 0 < m := Fintype.card_pos_iff.mpr ⟨⟨0, zero_mem_latticeShiftBox n⟩⟩
  let p : PMF S := PMF.ofFintype (fun _ => ((m : ℕ) : ENNReal)⁻¹) (by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact ENNReal.mul_inv_cancel (by exact_mod_cast (Nat.ne_of_gt hm))
      (ENNReal.natCast_ne_top _))
  exact p.map Subtype.val

theorem latticeShiftUniform_apply (n : ℕ) (a : LatticeShift) :
    latticeShiftUniform n a =
      if a ∈ latticeShiftBox n then
        ((Fintype.card {a : LatticeShift // a ∈ latticeShiftBox n} : ℕ) : ENNReal)⁻¹
      else 0 := by
  classical
  simp [latticeShiftUniform, PMF.map_apply, PMF.ofFintype_apply]
  by_cases ha : a ∈ latticeShiftBox n
  · let x : {z : LatticeShift // z ∈ latticeShiftBox n} := ⟨a, ha⟩
    have hx : x ∈ (latticeShiftBox n).attach := Finset.mem_attach _ _
    have hsum :
        (∑ z ∈ (latticeShiftBox n).attach,
          @ite ENNReal (a = (z : LatticeShift))
            (Classical.propDecidable (a = (z : LatticeShift)))
            ((latticeShiftBox n).card : ENNReal)⁻¹ 0) =
          ((latticeShiftBox n).card : ENNReal)⁻¹ := by
      calc
        _ = (@ite ENNReal (a = (x : LatticeShift))
            (Classical.propDecidable (a = (x : LatticeShift)))
            ((latticeShiftBox n).card : ENNReal)⁻¹ 0) := by
          apply Finset.sum_eq_single x
          · intro z hz hzx
            have hne : a ≠ (z : LatticeShift) := by
              intro h
              apply hzx
              exact Subtype.ext h.symm
            simp [hne]
          · intro hnot
            exact (hnot hx).elim
        _ = _ := by simp [x]
    convert hsum using 1
    · simp [ha]
  · have hsum :
        (∑ z ∈ (latticeShiftBox n).attach,
          @ite ENNReal (a = (z : LatticeShift))
            (Classical.propDecidable (a = (z : LatticeShift)))
            ((latticeShiftBox n).card : ENNReal)⁻¹ 0) = 0 := by
      apply Finset.sum_eq_zero
      intro z hz
      have hne : a ≠ (z : LatticeShift) := by
        intro h
        exact ha (h ▸ z.2)
      simp [hne]
    convert hsum using 1
    · simp [ha]

/-- Finite Følner average of a family of probability laws. -/
noncomputable def finiteShiftAverage {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] [Countable α] [DecidableEq α]
    (n : ℕ) (f : LatticeShift → PMF α) : PMF α :=
  PMF.bind (latticeShiftUniform n) f

theorem finiteShiftAverage_apply {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] [Countable α] [DecidableEq α]
    (n : ℕ) (f : LatticeShift → PMF α) (x : α) :
    finiteShiftAverage n f x =
      ∑ a ∈ latticeShiftBox n,
        (((Fintype.card {a : LatticeShift // a ∈ latticeShiftBox n} : ℕ) : ENNReal)⁻¹) *
          f a x := by
  classical
  let w : ENNReal :=
    ((Fintype.card {a : LatticeShift // a ∈ latticeShiftBox n} : ℕ) : ENNReal)⁻¹
  have hw (a : LatticeShift) : latticeShiftUniform n a =
      if a ∈ latticeShiftBox n then w else 0 := by
    simpa [w] using latticeShiftUniform_apply n a
  calc
    finiteShiftAverage n f x =
        ∑' a, latticeShiftUniform n a * f a x := by
          rw [finiteShiftAverage, PMF.bind_apply]
    _ = ∑' a, (if a ∈ latticeShiftBox n then w else 0) * f a x := by
          congr 1
          funext a
          rw [hw]
    _ = ∑ a ∈ latticeShiftBox n,
        (if a ∈ latticeShiftBox n then w else 0) * f a x := by
          apply tsum_eq_sum
          intro a ha
          simp [ha]
    _ = ∑ a ∈ latticeShiftBox n, w * f a x := by
          apply Finset.sum_congr rfl
          intro a ha
          simp [ha]

theorem finiteShiftAverage_apply_toReal {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] [Countable α] [DecidableEq α]
    (n : ℕ) (f : LatticeShift → PMF α) (x : α) :
    (finiteShiftAverage n f x).toReal =
      (Fintype.card {a : LatticeShift // a ∈ latticeShiftBox n} : ℝ)⁻¹ *
        ∑ a ∈ latticeShiftBox n, (f a x).toReal := by
  classical
  rw [finiteShiftAverage_apply]
  rw [ENNReal.toReal_sum]
  · simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast]
    rw [← Finset.mul_sum]
  · intro a ha
    apply ENNReal.mul_ne_top
    · apply ENNReal.inv_ne_top.mpr
      have hcard : 0 < Fintype.card {a : LatticeShift // a ∈ latticeShiftBox n} :=
        Fintype.card_pos_iff.mpr ⟨⟨0, zero_mem_latticeShiftBox n⟩⟩
      exact_mod_cast (Nat.ne_of_gt hcard)
    · exact (f a).apply_ne_top x

private noncomputable def finiteShiftAverageWeight (n : ℕ) : ENNReal :=
  ((Fintype.card {a : LatticeShift // a ∈ latticeShiftBox n} : ℕ) : ENNReal)⁻¹

private theorem finiteShiftAverageWeight_ne_zero (n : ℕ) :
    finiteShiftAverageWeight n ≠ 0 := by
  unfold finiteShiftAverageWeight
  apply ENNReal.inv_ne_zero.mpr
  exact ENNReal.natCast_ne_top _

private theorem finiteShiftAverageWeight_ne_top (n : ℕ) :
    finiteShiftAverageWeight n ≠ ⊤ := by
  unfold finiteShiftAverageWeight
  apply ENNReal.inv_ne_top.mpr
  have hcard : 0 < Fintype.card {a : LatticeShift // a ∈ latticeShiftBox n} :=
    Fintype.card_pos_iff.mpr ⟨⟨0, zero_mem_latticeShiftBox n⟩⟩
  exact_mod_cast (Nat.ne_of_gt hcard)

/-- The law of a finite Følner average is the corresponding finite weighted
sum of its component measures. -/
private theorem finiteShiftAverage_toMeasure_eq
    {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    [Countable α] [DecidableEq α]
    (n : ℕ) (f : LatticeShift → PMF α) :
    (finiteShiftAverage n f).toMeasure =
      ∑ a ∈ latticeShiftBox n,
        finiteShiftAverageWeight n • (f a).toMeasure := by
  classical
  apply MeasureTheory.Measure.ext
  intro s hs
  rw [finiteShiftAverage, PMF.toMeasure_bind_apply _ _ _ hs]
  let w := finiteShiftAverageWeight n
  have hterm (a : LatticeShift) :
      latticeShiftUniform n a * (f a).toMeasure s =
        (if a ∈ latticeShiftBox n then w else 0) * (f a).toMeasure s := by
    rw [latticeShiftUniform_apply]
    simp [w, finiteShiftAverageWeight]
  calc
    (∑' a : LatticeShift,
        latticeShiftUniform n a * (f a).toMeasure s) =
      ∑' a : LatticeShift,
        (if a ∈ latticeShiftBox n then w else 0) * (f a).toMeasure s := by
          apply tsum_congr
          intro a
          exact hterm a
    _ = ∑ a ∈ latticeShiftBox n,
        (if a ∈ latticeShiftBox n then w else 0) * (f a).toMeasure s := by
          apply tsum_eq_sum
          intro a ha
          simp [ha]
    _ = ∑ a ∈ latticeShiftBox n,
        finiteShiftAverageWeight n * (f a).toMeasure s := by
          apply Finset.sum_congr rfl
          intro a ha
          simp [ha, w]
  rw [MeasureTheory.Measure.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro a ha
  rw [MeasureTheory.Measure.smul_apply, smul_eq_mul]

/-- Integrals against a finite shift average are the arithmetic averages of
the component integrals. -/
private theorem finiteShiftAverage_integral
    {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    [Countable α] [DecidableEq α]
    (n : ℕ) (f : LatticeShift → PMF α) (g : α → ℝ)
    (hfi : ∀ a, Integrable g (f a).toMeasure) :
    Integrable g (finiteShiftAverage n f).toMeasure ∧
      ∫ x, g x ∂(finiteShiftAverage n f).toMeasure =
        (Fintype.card {a : LatticeShift // a ∈ latticeShiftBox n} : ℝ)⁻¹ *
          ∑ a ∈ latticeShiftBox n, ∫ x, g x ∂(f a).toMeasure := by
  classical
  rw [finiteShiftAverage_toMeasure_eq]
  have hsumInt : Integrable g
      (∑ a ∈ latticeShiftBox n,
        finiteShiftAverageWeight n • (f a).toMeasure) := by
    rw [MeasureTheory.integrable_finsetSum_measure]
    intro a ha
    rw [MeasureTheory.integrable_smul_measure
      (finiteShiftAverageWeight_ne_zero n) (finiteShiftAverageWeight_ne_top n)]
    exact hfi a
  constructor
  · exact hsumInt
  · rw [MeasureTheory.integral_finsetSum_measure]
    · simp only [MeasureTheory.integral_smul_measure, smul_eq_mul]
      simp [finiteShiftAverageWeight, ENNReal.toReal_inv,
        ENNReal.toReal_natCast, ← Finset.mul_sum]
    · intro a ha
      rw [MeasureTheory.integrable_smul_measure
        (finiteShiftAverageWeight_ne_zero n) (finiteShiftAverageWeight_ne_top n)]
      exact hfi a

private theorem finiteShiftAverage_translate_unit_error
    {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    [Countable α] [DecidableEq α]
    (n : ℕ) (f : LatticeShift → PMF α) (x : α) (i : Fin 4) :
    |(finiteShiftAverage n (fun a => f (a + latticeShiftUnit i)) x).toReal -
        (finiteShiftAverage n f x).toReal| ≤ 2 / (2 * n + 1 : ℝ) := by
  classical
  let B := latticeShiftBox n
  let C := translatedLatticeShiftBox (latticeShiftUnit i) n
  let g : LatticeShift → ℝ := fun a => (f a x).toReal
  have hg₀ (a : LatticeShift) : 0 ≤ g a := ENNReal.toReal_nonneg
  have hg₁ (a : LatticeShift) : g a ≤ 1 := by
    dsimp [g]
    rw [← ENNReal.toReal_one]
    exact ENNReal.toReal_mono (by simp) (PMF.coe_le_one (f a) x)
  have hsum := abs_sum_sub_sum_le_sdiff_card B C g hg₀ hg₁
  have hsumMap : (∑ a ∈ B, g (a + latticeShiftUnit i)) =
      ∑ a ∈ C, g a := by
    simpa [B, C] using sum_latticeShiftBox_translate n (latticeShiftUnit i) g
  have hcard : (B \ C).card + (C \ B).card = 2 * (2 * n + 1) ^ 3 := by
    simpa [B, C] using unit_translate_symmDiff_card n i
  have hcardℝ : (Fintype.card {a : LatticeShift // a ∈ latticeShiftBox n} : ℝ) =
      (2 * n + 1 : ℝ) ^ 4 := by
    exact_mod_cast latticeShiftBox_index_card n
  rw [finiteShiftAverage_apply_toReal, finiteShiftAverage_apply_toReal,
    hcardℝ]
  rw [show (∑ a ∈ B, (fun a => (f (a + latticeShiftUnit i) x).toReal) a) =
      ∑ a ∈ C, g a by simpa [B, C, g] using hsumMap]
  have hden : 0 < (2 * n + 1 : ℝ) ^ 4 := by positivity
  have hbound : |(∑ a ∈ C, g a) - ∑ a ∈ B, g a| ≤
      ((B \ C).card + (C \ B).card : ℝ) := by
    simpa [B, C, abs_sub_comm] using hsum
  have hbound' : |(∑ a ∈ C, g a) - ∑ a ∈ B, g a| ≤
      2 * (2 * n + 1 : ℝ) ^ 3 := by
    have hcardR : ((B \ C).card : ℝ) + ((C \ B).card : ℝ) =
        2 * (2 * n + 1 : ℝ) ^ 3 := by exact_mod_cast hcard
    rw [hcardR] at hbound
    exact hbound
  rw [← mul_sub]
  calc
    |((2 * n + 1 : ℝ) ^ 4)⁻¹ *
          ((∑ a ∈ C, g a) - ∑ a ∈ B, g a)| =
        ((2 * n + 1 : ℝ) ^ 4)⁻¹ *
          |(∑ a ∈ C, g a) - ∑ a ∈ B, g a| := by
            rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr hden.le)]
    _ ≤ ((2 * n + 1 : ℝ) ^ 4)⁻¹ *
          (2 * (2 * n + 1 : ℝ) ^ 3) :=
            mul_le_mul_of_nonneg_left hbound' (by positivity)
    _ = 2 / (2 * n + 1 : ℝ) := by
      field_simp

private theorem tendsto_two_div_latticeShiftBoxSide :
    Tendsto (fun n : ℕ => 2 / (2 * n + 1 : ℝ)) atTop (𝓝 0) := by
  have hside : Tendsto (fun n : ℕ => (2 * n + 1 : ℝ)) atTop atTop := by
    apply tendsto_atTop.2
    intro r
    obtain ⟨N, hN⟩ := exists_nat_gt r
    exact Filter.eventually_atTop.2 ⟨N, fun n hn => by
      have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
      have hN' : r < (N : ℝ) := by exact_mod_cast hN
      have hle : (N : ℝ) ≤ 2 * (n : ℝ) + 1 := by nlinarith
      exact le_trans hN'.le hle⟩
  have hinv := tendsto_inv_atTop_zero.comp hside
  have hfun : (fun n : ℕ => 2 / (2 * n + 1 : ℝ)) =
      fun n : ℕ => 2 * ((2 * n + 1 : ℝ)⁻¹) := by
    funext n
    ring_nf
  rw [hfun]
  simpa using tendsto_const_nhds.mul hinv

noncomputable def shiftedCylinderAverage (ν : CurvatureCylinderState)
    (b : LatticeShift) (n : ℕ) (P : Finset GlobalIntegerPlaquette) : PMF (P → ℤ) :=
  finiteShiftAverage n (fun a => translateCylinderLaw ν (a + b) P)

theorem shiftedCylinderAverage_translate (ν : CurvatureCylinderState)
    (b c : LatticeShift) (n : ℕ) (P : Finset GlobalIntegerPlaquette) :
    shiftedCylinderAverage (translateCylinderState ν b) c n P =
      shiftedCylinderAverage ν (b + c) n P := by
  unfold shiftedCylinderAverage
  congr 1
  funext a
  rw [translateCylinderLaw_add]
  congr 1
  ext i
  simp only [Pi.add_apply]
  abel

def AveragedCylinderShiftStable (b : LatticeShift) : Prop :=
  ∀ (ν : CurvatureCylinderState) (P : Finset GlobalIntegerPlaquette) (x : P → ℤ),
    Tendsto
      (fun n =>
        (shiftedCylinderAverage ν b n P x).toReal -
          (shiftedCylinderAverage ν 0 n P x).toReal)
      atTop (𝓝 0)

theorem averagedCylinderShiftStable_zero : AveragedCylinderShiftStable 0 := by
  intro ν P x
  have hzero : ∀ n,
      (shiftedCylinderAverage ν 0 n P x).toReal -
        (shiftedCylinderAverage ν 0 n P x).toReal = 0 := by
    intro n
    ring_nf
  exact tendsto_const_nhds.congr' (Filter.Eventually.of_forall fun n => (hzero n).symm)

theorem averagedCylinderShiftStable_unit (i : Fin 4) :
    AveragedCylinderShiftStable (latticeShiftUnit i) := by
  intro ν P x
  rw [tendsto_zero_iff_abs_tendsto_zero]
  have hbound : ∀ n,
      |(shiftedCylinderAverage ν (latticeShiftUnit i) n P x).toReal -
          (shiftedCylinderAverage ν 0 n P x).toReal| ≤ 2 / (2 * n + 1 : ℝ) := by
    intro n
    simpa [shiftedCylinderAverage] using
      finiteShiftAverage_translate_unit_error n
        (fun a => translateCylinderLaw ν a P) x i
  apply squeeze_zero (fun _ => abs_nonneg _)
  · exact hbound
  · exact tendsto_two_div_latticeShiftBoxSide

theorem averagedCylinderShiftStable_add {b c : LatticeShift}
    (hb : AveragedCylinderShiftStable b) (hc : AveragedCylinderShiftStable c) :
    AveragedCylinderShiftStable (b + c) := by
  intro ν P x
  have hbc := hc (translateCylinderState ν b) P x
  have hb' := hb ν P x
  have hsum := hbc.add hb'
  have heq (n : ℕ) :
      ((shiftedCylinderAverage (translateCylinderState ν b) c n P x).toReal -
          (shiftedCylinderAverage (translateCylinderState ν b) 0 n P x).toReal) +
        ((shiftedCylinderAverage ν b n P x).toReal -
          (shiftedCylinderAverage ν 0 n P x).toReal) =
        (shiftedCylinderAverage ν (b + c) n P x).toReal -
          (shiftedCylinderAverage ν 0 n P x).toReal := by
    rw [shiftedCylinderAverage_translate, shiftedCylinderAverage_translate]
    simp only [add_zero]
    ring
  simpa using hsum.congr' (Filter.Eventually.of_forall heq)

theorem averagedCylinderShiftStable_neg {b : LatticeShift}
    (hb : AveragedCylinderShiftStable b) : AveragedCylinderShiftStable (-b) := by
  intro ν P x
  have h := hb (translateCylinderState ν (-b)) P x
  have hneg := h.neg
  have heq (n : ℕ) :
      -((shiftedCylinderAverage (translateCylinderState ν (-b)) b n P x).toReal -
          (shiftedCylinderAverage (translateCylinderState ν (-b)) 0 n P x).toReal) =
        (shiftedCylinderAverage ν (-b) n P x).toReal -
          (shiftedCylinderAverage ν 0 n P x).toReal := by
    rw [shiftedCylinderAverage_translate, shiftedCylinderAverage_translate]
    simp only [neg_add_cancel, add_zero]
    ring
  simpa using hneg.congr' (Filter.Eventually.of_forall heq)

def averagedCylinderStableShifts : AddSubgroup LatticeShift where
  carrier := {b | AveragedCylinderShiftStable b}
  zero_mem' := averagedCylinderShiftStable_zero
  add_mem' := fun hb hc => averagedCylinderShiftStable_add hb hc
  neg_mem' := fun hb => averagedCylinderShiftStable_neg hb

theorem latticeShiftUnit_mem_averagedCylinderStableShifts (i : Fin 4) :
    latticeShiftUnit i ∈ averagedCylinderStableShifts :=
  averagedCylinderShiftStable_unit i

theorem latticeShift_mem_averagedCylinderStableShifts (b : LatticeShift) :
    b ∈ averagedCylinderStableShifts := by
  have hcoord (i : Fin 4) : Pi.single i (b i) ∈ averagedCylinderStableShifts := by
    have hsingle : Pi.single i (b i) = (b i) • latticeShiftUnit i := by
      ext j
      by_cases hji : j = i
      · subst j
        simp [latticeShiftUnit]
      · simp [latticeShiftUnit, hji]
    rw [hsingle]
    exact averagedCylinderStableShifts.zsmul_mem
      (latticeShiftUnit_mem_averagedCylinderStableShifts i) (b i)
  have hdecomp : b = Pi.single 0 (b 0) + Pi.single 1 (b 1) +
      Pi.single 2 (b 2) + Pi.single 3 (b 3) := by
    ext i
    fin_cases i <;> simp
  rw [hdecomp]
  exact averagedCylinderStableShifts.add_mem
    (averagedCylinderStableShifts.add_mem
      (averagedCylinderStableShifts.add_mem (hcoord 0) (hcoord 1)) (hcoord 2))
    (hcoord 3)

theorem finiteShiftAverage_map {α β : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] [Countable α] [DecidableEq α]
    [MeasurableSpace β] [MeasurableSingletonClass β] [Countable β] [DecidableEq β]
    (n : ℕ) (f : LatticeShift → PMF α) (g : α → β) :
    PMF.map g (finiteShiftAverage n f) =
      finiteShiftAverage n (fun a => PMF.map g (f a)) := by
  classical
  simp [finiteShiftAverage, PMF.map_bind]

theorem finiteShiftAverage_consistent {α β : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] [Countable α] [DecidableEq α]
    [MeasurableSpace β] [MeasurableSingletonClass β] [Countable β] [DecidableEq β]
    (n : ℕ) (f : LatticeShift → PMF α) (g : LatticeShift → PMF β) (r : α → β)
    (h : ∀ a, PMF.map r (f a) = g a) :
    PMF.map r (finiteShiftAverage n f) = finiteShiftAverage n g := by
  classical
  rw [finiteShiftAverage, PMF.map_bind]
  congr 1
  funext a
  exact h a

/-- A finite mixture preserves a common tightness set. -/
theorem finiteShiftAverage_tight_of_uniform_tight
    {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    [Countable α] [DecidableEq α]
    (n : ℕ) (f : LatticeShift → PMF α) (S : Finset α) {ε : ℝ}
    (hε₁ : ε < 1)
    (htight : ∀ a, 1 - ε ≤ ∑ x ∈ S, (f a x).toReal) :
    1 - ε ≤ ∑ x ∈ S, (finiteShiftAverage n f x).toReal := by
  classical
  have hnonneg : 0 ≤ 1 - ε := by linarith
  have hSmeas : MeasurableSet (S : Set α) := by
    exact (S.finite_toSet).measurableSet
  have hcomp (a : LatticeShift) :
      ENNReal.ofReal (1 - ε) ≤ (f a).toMeasure (S : Set α) := by
    have hprob : (f a).toMeasure (S : Set α) ≤ 1 := by
      calc
        _ ≤ (f a).toMeasure Set.univ := MeasureTheory.measure_mono (Set.subset_univ _)
        _ = 1 := by simp
    have hnotTop : (f a).toMeasure (S : Set α) ≠ ⊤ :=
      ne_of_lt (lt_of_le_of_lt hprob ENNReal.one_lt_top)
    apply (ENNReal.ofReal_le_iff_le_toReal hnotTop).2
    rw [PMF.toMeasure_apply_finset, ENNReal.toReal_sum
      (fun x hx => (f a).apply_ne_top x)]
    simpa [ENNReal.toReal_ofReal hnonneg] using htight a
  have hbind : ENNReal.ofReal (1 - ε) ≤
      (finiteShiftAverage n f).toMeasure (S : Set α) := by
    rw [finiteShiftAverage, PMF.toMeasure_bind_apply
      (p := latticeShiftUniform n) (f := f) (S : Set α) hSmeas]
    calc
      ENNReal.ofReal (1 - ε) =
          ∑' a, (latticeShiftUniform n a) * ENNReal.ofReal (1 - ε) := by
            rw [ENNReal.tsum_mul_right, PMF.tsum_coe]
            simp
      _ ≤ ∑' a, (latticeShiftUniform n a) *
          (f a).toMeasure (S : Set α) := by
            apply ENNReal.tsum_le_tsum
            intro a
            exact mul_le_mul_of_nonneg_left (hcomp a) (by positivity)
  have hprob : (finiteShiftAverage n f).toMeasure (S : Set α) ≤ 1 := by
    calc
      _ ≤ (finiteShiftAverage n f).toMeasure Set.univ := MeasureTheory.measure_mono
        (Set.subset_univ _)
      _ = 1 := by simp
  have hnotTop : (finiteShiftAverage n f).toMeasure (S : Set α) ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt hprob ENNReal.one_lt_top)
  have hreal := (ENNReal.ofReal_le_iff_le_toReal hnotTop).1 hbind
  rw [PMF.toMeasure_apply_finset, ENNReal.toReal_sum
    (fun x hx => (finiteShiftAverage n f).apply_ne_top x)] at hreal
  simpa [ENNReal.toReal_ofReal hnonneg] using hreal

noncomputable def averagedCylinderLaw (ν : CurvatureCylinderState) (n : ℕ)
    (P : Finset GlobalIntegerPlaquette) : PMF (P → ℤ) :=
  finiteShiftAverage n (fun a => translateCylinderLaw ν a P)

theorem averagedCylinderLaw_consistent (ν : CurvatureCylinderState) (n : ℕ)
    (P₀ P₁ : Finset GlobalIntegerPlaquette) (hP : P₀ ⊆ P₁) :
    PMF.map (restrictCurvature hP) (averagedCylinderLaw ν n P₁) =
      averagedCylinderLaw ν n P₀ := by
  apply finiteShiftAverage_consistent
  intro a
  exact translateCylinderLaw_consistent ν a P₀ P₁ hP

noncomputable def averagedCylinderState (ν : CurvatureCylinderState) (n : ℕ) :
    CurvatureCylinderState where
  law := fun P => averagedCylinderLaw ν n P
  consistent := averagedCylinderLaw_consistent ν n

theorem shiftedCylinderAverage_zero (ν : CurvatureCylinderState)
    (n : ℕ) (P : Finset GlobalIntegerPlaquette) :
    shiftedCylinderAverage ν 0 n P = averagedCylinderLaw ν n P := by
  unfold shiftedCylinderAverage averagedCylinderLaw
  congr 1
  funext a
  simp

theorem translateAveragedCylinderLaw
    (ν : CurvatureCylinderState) (n : ℕ) (b : LatticeShift)
    (P : Finset GlobalIntegerPlaquette) :
    translateCylinderLaw (averagedCylinderState ν n) b P =
      finiteShiftAverage n (fun a => translateCylinderLaw ν (a + b) P) := by
  classical
  change PMF.map (untranslateCurvatureAssignment b P)
      (finiteShiftAverage n (fun a =>
        translateCylinderLaw ν a (translatePlaquettes b P))) = _
  rw [finiteShiftAverage_map]
  congr 1
  funext a
  exact translateCylinderLaw_add ν b a P

noncomputable def curvatureIndexCastEquiv
    {P Q : Finset GlobalIntegerPlaquette} (h : P = Q) : P ≃ Q :=
  Equiv.cast (congrArg (fun S : Finset GlobalIntegerPlaquette =>
    {p : GlobalIntegerPlaquette // p ∈ S}) h)

@[simp] theorem curvatureIndexCastEquiv_val
    {P Q : Finset GlobalIntegerPlaquette} (h : P = Q) (p : P) :
    (curvatureIndexCastEquiv h p).1 = p.1 := by
  cases h
  rfl

noncomputable def curvatureAssignmentCastEquiv
    {P Q : Finset GlobalIntegerPlaquette} (h : P = Q) : (P → ℤ) ≃ (Q → ℤ) where
  toFun x := fun q => x ((curvatureIndexCastEquiv h).symm q)
  invFun y := fun p => y ((curvatureIndexCastEquiv h) p)
  left_inv := by
    intro x
    funext p
    simp
  right_inv := by
    intro y
    funext q
    simp

theorem curvatureCylinderLaw_map_finsetEq
    (ν : CurvatureCylinderState) {P Q : Finset GlobalIntegerPlaquette}
    (h : P = Q) :
    PMF.map (curvatureAssignmentCastEquiv h) (ν.law P) = ν.law Q := by
  cases h
  change PMF.map id (ν.law P) = ν.law P
  exact PMF.map_id _

private theorem spectral_pmf_mass_summable {α : Type*} [Countable α]
    (p : PMF α) : Summable (fun x => (p x).toReal) := by
  apply ENNReal.summable_toReal
  rw [p.tsum_coe]
  exact ENNReal.one_ne_top


theorem cubeCurvatureLimitState_expLinear_integrable_spectral
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
  have hsq : ∀ k, Summable (fun x => (pn k x).toReal * (f x) ^ 2) := by
    intro k
    exact (cubeCurvaturePMFTotal_exp_linear_secondMoment
      (L.subsequence k) β hβ P c s).1
  have hsqBound : ∀ k, ∑' x, (pn k x).toReal * (f x) ^ 2 ≤ C := by
    intro k
    exact cubeCurvaturePMFTotal_exp_linear_secondMoment
      (L.subsequence k) β hβ P c s |>.2
  have hlimSq := pmf_secondMoment_bound_of_pointwise
    pn p f C hpoint hsq hsqBound
  have hmass := spectral_pmf_mass_summable p
  have hYoung (x : P → ℤ) : f x ≤ 1 + (f x) ^ 2 := by
    nlinarith [sq_nonneg (f x - 1 / 2)]
  have hweight : Summable (fun x => (p x).toReal * f x) := by
    apply Summable.of_nonneg_of_le
      (fun x => mul_nonneg ENNReal.toReal_nonneg (Real.exp_pos _).le)
    · intro x
      exact mul_le_mul_of_nonneg_left (hYoung x) ENNReal.toReal_nonneg
    · simpa [mul_add] using hmass.add hlimSq.1
  have hnorm : Summable (fun x => (p x).toReal * ‖f x‖) := by
    refine hweight.congr ?_
    intro x
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact pmf_integrable_of_summable_norm hnorm

private theorem spectral_sq_le_exp_abs (x : ℝ) :
    x ^ 2 ≤ 4 * Real.exp |x| := by
  let u := |x|
  have hu : 0 ≤ u := abs_nonneg x
  have hlin : u / 2 + 1 ≤ Real.exp (u / 2) := Real.add_one_le_exp _
  have hnonneg : 0 ≤ u / 2 + 1 := by positivity
  have hsq : (u / 2 + 1) ^ 2 ≤ Real.exp (u / 2) ^ 2 := by
    nlinarith [mul_self_le_mul_self hnonneg hlin]
  have hexp : Real.exp (u / 2) ^ 2 = Real.exp u := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring_nf
  have hpoly : u ^ 2 ≤ 4 * (u / 2 + 1) ^ 2 := by nlinarith
  have hx2 : x ^ 2 = u ^ 2 := by simp [u, sq_abs]
  calc
    x ^ 2 = u ^ 2 := hx2
    _ ≤ 4 * (u / 2 + 1) ^ 2 := hpoly
    _ ≤ 4 * Real.exp (u / 2) ^ 2 := by
      exact mul_le_mul_of_nonneg_left hsq (by norm_num)
    _ = 4 * Real.exp u := by rw [hexp]
    _ = 4 * Real.exp |x| := rfl

private theorem spectral_exp_abs_le (x : ℝ) :
    Real.exp |x| ≤ Real.exp x + Real.exp (-x) := by
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx]
    linarith [Real.exp_pos (-x)]
  · have hx' : x < 0 := lt_of_not_ge hx
    rw [abs_of_neg hx']
    linarith [Real.exp_pos x]


/-- Exponential integrability transfers through the exact translation map of
a finite curvature cylinder. -/
theorem translateCylinderLaw_sourceFilling_exp_integrable
    {β : ℝ} (hβ : 0 < β) (L : CubeCurvatureLimitState β hβ)
    (σ : GlobalPlaquetteField) (a : LatticeShift) (t : ℝ) :
    Integrable (fun x => Real.exp (t * sourceFillingCurvaturePairing σ x))
      (translateCylinderLaw (cubeStateToCylinderState L) a
        (fillingCurvatureIndexSet σ)).toMeasure := by
  classical
  let P := fillingCurvatureIndexSet σ
  let σa := translateGlobalPlaquetteField a σ
  let Pa := fillingCurvatureIndexSet σa
  let Ta := translatePlaquettes a P
  have hPa : Pa = Ta := fillingCurvatureIndexSet_translate a σ
  let e := translateFillingIndexEquiv a σ
  let c := curvatureAssignmentCastEquiv hPa
  let U := untranslateCurvatureAssignment a P
  let F : (Pa → ℤ) → (P → ℤ) := fun y => U (c y)
  have hLaw : PMF.map c (L.law Pa) = L.law Ta :=
    curvatureCylinderLaw_map_finsetEq (cubeStateToCylinderState L) hPa
  have hmapLaw : PMF.map F (L.law Pa) =
      translateCylinderLaw (cubeStateToCylinderState L) a P := by
    change PMF.map (U ∘ c) (L.law Pa) = PMF.map U (L.law Ta)
    rw [← hLaw]
    exact (PMF.map_comp c (L.law Pa) U).symm
  have hpair (y : Pa → ℤ) :
      sourceFillingCurvaturePairing σ (F y) =
        sourceFillingCurvaturePairing σa y := by
    have h := sourceFillingCurvaturePairing_translate a σ (F y)
    have hindex (q : Pa) :
        translatePlaquetteIndex a P (e.symm q) = (curvatureIndexCastEquiv hPa) q := by
      apply Subtype.ext
      have he := congrArg Subtype.val (e.apply_symm_apply q)
      have hcast := curvatureIndexCastEquiv_val hPa q
      have he' := he.trans hcast.symm
      simpa [e, translateFillingIndexEquiv, translatePlaquetteIndex] using he'
    have hassign : (fun q : Pa => F y (e.symm q)) = y := by
      funext q
      change (c y) (translatePlaquetteIndex a P (e.symm q)) = y q
      rw [hindex]
      simp [c, curvatureAssignmentCastEquiv]
    rw [hassign] at h
    exact h.symm
  have hsource := cubeCurvatureLimitState_expLinear_integrable_spectral β hβ L Pa
    (fun p => latticeCellOrientationSign p.1.1 *
      fillingPlaquetteCoeff σa p) t
  have hαa (y : Pa → ℤ) : sourceFillingCurvaturePairing σa y =
      ∑ p : Pa, (latticeCellOrientationSign p.1.1 *
        fillingPlaquetteCoeff σa p) * (y p : ℝ) := rfl
  have hsource' : Integrable
      (fun y : Pa → ℤ => Real.exp (t * sourceFillingCurvaturePairing σa y))
      (L.law Pa).toMeasure := by
    have heq : (fun y : Pa → ℤ => Real.exp
        (t * sourceFillingCurvaturePairing σa y)) =
        (fun y => Real.exp (t * ∑ p : Pa,
          (latticeCellOrientationSign p.1.1 * fillingPlaquetteCoeff σa p) *
            (y p : ℝ))) := by
      funext y
      rw [hαa]
    rw [heq]
    exact hsource
  have hcomp : Integrable
      (fun y : Pa → ℤ => Real.exp
        (t * sourceFillingCurvaturePairing σ (F y)))
      (L.law Pa).toMeasure := by
    have heq : (fun y : Pa → ℤ => Real.exp
        (t * sourceFillingCurvaturePairing σ (F y))) =
        (fun y => Real.exp (t * sourceFillingCurvaturePairing σa y)) := by
      funext y
      rw [hpair]
    rw [heq]
    exact hsource'
  have hmeas : Measurable F := by fun_prop
  have hmap := (MeasureTheory.integrable_map_measure
    (by fun_prop : AEStronglyMeasurable
      (fun x : P → ℤ => Real.exp (t * sourceFillingCurvaturePairing σ x))
      (Measure.map F (L.law Pa).toMeasure)) hmeas.aemeasurable).2 hcomp
  have hmap' : Integrable
      (fun x : P → ℤ => Real.exp (t * sourceFillingCurvaturePairing σ x))
      (PMF.map F (L.law Pa)).toMeasure := by
    rw [PMF.toMeasure_map F (L.law Pa) hmeas] at hmap
    exact hmap
  rw [hmapLaw] at hmap'
  exact hmap'

/-- Integrals of a filling observable in a translated law are the integrals
of the translated filling observable in the original projective law. -/
theorem translateCylinderLaw_sourceFilling_integral_eq
    {β : ℝ} (hβ : 0 < β) (L : CubeCurvatureLimitState β hβ)
    (σ : GlobalPlaquetteField) (a : LatticeShift) (g : ℝ → ℝ)
    (hg : StronglyMeasurable g) :
    ∫ x, g (sourceFillingCurvaturePairing σ x) ∂
        (translateCylinderLaw (cubeStateToCylinderState L) a
          (fillingCurvatureIndexSet σ)).toMeasure =
      ∫ y, g (sourceFillingCurvaturePairing
        (translateGlobalPlaquetteField a σ) y) ∂
          (L.law (fillingCurvatureIndexSet
            (translateGlobalPlaquetteField a σ))).toMeasure := by
  classical
  let P := fillingCurvatureIndexSet σ
  let σa := translateGlobalPlaquetteField a σ
  let Pa := fillingCurvatureIndexSet σa
  let Ta := translatePlaquettes a P
  have hPa : Pa = Ta := fillingCurvatureIndexSet_translate a σ
  let e := translateFillingIndexEquiv a σ
  let c := curvatureAssignmentCastEquiv hPa
  let U := untranslateCurvatureAssignment a P
  let F : (Pa → ℤ) → (P → ℤ) := fun y => U (c y)
  have hLaw : PMF.map c (L.law Pa) = L.law Ta :=
    curvatureCylinderLaw_map_finsetEq (cubeStateToCylinderState L) hPa
  have hmapLaw : PMF.map F (L.law Pa) =
      translateCylinderLaw (cubeStateToCylinderState L) a P := by
    change PMF.map (U ∘ c) (L.law Pa) = PMF.map U (L.law Ta)
    rw [← hLaw]
    exact (PMF.map_comp c (L.law Pa) U).symm
  have hpair (y : Pa → ℤ) :
      sourceFillingCurvaturePairing σ (F y) =
        sourceFillingCurvaturePairing σa y := by
    have h := sourceFillingCurvaturePairing_translate a σ (F y)
    have hindex (q : Pa) :
        translatePlaquetteIndex a P (e.symm q) = (curvatureIndexCastEquiv hPa) q := by
      apply Subtype.ext
      have he := congrArg Subtype.val (e.apply_symm_apply q)
      have hcast := curvatureIndexCastEquiv_val hPa q
      have he' := he.trans hcast.symm
      simpa [e, translateFillingIndexEquiv, translatePlaquetteIndex] using he'
    have hassign : (fun q : Pa => F y (e.symm q)) = y := by
      funext q
      change (c y) (translatePlaquetteIndex a P (e.symm q)) = y q
      rw [hindex]
      simp [c, curvatureAssignmentCastEquiv]
    rw [hassign] at h
    exact h.symm
  have hmeas : Measurable F := by fun_prop
  have hfg : StronglyMeasurable
      (fun x : P → ℤ => g (sourceFillingCurvaturePairing σ x)) := by
    exact hg.comp_measurable (by fun_prop)
  have hmap :
      ∫ x, g (sourceFillingCurvaturePairing σ x) ∂
          Measure.map F (L.law Pa).toMeasure =
        ∫ y, g (sourceFillingCurvaturePairing σ (F y)) ∂
          (L.law Pa).toMeasure :=
    MeasureTheory.integral_map_of_stronglyMeasurable hmeas hfg
  calc
    ∫ x, g (sourceFillingCurvaturePairing σ x) ∂
        (translateCylinderLaw (cubeStateToCylinderState L) a P).toMeasure =
      ∫ x, g (sourceFillingCurvaturePairing σ x) ∂
        (PMF.map F (L.law Pa)).toMeasure := by rw [hmapLaw]
    _ = ∫ y, g (sourceFillingCurvaturePairing σ (F y)) ∂
        (L.law Pa).toMeasure := by
          rw [← PMF.toMeasure_map F (L.law Pa) hmeas]
          exact hmap
    _ = ∫ y, g (sourceFillingCurvaturePairing σa y) ∂
        (L.law Pa).toMeasure := by
          apply integral_congr_ae
          filter_upwards [] with y
          rw [hpair y]

theorem translateCylinderLaw_sourceFilling_mgf_bounds
    {β : ℝ} (hβ : rootBetaThreshold ≤ β)
    (L : CubeCurvatureLimitState β (rootBeta_pos hβ))
    (μ : GlobalLinkField) (hμ : globallyCoClosed μ)
    (σ : GlobalPlaquetteField)
    (hfill : globalBoundary (σ : RealLatticeChain 4) =
      (μ : RealLatticeChain 4))
    (a : LatticeShift) (t : ℝ) :
    Real.exp ((t ^ 2 * betaDoublePrime rootPackingCoefficient β / 2) *
        fourierGreenQuadratic μ) ≤
      ∫ x, Real.exp (t * sourceFillingCurvaturePairing σ x) ∂
        (translateCylinderLaw (cubeStateToCylinderState L) a
          (fillingCurvatureIndexSet σ)).toMeasure ∧
    (∫ x, Real.exp (t * sourceFillingCurvaturePairing σ x) ∂
        (translateCylinderLaw (cubeStateToCylinderState L) a
          (fillingCurvatureIndexSet σ)).toMeasure) ≤
      Real.exp ((t ^ 2 * β / 2) * fourierGreenQuadratic μ) := by
  let σa := translateGlobalPlaquetteField a σ
  let μa := translateGlobalLinkField a μ
  have hμa : globallyCoClosed μa := translateGlobalLinkField_coClosed a μ hμ
  have hfillA : globalBoundary (σa : RealLatticeChain 4) =
      (μa : RealLatticeChain 4) := by
    rw [globalBoundary_translateGlobalPlaquetteField, hfill]
    rfl
  have hmgf := cubeCurvatureLimitState_sourceFilling_mgf_bounds
    hβ L μa hμa σa hfillA t
  have hgreen : fourierGreenQuadratic μa = fourierGreenQuadratic μ :=
    fourierGreenQuadratic_translate a μ hμ
  rw [hgreen] at hmgf
  have heq := translateCylinderLaw_sourceFilling_integral_eq
    (rootBeta_pos hβ) L σ a (fun x => Real.exp (t * x)) (by fun_prop)
  rw [heq]
  exact hmgf

private theorem spectral_fourth_le_exp_abs (x : ℝ) :
    x ^ 4 ≤ 256 * Real.exp |x| := by
  have hhalf := spectral_sq_le_exp_abs (x / 2)
  have habs : |x / 2| = |x| / 2 := by simp [abs_div]
  rw [habs] at hhalf
  have hsq : x ^ 2 ≤ 16 * Real.exp (|x| / 2) := by nlinarith [hhalf]
  have hsquare := mul_self_le_mul_self (sq_nonneg x) hsq
  calc
    x ^ 4 = (x ^ 2) * (x ^ 2) := by ring
    _ ≤ (16 * Real.exp (|x| / 2)) ^ 2 := by nlinarith [hsquare]
    _ = 256 * Real.exp (|x| / 2) ^ 2 := by ring
    _ = 256 * Real.exp |x| := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring_nf

theorem averagedCylinderLaw_sourceFilling_mgf_upper
    {β : ℝ} (hβ : rootBetaThreshold ≤ β)
    (L : CubeCurvatureLimitState β (rootBeta_pos hβ))
    (μ : GlobalLinkField) (hμ : globallyCoClosed μ)
    (σ : GlobalPlaquetteField)
    (hfill : globalBoundary (σ : RealLatticeChain 4) =
      (μ : RealLatticeChain 4)) (n : ℕ) (t : ℝ) :
    (∫ x, Real.exp (t * sourceFillingCurvaturePairing σ x) ∂
      (averagedCylinderLaw (cubeStateToCylinderState L) n
        (fillingCurvatureIndexSet σ)).toMeasure) ≤
      Real.exp ((t ^ 2 * β / 2) * fourierGreenQuadratic μ) := by
  classical
  let P := fillingCurvatureIndexSet σ
  let f : LatticeShift → PMF (P → ℤ) := fun a =>
    translateCylinderLaw (cubeStateToCylinderState L) a P
  let g : (P → ℤ) → ℝ := fun x =>
    Real.exp (t * sourceFillingCurvaturePairing σ x)
  let B := Real.exp ((t ^ 2 * β / 2) * fourierGreenQuadratic μ)
  have hfi (a : LatticeShift) : Integrable g (f a).toMeasure := by
    simpa [g, f] using translateCylinderLaw_sourceFilling_exp_integrable
      (rootBeta_pos hβ) L σ a t
  have havg := finiteShiftAverage_integral n f g hfi
  let cR : ℝ := Fintype.card {a : LatticeShift // a ∈ latticeShiftBox n}
  have hcR : 0 < cR := by
    dsimp [cR]
    have hz : (0 : LatticeShift) ∈ latticeShiftBox n := zero_mem_latticeShiftBox n
    exact_mod_cast (Fintype.card_pos_iff.mpr
      ⟨(⟨0, hz⟩ : {a : LatticeShift // a ∈ latticeShiftBox n})⟩)
  have hcardReal : cR = ((latticeShiftBox n).card : ℝ) := by
    dsimp [cR]
    simp
  have hterm (a : LatticeShift) : ∫ x, g x ∂(f a).toMeasure ≤ B := by
    simpa [g, f, B] using
      (translateCylinderLaw_sourceFilling_mgf_bounds hβ L μ hμ σ hfill a t).2
  have hsum : ∑ a ∈ latticeShiftBox n, ∫ x, g x ∂(f a).toMeasure ≤ cR * B := by
    calc
      _ ≤ ∑ _a ∈ latticeShiftBox n, B :=
        Finset.sum_le_sum fun a ha => hterm a
      _ = cR * B := by
        rw [Finset.sum_const, nsmul_eq_mul, hcardReal]
  have havgEq : ∫ x, g x ∂(averagedCylinderLaw
      (cubeStateToCylinderState L) n P).toMeasure =
      cR⁻¹ * ∑ a ∈ latticeShiftBox n, ∫ x, g x ∂(f a).toMeasure := by
    simpa [averagedCylinderLaw, f, cR, g] using havg.2
  rw [havgEq]
  calc
    cR⁻¹ * ∑ a ∈ latticeShiftBox n, ∫ x, g x ∂(f a).toMeasure ≤
      cR⁻¹ * (cR * B) := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = B := by field_simp [ne_of_gt hcR]

private theorem sourceFilling_fourth_integrable_of_exp
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (X : α → ℝ) (hX : Measurable X)
    (hplus : Integrable (fun x => Real.exp (X x)) μ)
    (hminus : Integrable (fun x => Real.exp (-X x)) μ) :
    Integrable (fun x => (X x) ^ 4) μ := by
  have hdom : Integrable (fun x => 256 *
      (Real.exp (X x) + Real.exp (-X x))) μ := by
    simpa [smul_eq_mul, mul_add] using (hplus.add hminus).const_mul 256
  have hmeas : AEStronglyMeasurable (fun x => (X x) ^ 4) μ :=
    (hX.pow_const 4).aestronglyMeasurable
  apply hdom.mono' hmeas
  filter_upwards [] with x
  have hnonneg : 0 ≤ (X x) ^ 4 := by positivity
  rw [Real.norm_of_nonneg hnonneg]
  calc
    (X x) ^ 4 ≤ 256 * Real.exp |X x| := spectral_fourth_le_exp_abs _
    _ ≤ 256 * (Real.exp (X x) + Real.exp (-X x)) := by
      exact mul_le_mul_of_nonneg_left (spectral_exp_abs_le _) (by norm_num)

theorem averagedCylinderLaw_sourceFilling_fourthMoment_bound
    {β : ℝ} (hβ : rootBetaThreshold ≤ β)
    (L : CubeCurvatureLimitState β (rootBeta_pos hβ))
    (μ : GlobalLinkField) (hμ : globallyCoClosed μ)
    (σ : GlobalPlaquetteField)
    (hfill : globalBoundary (σ : RealLatticeChain 4) =
      (μ : RealLatticeChain 4)) (n : ℕ) :
    Integrable (fun x => (sourceFillingCurvaturePairing σ x) ^ 4)
        (averagedCylinderLaw (cubeStateToCylinderState L) n
          (fillingCurvatureIndexSet σ)).toMeasure ∧
      ∫ x, (sourceFillingCurvaturePairing σ x) ^ 4 ∂
        (averagedCylinderLaw (cubeStateToCylinderState L) n
          (fillingCurvatureIndexSet σ)).toMeasure ≤
        512 * Real.exp ((β / 2) * fourierGreenQuadratic μ) := by
  classical
  let P := fillingCurvatureIndexSet σ
  let f : LatticeShift → PMF (P → ℤ) := fun a =>
    translateCylinderLaw (cubeStateToCylinderState L) a P
  let X : (P → ℤ) → ℝ := sourceFillingCurvaturePairing σ
  let ν := averagedCylinderLaw (cubeStateToCylinderState L) n P
  have hplusParts (a : LatticeShift) :
      Integrable (fun x => Real.exp (X x)) (f a).toMeasure := by
    simpa [X, f] using translateCylinderLaw_sourceFilling_exp_integrable
      (rootBeta_pos hβ) L σ a 1
  have hminusParts (a : LatticeShift) :
      Integrable (fun x => Real.exp (-X x)) (f a).toMeasure := by
    simpa [X, f] using translateCylinderLaw_sourceFilling_exp_integrable
      (rootBeta_pos hβ) L σ a (-1)
  have hplus : Integrable (fun x => Real.exp (X x)) ν.toMeasure := by
    simpa [ν, averagedCylinderLaw, f] using
      (finiteShiftAverage_integral n f (fun x => Real.exp (X x)) hplusParts).1
  have hminus : Integrable (fun x => Real.exp (-X x)) ν.toMeasure := by
    simpa [ν, averagedCylinderLaw, f] using
      (finiteShiftAverage_integral n f (fun x => Real.exp (-X x)) hminusParts).1
  have hfour := sourceFilling_fourth_integrable_of_exp X (by fun_prop) hplus hminus
  have hdom : Integrable (fun x => 256 *
      (Real.exp (X x) + Real.exp (-X x))) ν.toMeasure := by
    simpa [smul_eq_mul, mul_add] using (hplus.add hminus).const_mul 256
  have hpoint (x : P → ℤ) : (X x) ^ 4 ≤
      256 * (Real.exp (X x) + Real.exp (-X x)) := by
    calc
      (X x) ^ 4 ≤ 256 * Real.exp |X x| := spectral_fourth_le_exp_abs _
      _ ≤ 256 * (Real.exp (X x) + Real.exp (-X x)) := by
        exact mul_le_mul_of_nonneg_left (spectral_exp_abs_le _) (by norm_num)
  have hbound := MeasureTheory.integral_mono hfour hdom hpoint
  rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_add hplus hminus] at hbound
  have hplusBound := averagedCylinderLaw_sourceFilling_mgf_upper
    hβ L μ hμ σ hfill n 1
  have hminusBound := averagedCylinderLaw_sourceFilling_mgf_upper
    hβ L μ hμ σ hfill n (-1)
  have hplusBound' : ∫ x, Real.exp (X x) ∂ν.toMeasure ≤
      Real.exp ((β / 2) * fourierGreenQuadratic μ) := by
    simpa [ν, X, P] using hplusBound
  have hminusBound' : ∫ x, Real.exp (-X x) ∂ν.toMeasure ≤
      Real.exp ((β / 2) * fourierGreenQuadratic μ) := by
    simpa [ν, X, P, neg_mul] using hminusBound
  refine ⟨hfour, ?_⟩
  calc
    ∫ x, (X x) ^ 4 ∂ν.toMeasure ≤
        256 * (∫ x, Real.exp (X x) ∂ν.toMeasure +
          ∫ x, Real.exp (-X x) ∂ν.toMeasure) := hbound
    _ ≤ 512 * Real.exp ((β / 2) * fourierGreenQuadratic μ) := by
      nlinarith [hplusBound', hminusBound']

theorem translateCylinderLaw_sourceFilling_square_integrable
    {β : ℝ} (hβ : 0 < β) (L : CubeCurvatureLimitState β hβ)
    (σ : GlobalPlaquetteField) (a : LatticeShift) :
    Integrable (fun x => (sourceFillingCurvaturePairing σ x) ^ 2)
      (translateCylinderLaw (cubeStateToCylinderState L) a
        (fillingCurvatureIndexSet σ)).toMeasure := by
  let P := fillingCurvatureIndexSet σ
  let α : (P → ℤ) → ℝ := sourceFillingCurvaturePairing σ
  have hplus := translateCylinderLaw_sourceFilling_exp_integrable hβ L σ a 1
  have hminus := translateCylinderLaw_sourceFilling_exp_integrable hβ L σ a (-1)
  have hdom : Integrable (fun x => 4 * (Real.exp (α x) + Real.exp (-α x)))
      (translateCylinderLaw (cubeStateToCylinderState L) a P).toMeasure := by
    simpa [α, smul_eq_mul, mul_add] using (hplus.add hminus).const_mul 4
  have hmeas : AEStronglyMeasurable (fun x : P → ℤ => (α x) ^ 2)
      (translateCylinderLaw (cubeStateToCylinderState L) a P).toMeasure := by fun_prop
  apply hdom.mono' hmeas
  filter_upwards [] with x
  rw [Real.norm_of_nonneg (sq_nonneg (α x))]
  calc
    (α x) ^ 2 ≤ 4 * Real.exp |α x| := spectral_sq_le_exp_abs _
    _ ≤ 4 * (Real.exp (α x) + Real.exp (-α x)) := by
      exact mul_le_mul_of_nonneg_left (spectral_exp_abs_le _) (by norm_num)

theorem translateCylinderLaw_sourceFilling_secondMoment_bounds
    {β : ℝ} (hβ : rootBetaThreshold ≤ β)
    (L : CubeCurvatureLimitState β (rootBeta_pos hβ))
    (μ : GlobalLinkField) (hμ : globallyCoClosed μ)
    (σ : GlobalPlaquetteField)
    (hfill : globalBoundary (σ : RealLatticeChain 4) =
      (μ : RealLatticeChain 4))
    (a : LatticeShift) :
    betaDoublePrime rootPackingCoefficient β * fourierGreenQuadratic μ ≤
        ∫ x, (sourceFillingCurvaturePairing σ x) ^ 2 ∂
          (translateCylinderLaw (cubeStateToCylinderState L) a
            (fillingCurvatureIndexSet σ)).toMeasure ∧
      (∫ x, (sourceFillingCurvaturePairing σ x) ^ 2 ∂
          (translateCylinderLaw (cubeStateToCylinderState L) a
            (fillingCurvatureIndexSet σ)).toMeasure) ≤
        β * fourierGreenQuadratic μ := by
  classical
  let P := fillingCurvatureIndexSet σ
  let σa := translateGlobalPlaquetteField a σ
  let μa := translateGlobalLinkField a μ
  let Pa := fillingCurvatureIndexSet σa
  let Ta := translatePlaquettes a P
  have hμa : globallyCoClosed μa := translateGlobalLinkField_coClosed a μ hμ
  have hfillA : globalBoundary (σa : RealLatticeChain 4) =
      (μa : RealLatticeChain 4) := by
    rw [globalBoundary_translateGlobalPlaquetteField, hfill]
    rfl
  have hPa : Pa = Ta := by
    dsimp [Pa, Ta, P]
    exact fillingCurvatureIndexSet_translate a σ
  have hmoment := cubeCurvatureLimitState_sourceFilling_secondMoment_bounds
    hβ L μa hμa σa hfillA
  rw [show fourierGreenQuadratic μa = fourierGreenQuadratic μ by
    exact fourierGreenQuadratic_translate a μ hμ] at hmoment
  let e := translateFillingIndexEquiv a σ
  let c := curvatureAssignmentCastEquiv hPa
  let U := untranslateCurvatureAssignment a P
  let F : (Pa → ℤ) → (P → ℤ) := fun y => U (c y)
  have hLaw : PMF.map c (L.law Pa) = L.law Ta := by
    exact curvatureCylinderLaw_map_finsetEq (cubeStateToCylinderState L) hPa
  have hpair (y : Pa → ℤ) :
      sourceFillingCurvaturePairing σ (F y) =
        sourceFillingCurvaturePairing σa y := by
    have h := sourceFillingCurvaturePairing_translate a σ (F y)
    have hindex (q : Pa) :
        translatePlaquetteIndex a P (e.symm q) = (curvatureIndexCastEquiv hPa) q := by
      apply Subtype.ext
      have he := congrArg Subtype.val (e.apply_symm_apply q)
      have hcast := curvatureIndexCastEquiv_val hPa q
      have he' := he.trans hcast.symm
      simpa [e, translateFillingIndexEquiv, translatePlaquetteIndex] using he'
    have hassign : (fun q : Pa => F y (e.symm q)) = y := by
      funext q
      change y ((curvatureIndexCastEquiv hPa).symm
        (translatePlaquetteIndex a P (e.symm q))) = y q
      rw [hindex, Equiv.symm_apply_apply]
    rw [hassign] at h
    exact h.symm
  have hmap :
      ∫ x, (sourceFillingCurvaturePairing σ x) ^ 2 ∂
          (translateCylinderLaw (cubeStateToCylinderState L) a P).toMeasure =
        ∫ y, (sourceFillingCurvaturePairing σ (F y)) ^ 2 ∂(L.law Pa).toMeasure := by
    change ∫ x, (sourceFillingCurvaturePairing σ x) ^ 2 ∂
      (PMF.map U (L.law Ta)).toMeasure = _
    rw [← hLaw, PMF.map_comp]
    rw [← PMF.toMeasure_map (U ∘ c) (L.law Pa) (by fun_prop : Measurable (U ∘ c))]
    exact MeasureTheory.integral_map_of_stronglyMeasurable
      (by fun_prop : Measurable (U ∘ c))
      (by fun_prop : StronglyMeasurable (fun y =>
        (sourceFillingCurvaturePairing σ y) ^ 2))
  have hpairInt :
      ∫ y, (sourceFillingCurvaturePairing σ (F y)) ^ 2 ∂(L.law Pa).toMeasure =
        ∫ y, (sourceFillingCurvaturePairing σa y) ^ 2 ∂(L.law Pa).toMeasure := by
    apply integral_congr_ae
    filter_upwards [] with y
    rw [hpair y]
  constructor
  · calc
      betaDoublePrime rootPackingCoefficient β * fourierGreenQuadratic μ ≤
          ∫ y, (sourceFillingCurvaturePairing σa y) ^ 2 ∂(L.law Pa).toMeasure :=
        hmoment.1
      _ = ∫ y, (sourceFillingCurvaturePairing σ (F y)) ^ 2 ∂(L.law Pa).toMeasure :=
        hpairInt.symm
      _ = ∫ x, (sourceFillingCurvaturePairing σ x) ^ 2 ∂
          (translateCylinderLaw (cubeStateToCylinderState L) a P).toMeasure :=
        hmap.symm
  · calc
      ∫ x, (sourceFillingCurvaturePairing σ x) ^ 2 ∂
          (translateCylinderLaw (cubeStateToCylinderState L) a P).toMeasure =
        ∫ y, (sourceFillingCurvaturePairing σ (F y)) ^ 2 ∂(L.law Pa).toMeasure :=
          hmap
      _ = ∫ y, (sourceFillingCurvaturePairing σa y) ^ 2 ∂(L.law Pa).toMeasure :=
          hpairInt
      _ ≤ β * fourierGreenQuadratic μ := hmoment.2

theorem averagedCylinderLaw_sourceFilling_secondMoment_bounds
    {β : ℝ} (hβ : rootBetaThreshold ≤ β)
    (L : CubeCurvatureLimitState β (rootBeta_pos hβ))
    (σ : GlobalPlaquetteField) (μ : GlobalLinkField)
    (hμ : globallyCoClosed μ)
    (hfill : globalBoundary (σ : RealLatticeChain 4) =
      (μ : RealLatticeChain 4)) (n : ℕ) :
    betaDoublePrime rootPackingCoefficient β * fourierGreenQuadratic μ ≤
        ∫ x, (sourceFillingCurvaturePairing σ x) ^ 2 ∂
          (averagedCylinderLaw (cubeStateToCylinderState L) n
            (fillingCurvatureIndexSet σ)).toMeasure ∧
      (∫ x, (sourceFillingCurvaturePairing σ x) ^ 2 ∂
          (averagedCylinderLaw (cubeStateToCylinderState L) n
            (fillingCurvatureIndexSet σ)).toMeasure) ≤
        β * fourierGreenQuadratic μ := by
  classical
  let P := fillingCurvatureIndexSet σ
  let f : LatticeShift → PMF (P → ℤ) := fun a =>
    translateCylinderLaw (cubeStateToCylinderState L) a P
  let α : (P → ℤ) → ℝ := fun x => sourceFillingCurvaturePairing σ x
  have hfi (a : LatticeShift) : Integrable (fun x => (α x) ^ 2)
      (f a).toMeasure := by
    simpa [f, α] using translateCylinderLaw_sourceFilling_square_integrable
      (rootBeta_pos hβ) L σ a
  have havg := finiteShiftAverage_integral n f (fun x => (α x) ^ 2) hfi
  let cR : ℝ := Fintype.card {a : LatticeShift // a ∈ latticeShiftBox n}
  have hcR : 0 < cR := by
    dsimp [cR]
    have hz : (0 : LatticeShift) ∈ latticeShiftBox n := zero_mem_latticeShiftBox n
    exact_mod_cast (Fintype.card_pos_iff.mpr
      ⟨(⟨0, hz⟩ : {a : LatticeShift // a ∈ latticeShiftBox n})⟩)
  have hcardReal : cR = ((latticeShiftBox n).card : ℝ) := by
    dsimp [cR]
    simp
  have hsumLower :
      ∑ a ∈ latticeShiftBox n,
        betaDoublePrime rootPackingCoefficient β * fourierGreenQuadratic μ =
      cR * (betaDoublePrime rootPackingCoefficient β * fourierGreenQuadratic μ) := by
    rw [hcardReal]
    simp [Finset.sum_const, nsmul_eq_mul]
  have hsumUpper :
      ∑ a ∈ latticeShiftBox n, β * fourierGreenQuadratic μ =
      cR * (β * fourierGreenQuadratic μ) := by
    rw [hcardReal]
    simp [Finset.sum_const, nsmul_eq_mul]
  have hterm (a : LatticeShift) :
      betaDoublePrime rootPackingCoefficient β * fourierGreenQuadratic μ ≤
        ∫ x, (α x) ^ 2 ∂(f a).toMeasure ∧
      (∫ x, (α x) ^ 2 ∂(f a).toMeasure) ≤ β * fourierGreenQuadratic μ := by
    simpa [f, α] using translateCylinderLaw_sourceFilling_secondMoment_bounds
      hβ L μ hμ σ hfill a
  have hlow : betaDoublePrime rootPackingCoefficient β * fourierGreenQuadratic μ ≤
      cR⁻¹ * ∑ a ∈ latticeShiftBox n,
        ∫ x, (α x) ^ 2 ∂(f a).toMeasure := by
    calc
      betaDoublePrime rootPackingCoefficient β * fourierGreenQuadratic μ =
          cR⁻¹ * (cR *
            (betaDoublePrime rootPackingCoefficient β * fourierGreenQuadratic μ)) := by
              field_simp [ne_of_gt hcR]
      _ = cR⁻¹ * ∑ a ∈ latticeShiftBox n,
          betaDoublePrime rootPackingCoefficient β * fourierGreenQuadratic μ := by
            rw [hsumLower]
      _ ≤ cR⁻¹ * ∑ a ∈ latticeShiftBox n,
          ∫ x, (α x) ^ 2 ∂(f a).toMeasure := by
            exact mul_le_mul_of_nonneg_left
              (Finset.sum_le_sum fun a ha => (hterm a).1) (by positivity)
  have hupp : cR⁻¹ * ∑ a ∈ latticeShiftBox n,
      ∫ x, (α x) ^ 2 ∂(f a).toMeasure ≤ β * fourierGreenQuadratic μ := by
    calc
      cR⁻¹ * ∑ a ∈ latticeShiftBox n,
          ∫ x, (α x) ^ 2 ∂(f a).toMeasure ≤
        cR⁻¹ * ∑ a ∈ latticeShiftBox n, β * fourierGreenQuadratic μ := by
          exact mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum fun a ha => (hterm a).2) (by positivity)
      _ = cR⁻¹ * (cR * (β * fourierGreenQuadratic μ)) := by rw [hsumUpper]
      _ = β * fourierGreenQuadratic μ := by field_simp [ne_of_gt hcR]
  have havgEq :
      ∫ x, (α x) ^ 2 ∂(averagedCylinderLaw (cubeStateToCylinderState L) n P).toMeasure =
        cR⁻¹ * ∑ a ∈ latticeShiftBox n,
          ∫ x, (α x) ^ 2 ∂(f a).toMeasure := by
    simpa [averagedCylinderLaw, f, cR, α] using havg.2
  rw [havgEq]
  exact ⟨hlow, hupp⟩

theorem projectiveAveragedCylinderLimit_sourceFilling_secondMoment_bounds
    {β : ℝ} (hβ : rootBetaThreshold ≤ β)
    (L : CubeCurvatureLimitState β (rootBeta_pos hβ))
    (s : ℕ → ℕ) (S : CurvatureCylinderState)
    (hpoint : ∀ P x, Tendsto
      (fun k => (averagedCylinderLaw (cubeStateToCylinderState L) (s k) P x).toReal)
      atTop (𝓝 ((S.law P x).toReal)))
    (μ : GlobalLinkField) (hμ : globallyCoClosed μ)
    (σ : GlobalPlaquetteField)
    (hfill : globalBoundary (σ : RealLatticeChain 4) =
      (μ : RealLatticeChain 4)) :
    Integrable (fun x => (sourceFillingCurvaturePairing σ x) ^ 2)
        (S.law (fillingCurvatureIndexSet σ)).toMeasure ∧
      betaDoublePrime rootPackingCoefficient β * fourierGreenQuadratic μ ≤
        ∫ x, (sourceFillingCurvaturePairing σ x) ^ 2 ∂
          (S.law (fillingCurvatureIndexSet σ)).toMeasure ∧
      (∫ x, (sourceFillingCurvaturePairing σ x) ^ 2 ∂
          (S.law (fillingCurvatureIndexSet σ)).toMeasure) ≤
        β * fourierGreenQuadratic μ := by
  classical
  let P := fillingCurvatureIndexSet σ
  let p : PMF (P → ℤ) := S.law P
  let pn : ℕ → PMF (P → ℤ) := fun k =>
    averagedCylinderLaw (cubeStateToCylinderState L) (s k) P
  let f : (P → ℤ) → ℝ := fun x =>
    (sourceFillingCurvaturePairing σ x) ^ 2
  let C := 512 * Real.exp ((β / 2) * fourierGreenQuadratic μ)
  have hpoint' : ∀ x, Tendsto (fun k => (pn k x).toReal) atTop
      (𝓝 ((p x).toReal)) := by
    intro x
    exact hpoint P x
  have htight : ∀ ε : ℝ, 0 < ε → ∃ T : Finset (P → ℤ), ∀ k,
      1 - ε ≤ ∑ x ∈ T, (pn k x).toReal := by
    intro ε hε
    let ε' := min ε (1 / 2)
    have hε'pos : 0 < ε' := by dsimp [ε']; positivity
    have hε'le : ε' ≤ ε := min_le_left _ _
    have hε'lt : ε' < 1 := by dsimp [ε']; norm_num
    obtain ⟨K, hK⟩ := cubeCurvatureLimitState_uniform_box_tight
      (rootBeta_pos hβ) L P ε' hε'pos
    let T := (curvatureCoordinateBox_finite (P := P) K).toFinset
    have hTset : (T : Set (P → ℤ)) = curvatureCoordinateBox (P := P) K :=
      (curvatureCoordinateBox_finite (P := P) K).coe_toFinset
    have hsingle (a : LatticeShift) : 1 - ε' ≤
        ∑ x ∈ T,
          (translateCylinderLaw (cubeStateToCylinderState L) a P x).toReal := by
      let P' := translatePlaquettes a P
      let T' := (curvatureCoordinateBox_finite (P := P') K).toFinset
      have hT'set : (T' : Set (P' → ℤ)) = curvatureCoordinateBox (P := P') K :=
        (curvatureCoordinateBox_finite (P := P') K).coe_toFinset
      have hsrc := hK P' (translatePlaquettes_card a P)
      have hsrcMeasure : 1 - ε' ≤
          ((L.law P').toMeasure (curvatureCoordinateBox (P := P') K)).toReal := by
        rw [← hT'set, pmf_toReal_measure_finset]
        simpa [T'] using hsrc
      have hdstMeasure : 1 - ε' ≤
          ((translateCylinderLaw (cubeStateToCylinderState L) a P).toMeasure
            (curvatureCoordinateBox (P := P) K)).toReal := by
        rw [translateCylinderLaw_box_measure]
        exact hsrcMeasure
      rw [← pmf_toReal_measure_finset _ T]
      simpa [T, hTset] using hdstMeasure
    refine ⟨T, ?_⟩
    intro k
    have haverage := finiteShiftAverage_tight_of_uniform_tight (s k)
      (fun a => translateCylinderLaw (cubeStateToCylinderState L) a P)
      T hε'lt hsingle
    exact le_trans (by linarith : 1 - ε ≤ 1 - ε') haverage
  have hsq (k : ℕ) : Summable (fun x => (pn k x).toReal * (f x) ^ 2) := by
    have hfour := averagedCylinderLaw_sourceFilling_fourthMoment_bound
      hβ L μ hμ σ hfill (s k)
    have hnorm := pmf_summable_norm_of_integrable (p := pn k)
      (f := fun x => (sourceFillingCurvaturePairing σ x) ^ 4) (by
        simpa [pn] using hfour.1)
    refine hnorm.congr ?_
    intro x
    rw [Real.norm_of_nonneg (by positivity :
      0 ≤ (sourceFillingCurvaturePairing σ x) ^ 4)]
    simp only [f]
    congr 1
    ring
  have hsqBound (k : ℕ) : ∑' x, (pn k x).toReal * (f x) ^ 2 ≤ C := by
    have hfour := averagedCylinderLaw_sourceFilling_fourthMoment_bound
      hβ L μ hμ σ hfill (s k)
    have hsum :
        ∫ x, (sourceFillingCurvaturePairing σ x) ^ 4 ∂(pn k).toMeasure =
          ∑' x, (pn k x).toReal *
            (sourceFillingCurvaturePairing σ x) ^ 4 := by
      simpa [smul_eq_mul] using PMF.integral_eq_tsum (pn k)
        (fun x => (sourceFillingCurvaturePairing σ x) ^ 4) (by
          simpa [pn] using hfour.1)
    calc
      _ = ∑' x, (pn k x).toReal *
          (sourceFillingCurvaturePairing σ x) ^ 4 := by
            apply tsum_congr
            intro x
            dsimp [f]
            congr 1
            ring
      _ = ∫ x, (sourceFillingCurvaturePairing σ x) ^ 4 ∂(pn k).toMeasure :=
        hsum.symm
      _ ≤ C := by simpa [C, pn] using hfour.2
  have hlimSq := pmf_secondMoment_bound_of_pointwise
    pn p f C hpoint' hsq hsqBound
  have hmass := spectral_pmf_mass_summable p
  have hYoung (x : P → ℤ) : f x ≤ 1 + (f x) ^ 2 := by
    nlinarith [sq_nonneg (f x - 1 / 2)]
  have hweight : Summable (fun x => (p x).toReal * f x) := by
    apply Summable.of_nonneg_of_le
      (fun x => mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _))
    · intro x
      exact mul_le_mul_of_nonneg_left (hYoung x) ENNReal.toReal_nonneg
    · simpa [mul_add] using hmass.add hlimSq.1
  have hnorm : Summable (fun x => (p x).toReal * ‖f x‖) := by
    refine hweight.congr ?_
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hInt : Integrable f p.toMeasure := pmf_integrable_of_summable_norm hnorm
  have hIntSeq (k : ℕ) : Integrable f (pn k).toMeasure := by
    have hparts (a : LatticeShift) : Integrable f
        (translateCylinderLaw (cubeStateToCylinderState L) a P).toMeasure := by
      simpa [f, P] using translateCylinderLaw_sourceFilling_square_integrable
        (rootBeta_pos hβ) L σ a
    simpa [pn, averagedCylinderLaw, f] using (finiteShiftAverage_integral (s k)
      (fun a => translateCylinderLaw (cubeStateToCylinderState L) a P) f hparts).1
  have hsumSeq (k : ℕ) :
      ∫ x, f x ∂(pn k).toMeasure = ∑' x, (pn k x).toReal * f x := by
    simpa [smul_eq_mul] using PMF.integral_eq_tsum (pn k) f (hIntSeq k)
  have hsumLim : ∫ x, f x ∂p.toMeasure = ∑' x, (p x).toReal * f x := by
    simpa [smul_eq_mul] using PMF.integral_eq_tsum p f hInt
  have hweightConv := pmf_weighted_tsum_tendsto_of_tight_secondMoment
    pn p f C hpoint' htight (fun x => sq_nonneg _) hsq hsqBound
  have hIntConv : Tendsto (fun k => ∫ x, f x ∂(pn k).toMeasure) atTop
      (𝓝 (∫ x, f x ∂p.toMeasure)) := by
    have hseq : (fun k => ∫ x, f x ∂(pn k).toMeasure) =
        (fun k => ∑' x, (pn k x).toReal * f x) := funext hsumSeq
    rw [hseq, hsumLim]
    exact hweightConv
  have hlow (k : ℕ) :
      betaDoublePrime rootPackingCoefficient β * fourierGreenQuadratic μ ≤
        ∫ x, f x ∂(pn k).toMeasure := by
    simpa [pn, f] using
      (averagedCylinderLaw_sourceFilling_secondMoment_bounds
        hβ L σ μ hμ hfill (s k)).1
  have hupp (k : ℕ) :
      ∫ x, f x ∂(pn k).toMeasure ≤ β * fourierGreenQuadratic μ := by
    simpa [pn, f] using
      (averagedCylinderLaw_sourceFilling_secondMoment_bounds
        hβ L σ μ hμ hfill (s k)).2
  refine ⟨hInt, ?_⟩
  constructor
  · exact le_of_tendsto_of_tendsto tendsto_const_nhds hIntConv
      (Filter.Eventually.of_forall hlow)
  · exact le_of_tendsto_of_tendsto hIntConv tendsto_const_nhds
      (Filter.Eventually.of_forall hupp)

theorem averagedCylinderState_shift_error
    (ν : CurvatureCylinderState) (b : LatticeShift)
    (P : Finset GlobalIntegerPlaquette) (x : P → ℤ) :
    Tendsto
      (fun n =>
        (translateCylinderLaw (averagedCylinderState ν n) b P x).toReal -
          ((averagedCylinderState ν n).law P x).toReal)
      atTop (𝓝 0) := by
  have hstable : AveragedCylinderShiftStable b :=
    latticeShift_mem_averagedCylinderStableShifts b
  have h := hstable ν P x
  have heq (n : ℕ) :
      (translateCylinderLaw (averagedCylinderState ν n) b P x).toReal -
          ((averagedCylinderState ν n).law P x).toReal =
        (shiftedCylinderAverage ν b n P x).toReal -
          (shiftedCylinderAverage ν 0 n P x).toReal := by
    rw [translateAveragedCylinderLaw]
    rw [shiftedCylinderAverage_zero]
    rfl
  exact h.congr' (Filter.Eventually.of_forall fun n => (heq n).symm)


theorem cubeState_averagedCylinderLaw_tight
    {β : ℝ} (hβ : 0 < β) (L : CubeCurvatureLimitState β hβ)
    (P : Finset GlobalIntegerPlaquette) (ε : ℝ) (hε : 0 < ε) :
    ∃ S : Finset (P → ℤ), ∀ n,
      1 - ε ≤ ∑ x ∈ S, (averagedCylinderLaw (cubeStateToCylinderState L) n P x).toReal := by
  classical
  let ε' := min ε (1 / 2)
  have hε'pos : 0 < ε' := by dsimp [ε']; positivity
  have hε'le : ε' ≤ ε := min_le_left _ _
  have hε'lt : ε' < 1 := by dsimp [ε']; norm_num
  obtain ⟨K, hK⟩ := cubeCurvatureLimitState_uniform_box_tight hβ L P ε' hε'pos
  let S := (curvatureCoordinateBox_finite (P := P) K).toFinset
  have hS : (S : Set (P → ℤ)) = curvatureCoordinateBox (P := P) K :=
    (curvatureCoordinateBox_finite (P := P) K).coe_toFinset
  have hsingle (a : LatticeShift) :
      1 - ε' ≤ ∑ x ∈ S,
        (translateCylinderLaw (cubeStateToCylinderState L) a P x).toReal := by
    let P' := translatePlaquettes a P
    let S' := (curvatureCoordinateBox_finite (P := P') K).toFinset
    have hS' : (S' : Set (P' → ℤ)) = curvatureCoordinateBox (P := P') K :=
      (curvatureCoordinateBox_finite (P := P') K).coe_toFinset
    have hsrc := hK P' (translatePlaquettes_card a P)
    have hsrcMeasure : 1 - ε' ≤
        ((L.law P').toMeasure (curvatureCoordinateBox (P := P') K)).toReal := by
      rw [← hS', pmf_toReal_measure_finset]
      simpa [S'] using hsrc
    have hdstMeasure : 1 - ε' ≤
        ((translateCylinderLaw (cubeStateToCylinderState L) a P).toMeasure
          (curvatureCoordinateBox (P := P) K)).toReal := by
      rw [translateCylinderLaw_box_measure]
      exact hsrcMeasure
    rw [← pmf_toReal_measure_finset _ S]
    simpa [S, hS] using hdstMeasure
  refine ⟨S, ?_⟩
  intro n
  have haverage := finiteShiftAverage_tight_of_uniform_tight n
    (fun a => translateCylinderLaw (cubeStateToCylinderState L) a P) S hε'lt hsingle
  exact le_trans (by linarith : 1 - ε ≤ 1 - ε') haverage

/--
A projective subsequential limit of the Følner-averaged cylinder laws.
-/
theorem exists_averagedCylinderLimit (ν : CurvatureCylinderState)
    (htight : ∀ (P : Finset GlobalIntegerPlaquette) (ε : ℝ), 0 < ε →
      ∃ S : Finset (P → ℤ), ∀ n,
        1 - ε ≤ ∑ x ∈ S, (averagedCylinderLaw ν n P x).toReal) :
    ∃ s : ℕ → ℕ, StrictMono s ∧
      ∃ L : CurvatureCylinderState,
        (∀ P x, Tendsto (fun k => (averagedCylinderLaw ν (s k) P x).toReal)
          atTop (𝓝 ((L.law P x).toReal))) := by
  classical
  let laws : ℕ → (P : Finset GlobalIntegerPlaquette) → PMF (P → ℤ) :=
    fun n P => averagedCylinderLaw ν n P
  obtain ⟨s, hs, limits, hconv, hpmf⟩ :=
    exists_subseq_cylinderPMF laws (fun P ε hε => htight P ε hε)
  let Llaw : (P : Finset GlobalIntegerPlaquette) → PMF (P → ℤ) :=
    fun P => Classical.choose (hpmf P)
  have hLlaw (P : Finset GlobalIntegerPlaquette) (x : P → ℤ) :
      Llaw P x = ENNReal.ofReal (cylinderLimitValue limits ⟨P, x⟩) :=
    Classical.choose_spec (hpmf P) x
  have hpoint (P : Finset GlobalIntegerPlaquette) (x : P → ℤ) :
      Tendsto (fun k => (laws (s k) P x).toReal) atTop
        (𝓝 ((Llaw P x).toReal)) := by
    have hpi := (tendsto_pi_nhds.mp hconv)
      (show CylinderIndex GlobalIntegerPlaquette from ⟨P, x⟩)
    have hval := continuous_subtype_val.continuousAt.tendsto.comp hpi
    change Tendsto (fun k => (laws (s k) P x).toReal) atTop
      (𝓝 (cylinderLimitValue limits ⟨P, x⟩)) at hval
    rw [hLlaw, ENNReal.toReal_ofReal (cylinderLimitValue_nonneg limits ⟨P, x⟩)]
    exact hval
  have hcons (P₀ P₁ : Finset GlobalIntegerPlaquette) (hP : P₀ ⊆ P₁) :
      PMF.map (restrictCurvature hP) (Llaw P₁) = Llaw P₀ := by
    ext y
    have hmap : Tendsto
        (fun k => (PMF.map (restrictCurvature hP) (laws (s k) P₁) y).toReal)
        atTop (𝓝 ((PMF.map (restrictCurvature hP) (Llaw P₁) y).toReal)) := by
      apply pmf_map_apply_tendsto_of_tight
      · intro x
        exact hpoint P₁ x
      · intro ε hε
        obtain ⟨S, hS⟩ := htight P₁ ε hε
        exact ⟨S, fun k => hS (s k)⟩
    have hsmall : Tendsto (fun k => (laws (s k) P₀ y).toReal) atTop
        (𝓝 ((Llaw P₀ y).toReal)) := hpoint P₀ y
    have heq : ∀ k, (PMF.map (restrictCurvature hP) (laws (s k) P₁) y).toReal =
        (laws (s k) P₀ y).toReal := by
      intro k
      rw [averagedCylinderLaw_consistent ν (s k) P₀ P₁ hP]
    have hmap' : Tendsto (fun k => (laws (s k) P₀ y).toReal) atTop
        (𝓝 ((PMF.map (restrictCurvature hP) (Llaw P₁) y).toReal)) :=
      hmap.congr' (Filter.Eventually.of_forall heq)
    have hreal := tendsto_nhds_unique hmap' hsmall
    exact (ENNReal.toReal_eq_toReal_iff'
      (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp hreal
  refine ⟨s, hs, ⟨Llaw, hcons⟩, ?_⟩
  intro P x
  exact hpoint P x

/-- Følner averaging has a translation-invariant projective limit whenever
its finite-cylinder marginals are uniformly tight and their fixed-shift
boundary errors vanish. The latter is the quantitative Følner estimate for
the chosen finite shift boxes. -/
theorem exists_invariant_averagedCylinderLimit (ν : CurvatureCylinderState)
    (htight : ∀ (P : Finset GlobalIntegerPlaquette) (ε : ℝ), 0 < ε →
      ∃ S : Finset (P → ℤ), ∀ n,
        1 - ε ≤ ∑ x ∈ S, (averagedCylinderLaw ν n P x).toReal)
    (hshift : ∀ (a : LatticeShift) (P : Finset GlobalIntegerPlaquette)
      (x : P → ℤ), Tendsto
        (fun n => (translateCylinderLaw (averagedCylinderState ν n) a P x).toReal -
          ((averagedCylinderState ν n).law P x).toReal)
        atTop (𝓝 0)) :
    ∃ s : ℕ → ℕ, StrictMono s ∧
      ∃ L : CurvatureCylinderState,
        (∀ P x, Tendsto (fun k => (averagedCylinderLaw ν (s k) P x).toReal)
          atTop (𝓝 ((L.law P x).toReal))) ∧
        ∀ a P, translateCylinderLaw L a P = L.law P := by
  classical
  obtain ⟨s, hs, L, hpoint⟩ := exists_averagedCylinderLimit ν htight
  have hsTop : Tendsto s atTop atTop := hs.tendsto_atTop
  have hinvariant (a : LatticeShift) (P : Finset GlobalIntegerPlaquette) :
      translateCylinderLaw L a P = L.law P := by
    apply PMF.ext
    intro x
    have htranslated : Tendsto
        (fun k => (translateCylinderLaw (averagedCylinderState ν (s k)) a P x).toReal)
        atTop (𝓝 ((translateCylinderLaw L a P x).toReal)) := by
      unfold translateCylinderLaw
      apply pmf_map_apply_tendsto_of_tight
      · intro y
        exact hpoint (translatePlaquettes a P) y
      · intro ε hε
        obtain ⟨S, hS⟩ := htight (translatePlaquettes a P) ε hε
        exact ⟨S, fun k => hS (s k)⟩
    have havg : Tendsto
        (fun k => ((averagedCylinderState ν (s k)).law P x).toReal)
        atTop (𝓝 ((L.law P x).toReal)) := hpoint P x
    have herror : Tendsto
        (fun k =>
          (translateCylinderLaw (averagedCylinderState ν (s k)) a P x).toReal -
            ((averagedCylinderState ν (s k)).law P x).toReal)
        atTop (𝓝 0) := (hshift a P x).comp hsTop
    have hdiff := htranslated.sub havg
    have hlim := tendsto_nhds_unique hdiff herror
    have hreal : (translateCylinderLaw L a P x).toReal = (L.law P x).toReal := by
      linarith
    exact (ENNReal.toReal_eq_toReal_iff'
      (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp hreal
  exact ⟨s, hs, L, hpoint, hinvariant⟩


theorem exists_translationInvariantCylinderLimit_with_secondMomentBounds
    {β : ℝ} (hβ : rootBetaThreshold ≤ β)
    (L : CubeCurvatureLimitState β (rootBeta_pos hβ)) :
    ∃ s : ℕ → ℕ, StrictMono s ∧
      ∃ S : CurvatureCylinderState,
        (∀ P x, Tendsto
          (fun k => (averagedCylinderLaw (cubeStateToCylinderState L) (s k) P x).toReal)
          atTop (𝓝 ((S.law P x).toReal))) ∧
        (∀ a P, translateCylinderLaw S a P = S.law P) ∧
        (∀ (μ : GlobalLinkField) (_hμ : globallyCoClosed μ)
          (σ : GlobalPlaquetteField)
          (_hfill : globalBoundary (σ : RealLatticeChain 4) =
            (μ : RealLatticeChain 4)),
          betaDoublePrime rootPackingCoefficient β * fourierGreenQuadratic μ ≤
              ∫ x, (sourceFillingCurvaturePairing σ x) ^ 2 ∂
                (S.law (fillingCurvatureIndexSet σ)).toMeasure ∧
            (∫ x, (sourceFillingCurvaturePairing σ x) ^ 2 ∂
                (S.law (fillingCurvatureIndexSet σ)).toMeasure) ≤
              β * fourierGreenQuadratic μ) := by
  have htight : ∀ (P : Finset GlobalIntegerPlaquette) (ε : ℝ), 0 < ε →
      ∃ T : Finset (P → ℤ), ∀ n,
        1 - ε ≤ ∑ x ∈ T,
          (averagedCylinderLaw (cubeStateToCylinderState L) n P x).toReal := by
    intro P ε hε
    exact cubeState_averagedCylinderLaw_tight (rootBeta_pos hβ) L P ε hε
  have hshift : ∀ (a : LatticeShift) (P : Finset GlobalIntegerPlaquette)
      (x : P → ℤ), Tendsto
        (fun n => (translateCylinderLaw
            (averagedCylinderState (cubeStateToCylinderState L) n) a P x).toReal -
          ((averagedCylinderState (cubeStateToCylinderState L) n).law P x).toReal)
        atTop (𝓝 0) := by
    intro a P x
    exact averagedCylinderState_shift_error
      (cubeStateToCylinderState L) a P x
  obtain ⟨s, hs, S, hpoint, hinvariant⟩ :=
    exists_invariant_averagedCylinderLimit
      (cubeStateToCylinderState L) htight hshift
  refine ⟨s, hs, S, hpoint, hinvariant, ?_⟩
  intro μ _hμ σ _hfill
  exact (projectiveAveragedCylinderLimit_sourceFilling_secondMoment_bounds
    hβ L s S hpoint μ _hμ σ _hfill).2

end FroehlichSpencer.FS82.Infinite.Nonsummability

end
