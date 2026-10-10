/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Wilson.PerimeterDualityUnfold
public import FroehlichSpencer.FS82.Root.SourceMoment
public import FroehlichSpencer.FS82.Gaussian.LatticePoincare
public import FroehlichSpencer.FS82.Wilson.LoopCovariance

/-!
# exact integer dual two-fields and the tree-gauge chord model

The first root works with `sourceDualMoment`, a ratio of
sums over integer fields on the chords of the rooted tree.

This module identifies the two.

The integer differential `sourceIntegerDualOneDifferential` is the star-oriented one, while the
complex `sourceLatticeComplex`, its Hodge matrix and the rooted tree are written in the C2-twisted
variable `b = Tα`.

So a chord field `n` is sent to the differential of the link field
`e ↦ sourceDualT e · (extendChord n) e`.

* `chordGaugeClassEquiv`: chord fields are in bijection with the exact two-fields.

Injectivity is
  exactness of the complex at degree one plus the tree gauge; surjectivity is the tree
  normalization of a link field.
* `chordGaugeClass_normSq`: `‖dα‖²` is the reduced chord quadratic form.
* `chordGaugeClass_pairing`: `⟨dα, σ⟩` is the chord pairing with the co-closed test `d₁†σ`.
* `sourceDiscreteDualExpectation_eq_sourceDualMoment`: the two ratios agree, at `t = −1/β`.
-/

open scoped BigOperators
open Matrix
open FroehlichSpencer.FS82.Gaussian
open FroehlichSpencer.FS82.Poisson
open FroehlichSpencer.FS82.Moment.SourceConstructor
open FroehlichSpencer.FS82.Root

@[expose] public section

namespace FroehlichSpencer.FS82.Wilson

noncomputable section

variable {B : Cubical.Box 4}

/-! ### The integer differential and the real complex -/

/-- On a dual two-cell, the cast of the integer differential is the real star-oriented `D₁` of the
cast field. -/
theorem sourceIntegerDualOneDifferential_cast (a : SourceDualOneCells B →₀ ℤ)
    (f : SourceDualTwoCells B) :
    ((sourceIntegerDualOneDifferential a f.1 : ℤ) : ℝ) =
      sourceDualD₁ (finsuppToEuclidean (castIntegerFinsupp a)) f := by
  have h1 : castIntegerFinsupp (sourceIntegerDualOneDifferential a) =
      Cubical.dualExteriorDifference
        (embedDualSubtype sourceDualOneEmbedding (castIntegerFinsupp a)) := by
    unfold sourceIntegerDualOneDifferential
    rw [castIntegerDualExteriorDifference]
    congr 1
    exact castSourceIntegerDualOneChain a
  have h2 := sourceDualD₁_embed_eq_derivative (finsuppToEuclidean (castIntegerFinsupp a))
  have h3 : sourceDualOneToChain (finsuppToEuclidean (castIntegerFinsupp a)) =
      embedDualSubtype sourceDualOneEmbedding (castIntegerFinsupp a) := by
    simp [sourceDualOneToChain, euclideanToFinsupp_finsuppToEuclidean]
  rw [h3] at h2
  have h4 := congrArg (fun q : Cubical.DualRealChain 4 B => q f.1) (h1.trans h2.symm)
  have hL : castIntegerFinsupp (sourceIntegerDualOneDifferential a) f.1 =
      ((sourceIntegerDualOneDifferential a f.1 : ℤ) : ℝ) := by
    simp [castIntegerFinsupp]
  have hR : sourceDualTwoToChain
      (sourceDualD₁ (finsuppToEuclidean (castIntegerFinsupp a))) f.1 =
      sourceDualD₁ (finsuppToEuclidean (castIntegerFinsupp a)) f := by
    change embedDualSubtype sourceDualTwoEmbedding
      (euclideanToFinsupp (sourceDualD₁ (finsuppToEuclidean (castIntegerFinsupp a))))
      (sourceDualTwoEmbedding f) = _
    rw [embedDualSubtype_apply_at_image]
    rfl
  rw [← hL, ← hR]
  exact h4

/-- The star-oriented integer link field of an integer field in the twisted variable. -/
def starLinkField (b : SourceDualOneCells B → ℤ) : SourceDualOneCells B →₀ ℤ :=
  Finsupp.equivFunOnFinite.symm (fun e => sourceDualT e * b e)

/-- The real field of an integer link field. -/
def realLinkField (b : SourceDualOneCells B → ℤ) : EuclideanSpace ℝ (SourceDualOneCells B) :=
  WithLp.toLp 2 (fun e => ((b e : ℤ) : ℝ))

theorem starLinkField_cast (b : SourceDualOneCells B → ℤ) :
    finsuppToEuclidean (castIntegerFinsupp (starLinkField b)) =
      sourceDualTLinear (realLinkField b) := by
  ext e
  rw [finsuppToEuclidean_apply, sourceDualTLinear_apply]
  simp [starLinkField, realLinkField, castIntegerFinsupp, sourceDualT_cast_eq_orientationSign]

/-- The differential of `starLinkField b` is `d₁` of the real field of `b`. -/
theorem starLinkField_differential_cast (b : SourceDualOneCells B → ℤ)
    (f : SourceDualTwoCells B) :
    ((sourceIntegerDualOneDifferential (starLinkField b) f.1 : ℤ) : ℝ) =
      (sourceLatticeComplex (B := B)).d₁ (realLinkField b) f := by
  rw [sourceIntegerDualOneDifferential_cast, starLinkField_cast]
  rfl

/-- Every star-oriented integer link field is the twist of an integer field. -/
theorem starLinkField_twist (a : SourceDualOneCells B →₀ ℤ) :
    starLinkField (fun e => sourceDualT e * a e) = a := by
  ext e
  have hsq : sourceDualT e * sourceDualT e = 1 := by
    rcases sourceDualT_is_pm_one e with h | h <;> simp [h]
  simp only [starLinkField, Finsupp.equivFunOnFinite_symm_apply_apply]
  rw [← mul_assoc, hsq, one_mul]

/-- Two twisted fields with the same real `d₁` have the same integer differential. -/
theorem sourceIntegerDualOneDifferential_eq_of_d₁_eq (b b' : SourceDualOneCells B → ℤ)
    (h : (sourceLatticeComplex (B := B)).d₁ (realLinkField b) =
      (sourceLatticeComplex (B := B)).d₁ (realLinkField b')) :
    sourceIntegerDualOneDifferential (starLinkField b) =
      sourceIntegerDualOneDifferential (starLinkField b') := by
  ext c
  by_cases hc : Cubical.dualCellDegree c = 2
  · have hcast := (starLinkField_differential_cast b ⟨c, hc⟩).trans
      ((congrArg (fun y : EuclideanSpace ℝ (SourceDualTwoCells B) => y.ofLp ⟨c, hc⟩) h).trans
        (starLinkField_differential_cast b' ⟨c, hc⟩).symm)
    exact_mod_cast hcast
  · have h0 : ∀ a : SourceDualOneCells B →₀ ℤ, sourceIntegerDualOneDifferential a c = 0 := by
      intro a
      by_contra hne
      exact hc ((dualIntegerHomogeneousSupport_iff _ 2).mp
        (sourceIntegerDualOneDifferential_homogeneousSupport a) c
        (Finsupp.mem_support_iff.mpr hne))
    rw [h0, h0]

/-! ### Chord fields and exact two-fields -/

/-- The exact integer dual two-field of a chord field: the differential of its C2-twisted
extension by zero on the tree. -/
def chordGaugeClass (n : (sourceRootedTree B).Chord → ℤ) : SourceIntegerDualGaugeClass B :=
  ⟨sourceIntegerDualOneDifferential (starLinkField ((sourceRootedTree B).extendChord n)),
    ⟨_, rfl⟩⟩

theorem chordGaugeClass_cast (n : (sourceRootedTree B).Chord → ℤ) (f : SourceDualTwoCells B) :
    (((chordGaugeClass n).1 f.1 : ℤ) : ℝ) =
      (sourceLatticeComplex (B := B)).d₁
        (realLinkField ((sourceRootedTree B).extendChord n)) f :=
  starLinkField_differential_cast _ f

theorem extendChord_treeEdge (n : (sourceRootedTree B).Chord → ℤ)
    (w : {x : SourcePoissonVertex B // x ≠ (sourceRootedTree B).root}) :
    (sourceRootedTree B).extendChord n ((sourceRootedTree B).treeEdge w) = 0 := by
  have htree : (sourceRootedTree B).treeEdge w ∈ Set.range (sourceRootedTree B).treeEdge :=
    ⟨w, rfl⟩
  rw [RootedTreeGauge.extendChord, dite_eq_left htree]

/-- **Injectivity.** Two chord fields with the same exact two-field differ by a gradient that
vanishes on the tree, hence by zero. -/
theorem chordGaugeClass_injective : Function.Injective (chordGaugeClass (B := B)) := by
  intro n n' h
  let T := sourceRootedTree B
  let C := sourceLatticeComplex (B := B)
  have hd : C.d₁ (realLinkField (T.extendChord n) - realLinkField (T.extendChord n')) = 0 := by
    rw [map_sub, sub_eq_zero]
    ext f
    have h1 := chordGaugeClass_cast n f
    have h2 := chordGaugeClass_cast n' f
    rw [h] at h1
    exact h1.symm.trans h2
  obtain ⟨u, hu⟩ := C.exactOne (LinearMap.mem_ker.mpr hd)
  let p := sourceTreeZeroPotential B u
  have hgraph : sourceGraphField p =
      realLinkField (T.extendChord n) - realLinkField (T.extendChord n') :=
    (sourceLatticeD0_eq_sourceGraphField Cubical.originZero u).symm.trans hu
  have hpTree : ∀ w : {x : SourcePoissonVertex B // x ≠ T.root},
      T.coboundary p (T.treeEdge w) = 0 := by
    intro w
    have he := congrArg
      (fun x : EuclideanSpace ℝ (SourceDualOneCells B) => x.ofLp (T.treeEdge w)) hgraph
    change T.coboundary p (T.treeEdge w) =
      (((T.extendChord n (T.treeEdge w) : ℤ) : ℝ)) - ((T.extendChord n' (T.treeEdge w) : ℤ) : ℝ)
      at he
    rw [extendChord_treeEdge, extendChord_treeEdge] at he
    simpa using he
  have hconst := T.potential_constant_of_tree_zero p hpTree
  have hzero : realLinkField (T.extendChord n) - realLinkField (T.extendChord n') = 0 := by
    rw [← hgraph]
    ext e
    change T.coboundary p e = 0
    unfold RootedTreeGauge.coboundary
    rw [hconst (T.edgeTarget e), hconst (T.edgeSource e), sub_self]
  have hext : T.extendChord n = T.extendChord n' := by
    funext e
    have he := congrArg (fun x : EuclideanSpace ℝ (SourceDualOneCells B) => x.ofLp e)
      (sub_eq_zero.mp hzero)
    change ((T.extendChord n e : ℤ) : ℝ) = ((T.extendChord n' e : ℤ) : ℝ) at he
    exact_mod_cast he
  calc n = T.restrictChord (T.extendChord n) := (T.restrict_extendChord n).symm
    _ = T.restrictChord (T.extendChord n') := by rw [hext]
    _ = n' := T.restrict_extendChord n'

/-- **Surjectivity.** The tree normalization of the twisted link field has the same differential,
and it is the extension of its chord restriction. -/
theorem chordGaugeClass_surjective : Function.Surjective (chordGaugeClass (B := B)) := by
  rintro ⟨x, a, rfl⟩
  let T := sourceRootedTree B
  let C := sourceLatticeComplex (B := B)
  let b : SourceDualOneCells B → ℤ := fun e => sourceDualT e * a e
  obtain ⟨p, hp0, hp⟩ := T.normalize_gaugeEquivalent b
  refine ⟨T.restrictChord (T.normalize b), ?_⟩
  apply Subtype.ext
  change sourceIntegerDualOneDifferential
      (starLinkField (T.extendChord (T.restrictChord (T.normalize b)))) =
    sourceIntegerDualOneDifferential a
  rw [T.extend_restrictChord T.normalize_mem]
  conv_rhs => rw [← starLinkField_twist a]
  apply sourceIntegerDualOneDifferential_eq_of_d₁_eq
  let pr : SourcePoissonVertex B → ℝ := fun v => ((p v : ℤ) : ℝ)
  have hfield : realLinkField (T.normalize b) = realLinkField b - sourceGraphField pr := by
    ext e
    change ((T.normalize b e : ℤ) : ℝ) =
      ((b e : ℤ) : ℝ) - (pr (T.edgeTarget e) - pr (T.edgeSource e))
    rw [hp e]
    simp [RootedTreeGauge.coboundary, pr]
  have hpr : sourceTreeZeroPotential B (sourceTreeVertexPotential B pr) = pr := by
    have hnorm : sourceNormalizePotential pr = pr := by
      funext v
      have h0 : pr none = 0 := by
        change ((p T.root : ℤ) : ℝ) = 0
        rw [hp0]
        simp
      simp [sourceNormalizePotential, h0]
    have h := sourceTreeVertexPotential_normalize pr
    rwa [hnorm] at h
  have hgraph : C.d₀ (sourceTreeVertexPotential B pr) = sourceGraphField pr := by
    rw [sourceLatticeD0_eq_sourceGraphField, hpr]
  have hzero : C.d₁ (C.d₀ (sourceTreeVertexPotential B pr)) = 0 := by
    have h := congrArg (fun g : EuclideanSpace ℝ (SourceDualZeroCells B) →ₗ[ℝ]
      EuclideanSpace ℝ (SourceDualTwoCells B) => g (sourceTreeVertexPotential B pr)) C.complex
    simpa using h
  change C.d₁ (realLinkField (T.normalize b)) = C.d₁ (realLinkField b)
  rw [hfield, map_sub, ← hgraph, hzero, sub_zero]

/-- **The chord parametrization of the exact integer dual two-fields.** -/
def chordGaugeClassEquiv :
    ((sourceRootedTree B).Chord → ℤ) ≃ SourceIntegerDualGaugeClass B :=
  Equiv.ofBijective chordGaugeClass ⟨chordGaugeClass_injective, chordGaugeClass_surjective⟩

@[simp] theorem chordGaugeClassEquiv_apply (n : (sourceRootedTree B).Chord → ℤ) :
    chordGaugeClassEquiv n = chordGaugeClass n := rfl

/-! ### Energy and pairing in chord coordinates -/

/-- The pairing of an exact two-field with an integer dual chain is a sum over the dual
two-cells. -/
theorem chordGaugeClass_pairing_eq_sum (n : (sourceRootedTree B).Chord → ℤ)
    (y : DualIntegerChain B) :
    integerDualPairing (chordGaugeClass n).1 y =
      ∑ f : SourceDualTwoCells B,
        (sourceLatticeComplex (B := B)).d₁
          (realLinkField ((sourceRootedTree B).extendChord n)) f * ((y f.1 : ℤ) : ℝ) := by
  classical
  unfold integerDualPairing
  have hx0 : ∀ c : Cubical.DualCell 4 B, Cubical.dualCellDegree c ≠ 2 →
      (chordGaugeClass n).1 c = 0 := by
    intro c hc
    by_contra hne
    exact hc ((dualIntegerHomogeneousSupport_iff _ 2).mp
      (sourceIntegerDualOneDifferential_homogeneousSupport _) c
      (Finsupp.mem_support_iff.mpr hne))
  rw [← Finset.sum_subset (Finset.subset_univ
      (Finset.univ.filter fun c : Cubical.DualCell 4 B => Cubical.dualCellDegree c = 2))
    (fun c _ hc => by
      have hdeg : Cubical.dualCellDegree c ≠ 2 := fun h =>
        hc (Finset.mem_filter.mpr ⟨Finset.mem_univ c, h⟩)
      rw [hx0 c hdeg]
      simp)]
  rw [Finset.sum_subtype (p := fun c : Cubical.DualCell 4 B => Cubical.dualCellDegree c = 2)
    (Finset.univ.filter fun c : Cubical.DualCell 4 B => Cubical.dualCellDegree c = 2)
    (fun c => by simp)
    (fun c => (((chordGaugeClass n).1 c : ℤ) : ℝ) * ((y c : ℤ) : ℝ))]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [chordGaugeClass_cast]

/-- The squared norm of the exact two-field of a chord field. -/
theorem chordGaugeClass_normSq (n : (sourceRootedTree B).Chord → ℤ) :
    integerDualNormSq (chordGaugeClass n).1 =
      ‖(sourceLatticeComplex (B := B)).d₁
        (realLinkField ((sourceRootedTree B).extendChord n))‖ ^ 2 := by
  unfold integerDualNormSq
  rw [chordGaugeClass_pairing_eq_sum, EuclideanSpace.norm_sq_eq]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [chordGaugeClass_cast, Real.norm_eq_abs, sq_abs]
  ring

theorem chordEmbedding_mulVec_eq_realLinkField (n : (sourceRootedTree B).Chord → ℤ) :
    (chordEmbeddingMatrix (sourceRootedTree B)).mulVec (fun c => ((n c : ℤ) : ℝ)) =
      fun e => (realLinkField ((sourceRootedTree B).extendChord n)).ofLp e := by
  classical
  funext e
  by_cases ht : e ∈ Set.range (sourceRootedTree B).treeEdge
  · obtain ⟨w, rfl⟩ := ht
    rw [chordEmbeddingMatrix_mulVec_at_tree]
    change (0 : ℝ) = (((sourceRootedTree B).extendChord n
      ((sourceRootedTree B).treeEdge w) : ℤ) : ℝ)
    rw [extendChord_treeEdge]
    simp
  · let c : (sourceRootedTree B).Chord := ⟨e, ht⟩
    have hc := chordEmbeddingMatrix_mulVec_at_chord (sourceRootedTree B)
      (fun c => ((n c : ℤ) : ℝ)) c
    change (chordEmbeddingMatrix (sourceRootedTree B)).mulVec (fun c => ((n c : ℤ) : ℝ)) e =
      (((sourceRootedTree B).extendChord n e : ℤ) : ℝ)
    rw [RootedTreeGauge.extendChord, dite_eq_right ht]
    simpa [c] using hc

/-- The reduced chord quadratic form is the squared norm of `d₁` of the extended field. -/
theorem reducedChord_quadratic_eq_d₁_normSq (n : (sourceRootedTree B).Chord → ℤ) :
    dotProduct (fun c => ((n c : ℤ) : ℝ))
        ((reducedChordMatrix (sourceRootedTree B)
          (sourceFinitePoissonModel (B := B) Cubical.originZero)).mulVec
            (fun c => ((n c : ℤ) : ℝ))) =
      ‖(sourceLatticeComplex (B := B)).d₁
        (realLinkField ((sourceRootedTree B).extendChord n))‖ ^ 2 := by
  let T := sourceRootedTree B
  let M := sourceFinitePoissonModel (B := B) Cubical.originZero
  let τ := realLinkField (T.extendChord n)
  have hEmb := chordEmbedding_mulVec_eq_realLinkField n
  have hK : M.K.mulVec (fun e => τ.ofLp e) =
      (latticeStencilOperator Cubical.originZero τ).ofLp :=
    sourcePoissonMatrix_mulVec Cubical.originZero (fun e => τ.ofLp e)
  calc dotProduct (fun c => ((n c : ℤ) : ℝ))
        ((reducedChordMatrix T M).mulVec (fun c => ((n c : ℤ) : ℝ)))
      = dotProduct ((chordEmbeddingMatrix T).mulVec (fun c => ((n c : ℤ) : ℝ)))
          (M.K.mulVec ((chordEmbeddingMatrix T).mulVec (fun c => ((n c : ℤ) : ℝ)))) :=
        reducedChord_energy_eq T M (fun c => ((n c : ℤ) : ℝ))
    _ = inner ℝ τ (latticeStencilOperator Cubical.originZero τ) := by
        rw [hEmb, hK, PiLp.inner_apply, dotProduct]
        simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
    _ = ‖(sourceLatticeComplex (B := B)).d₁ τ‖ ^ 2 :=
        latticeStencil_inner_eq_d1_norm_sq Cubical.originZero τ

/-- The Gaussian weight of an exact two-field is the tree-gauge chord weight. -/
theorem chordGaugeClass_weight {β : ℝ} (hβ : 0 < β) (τ : (sourceRootedTree B).Chord → ℝ)
    (n : (sourceRootedTree B).Chord → ℤ) :
    sourceDualGaugeClassWeight β (chordGaugeClass n) =
      dualPrimalWeight (sourceChordMatrix (B := B) β) τ 0 n := by
  let T := sourceRootedTree B
  let R := reducedChordMatrix T (sourceFinitePoissonModel (B := B) Cubical.originZero)
  have hquad : (∑ i : T.Chord, ∑ j : T.Chord,
        ((n i : ℤ) : ℝ) * sourceChordMatrix (B := B) β i j * ((n j : ℤ) : ℝ)) =
      (1 / (2 * Real.pi * β)) *
        dotProduct (fun q => ((n q : ℤ) : ℝ)) (R.mulVec (fun q => ((n q : ℤ) : ℝ))) := by
    rw [show sourceChordMatrix (B := B) β = ((2 * Real.pi * β)⁻¹) • R from rfl]
    simp only [dotProduct, Matrix.mulVec, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    field_simp
  unfold sourceDualGaugeClassWeight dualPrimalWeight
  rw [hquad, reducedChord_quadratic_eq_d₁_normSq, chordGaugeClass_normSq]
  congr 1
  have hpi := Real.pi_ne_zero
  field_simp
  ring

/-! ### The observable and the moment -/

/-- The co-closed test form of a real dual two-form `s`: `d₁† s` (FS82: `δσ`). -/
def sheetTest (s : EuclideanSpace ℝ (SourceDualTwoCells B)) : SourceW B :=
  ⟨(sourceLatticeComplex (B := B)).d₁.adjoint s, adjoint_mem_coClosed _ s⟩

/-- A sum against a field in tree gauge is a sum over the chords. -/
theorem weighted_sum_treeGauge_chords {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    [DecidableEq E] (T : RootedTreeGauge V E) (a : E → ℤ) (b : E → ℝ)
    (ha : RootedTreeGauge.InTreeGauge T a) :
    (∑ e : E, ((a e : ℤ) : ℝ) * b e) = ∑ c : T.Chord, ((a c.1 : ℤ) : ℝ) * b c.1 := by
  classical
  calc (∑ e : E, ((a e : ℤ) : ℝ) * b e)
      = ∑ s : T.Chord ⊕ {x : V // x ≠ T.root},
          ((a ((T.edgeSplitEquiv).symm s) : ℤ) : ℝ) * b ((T.edgeSplitEquiv).symm s) :=
        (Equiv.sum_comp (T.edgeSplitEquiv).symm (fun e => ((a e : ℤ) : ℝ) * b e)).symm
    _ = (∑ c : T.Chord, ((a c.1 : ℤ) : ℝ) * b c.1) +
        ∑ x : {x : V // x ≠ T.root}, ((a (T.treeEdge x) : ℤ) : ℝ) * b (T.treeEdge x) := by
        rw [Fintype.sum_sum_type]
        simp only [RootedTreeGauge.edgeSplitEquiv_symm_inl,
          RootedTreeGauge.edgeSplitEquiv_symm_inr]
    _ = ∑ c : T.Chord, ((a c.1 : ℤ) : ℝ) * b c.1 := by
        have htree : (∑ x : {x : V // x ≠ T.root},
            ((a (T.treeEdge x) : ℤ) : ℝ) * b (T.treeEdge x)) = 0 := by
          refine Finset.sum_eq_zero fun x _ => ?_
          rw [ha x]
          simp
        rw [htree, add_zero]

/-- The pairing of an exact two-field with an integer dual two-form is the chord pairing with the
test `d₁†σ`. -/
theorem chordGaugeClass_pairing (q : SourceIntegerDualTwoField B)
    (n : (sourceRootedTree B).Chord → ℤ) :
    integerDualPairing (chordGaugeClass n).1 (sourceIntegerDualTwoChain q) =
      ∑ c : (sourceRootedTree B).Chord,
        sourceChordTest (sheetTest (finsuppToEuclidean (castIntegerFinsupp q))) c *
          ((n c : ℤ) : ℝ) := by
  classical
  let T := sourceRootedTree B
  let C := sourceLatticeComplex (B := B)
  let s : EuclideanSpace ℝ (SourceDualTwoCells B) := finsuppToEuclidean (castIntegerFinsupp q)
  let r := realLinkField (T.extendChord n)
  have hq : ∀ f : SourceDualTwoCells B,
      ((sourceIntegerDualTwoChain q f.1 : ℤ) : ℝ) = s.ofLp f := by
    intro f
    have h1 : sourceIntegerDualTwoChain q f.1 = q f := by
      change Finsupp.embDomain sourceDualTwoEmbedding q (sourceDualTwoEmbedding f) = q f
      exact Finsupp.embDomain_apply_self _ _ _
    rw [h1]
    simp [s, castIntegerFinsupp]
  have hinner : (∑ f : SourceDualTwoCells B, C.d₁ r f * s.ofLp f) = inner ℝ (C.d₁.adjoint s) r := by
    rw [LinearMap.adjoint_inner_left, PiLp.inner_apply]
    simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial]
  have hchord : inner ℝ (C.d₁.adjoint s) r =
      ∑ c : T.Chord, ((T.extendChord n c.1 : ℤ) : ℝ) * (C.d₁.adjoint s).ofLp c.1 := by
    rw [PiLp.inner_apply]
    simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial]
    have htree : RootedTreeGauge.InTreeGauge T (T.extendChord n) := fun w =>
      extendChord_treeEdge n w
    exact weighted_sum_treeGauge_chords T (T.extendChord n)
      (fun e => (C.d₁.adjoint s).ofLp e) htree
  rw [chordGaugeClass_pairing_eq_sum]
  simp_rw [hq]
  rw [hinner, hchord]
  refine Finset.sum_congr rfl fun c _ => ?_
  have hn : T.extendChord n c.1 = n c := congrFun (T.restrict_extendChord n) c
  rw [hn, mul_comm]
  rfl


theorem sourceDiscreteDualExpectation_eq_sourceDualMoment {β : ℝ} (hβ : 0 < β)
    (q : SourceIntegerDualTwoField B) :
    sourceDiscreteDualExpectation β (sourceIntegerDualTwoChain q) =
      sourceDualMoment β (sheetTest (finsuppToEuclidean (castIntegerFinsupp q))) (-1 / β) := by
  rw [sourceDiscreteDualExpectation_eq_tsum_div]
  unfold sourceDualMoment dualMoment
  congr 1
  · rw [← Equiv.tsum_eq chordGaugeClassEquiv]
    refine tsum_congr fun n => ?_
    rw [chordGaugeClassEquiv_apply, chordGaugeClass_weight hβ
      (sourceChordTest (sheetTest (finsuppToEuclidean (castIntegerFinsupp q)))) n]
    unfold sourceDualGaugeClassObservable dualPrimalWeight
    rw [chordGaugeClass_pairing, ← Real.exp_add]
    congr 1
    ring
  · rw [← Equiv.tsum_eq chordGaugeClassEquiv]
    exact tsum_congr fun n => chordGaugeClass_weight hβ _ n

end

end FroehlichSpencer.FS82.Wilson

end
