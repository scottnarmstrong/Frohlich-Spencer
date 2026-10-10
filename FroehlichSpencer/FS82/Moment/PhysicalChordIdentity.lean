/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Moment.ExpansionIntegral
public import FroehlichSpencer.FS82.Moment.GaugeWeight
public import FroehlichSpencer.FS82.Poisson.PerAssignment

/-!
# FS82 physical-to-chord assignment identity
-/

@[expose] public section

set_option linter.style.haveILetI false

open scoped BigOperators InnerProductSpace
open Matrix

namespace FroehlichSpencer.FS82.Moment.PhysicalChordIdentity

open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Currents
open FroehlichSpencer.FS82.Gaussian
open FroehlichSpencer.FS82.Gaussian.GaugeAveraged
open FroehlichSpencer.FS82.Moment.GaugeCharacter
open FroehlichSpencer.FS82.Moment.GaugeWeight
open FroehlichSpencer.FS82.Moment.PhysicalGaugeCurrent
open FroehlichSpencer.FS82.Moment.QuotientGaussian
open FroehlichSpencer.FS82.Moment.SourceCoercivity
open FroehlichSpencer.FS82.Moment.ExpansionIntegral
open FroehlichSpencer.FS82.Poisson

variable {B : Box 4}

noncomputable abbrev srcTree (B : Box 4) := sourceRootedTree B
noncomputable abbrev srcComplex (B : Box 4) := physicalComplex (B := B)

/-- The physical co-closed test in tree-link coordinates. -/
noncomputable def physicalTestChord
    (τ : coClosed (srcComplex B)) : (srcTree B).Chord → ℝ :=
  (srcTree B).restrictChord (fun e => τ.1 e)

private theorem physicalTest_rootedCoClosed (τ : coClosed (srcComplex B)) :
    RootedTreeGauge.CoClosed (srcTree B) (fun e => τ.1 e) := by
  apply (RootedTreeGauge.coClosed_iff_orthogonalToCoboundaries (srcTree B)
    (fun e => τ.1 e)).2
  intro p
  let u := sourceTreeVertexPotential B (sourceNormalizePotential p)
  have hfield (e : SourcePoissonEdge B) :
      ((srcComplex B).d₀ u).ofLp e =
        RootedTreeGauge.coboundary (srcTree B) p e := by
    change (sourceDualTLinear (sourceDualD₀ u)).ofLp e = _
    rw [sourceDualT_D0_eq_treeCoboundary]
    calc
      sourceTreeCoboundary B (sourceTreeZeroPotential B u) e =
          sourceTreeCoboundary B (sourceNormalizePotential p) e := by
            rw [sourceTreeVertexPotential_normalize]
      _ = sourceTreeCoboundary B p e := sourceTreeCoboundary_normalize p e
  have hker : (srcComplex B).d₀.adjoint τ.1 = 0 :=
    LinearMap.mem_ker.mp τ.2
  have hinner : inner ℝ τ.1 ((srcComplex B).d₀ u) = 0 := by
    calc
      inner ℝ τ.1 ((srcComplex B).d₀ u) =
          inner ℝ ((srcComplex B).d₀ u) τ.1 := real_inner_comm _ _
      _ = inner ℝ u ((srcComplex B).d₀.adjoint τ.1) :=
        (LinearMap.adjoint_inner_right (srcComplex B).d₀ u τ.1).symm
      _ = 0 := by rw [hker]; simp
  have hsum : inner ℝ τ.1 ((srcComplex B).d₀ u) =
      ∑ e : SourcePoissonEdge B, τ.1 e *
        RootedTreeGauge.coboundary (srcTree B) p e := by
    rw [PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro e he
    rw [hfield, Real.inner_apply]
  rw [← hsum]
  exact hinner

private theorem physicalCurrent_divergence_to_rootedCoClosed
    (j : SourcePoissonEdge B → ℤ)
    (hdiv : currentDivergence (physicalGaugeCurrent (B := B) j) = 0) :
    RootedTreeGauge.CoClosed (srcTree B) j := by
  have hreal : RootedTreeGauge.CoClosed (srcTree B)
      (fun e => (j e : ℝ)) := by
    apply (RootedTreeGauge.coClosed_iff_orthogonalToCoboundaries
      (srcTree B) (fun e => (j e : ℝ))).2
    intro p
    let u := sourceTreeVertexPotential B (sourceNormalizePotential p)
    have hfield (e : SourcePoissonEdge B) :
        ((srcComplex B).d₀ u).ofLp e =
          RootedTreeGauge.coboundary (srcTree B) p e := by
      change (sourceDualTLinear (sourceDualD₀ u)).ofLp e = _
      rw [sourceDualT_D0_eq_treeCoboundary]
      calc
        sourceTreeCoboundary B (sourceTreeZeroPotential B u) e =
            sourceTreeCoboundary B (sourceNormalizePotential p) e := by
              rw [sourceTreeVertexPotential_normalize]
        _ = sourceTreeCoboundary B p e := sourceTreeCoboundary_normalize p e
    let W := sourcePhysicalCurrentCoClosed Cubical.originZero
      (physicalGaugeCurrent (B := B) j) hdiv
    have hker : (srcComplex B).d₀.adjoint
        (W : EuclideanSpace ℝ (SourceDualOneCells B)) = 0 :=
      LinearMap.mem_ker.mp W.2
    have hinner : inner ℝ (W : EuclideanSpace ℝ (SourceDualOneCells B))
        ((srcComplex B).d₀ u) = 0 := by
      calc
        inner ℝ (W : EuclideanSpace ℝ (SourceDualOneCells B))
            ((srcComplex B).d₀ u) =
            inner ℝ ((srcComplex B).d₀ u)
              (W : EuclideanSpace ℝ (SourceDualOneCells B)) :=
          real_inner_comm _ _
        _ =
            inner ℝ u ((srcComplex B).d₀.adjoint
              (W : EuclideanSpace ℝ (SourceDualOneCells B))) :=
          (LinearMap.adjoint_inner_right (srcComplex B).d₀ u
            (W : EuclideanSpace ℝ (SourceDualOneCells B))).symm
        _ = 0 := by rw [hker]; simp
    have hmode : latticeIntegerModeVector (B := B)
        (physicalGaugeCurrent (B := B) j) = gaugeRealVector (B := B) j := by
      calc
        latticeIntegerModeVector (B := B)
            (physicalGaugeCurrent (B := B) j) =
            sourceDualTLinear (sourceRealLinkVector (B := B)
              (physicalGaugeCurrent (B := B) j)) :=
          latticeIntegerModeVector_eq_orientedSourceVector (B := B) _
        _ = sourceDualTLinear
            (sourceDualTLinear (gaugeRealVector (B := B) j)) := by
          have hreal : sourceRealLinkVector (B := B)
              (physicalGaugeCurrent (B := B) j) =
              WithLp.toLp 2 (fun e : SourceDualOneCells B =>
                ((physicalGaugeCurrent (B := B) j e : ℤ) : ℝ)) := by
            ext e
            simp [sourceRealLinkVector_apply]
          rw [hreal, physicalGaugeCurrentRealVector_eq_T (B := B) j]
        _ = gaugeRealVector (B := B) j :=
          sourceDualTLinear_apply_apply (gaugeRealVector (B := B) j)
    have hW := sourcePhysicalCurrentCoClosed_eq_two_pi_mode
      (B := B) (j := physicalGaugeCurrent (B := B) j) hdiv
    rw [hmode] at hW
    have hsum : inner ℝ (W : EuclideanSpace ℝ (SourceDualOneCells B))
        ((srcComplex B).d₀ u) = (2 * Real.pi) *
          ∑ e : SourcePoissonEdge B, (j e : ℝ) *
            RootedTreeGauge.coboundary (srcTree B) p e := by
      rw [hW, real_inner_smul_left, PiLp.inner_apply]
      apply congrArg
      apply Finset.sum_congr rfl
      intro e he
      rw [hfield]
      simp [gaugeRealVector]
      ring
    have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    exact (mul_eq_zero.mp (hsum.symm.trans hinner)).resolve_left hpi
  intro v hv
  have h := hreal v hv
  have hcast : (((srcTree B).divergence j v : ℤ) : ℝ) = 0 := by
    simpa [RootedTreeGauge.divergence, map_sum, Int.cast_ite] using h
  exact_mod_cast hcast

private theorem physicalGaugeCurrent_modeVector_eq
    (j : SourcePoissonEdge B → ℤ) :
    latticeIntegerModeVector (B := B)
        (physicalGaugeCurrent (B := B) j) = gaugeRealVector (B := B) j := by
  calc
    latticeIntegerModeVector (B := B) (physicalGaugeCurrent (B := B) j) =
        sourceDualTLinear (sourceRealLinkVector (B := B)
          (physicalGaugeCurrent (B := B) j)) :=
      latticeIntegerModeVector_eq_orientedSourceVector (B := B) _
    _ = sourceDualTLinear (sourceDualTLinear (gaugeRealVector (B := B) j)) := by
      have hreal : sourceRealLinkVector (B := B)
          (physicalGaugeCurrent (B := B) j) =
          WithLp.toLp 2 (fun e : SourceDualOneCells B =>
            ((physicalGaugeCurrent (B := B) j e : ℤ) : ℝ)) := by
        ext e
        simp [sourceRealLinkVector_apply]
      rw [hreal, physicalGaugeCurrentRealVector_eq_T (B := B) j]
    _ = gaugeRealVector (B := B) j :=
      sourceDualTLinear_apply_apply (gaugeRealVector (B := B) j)

private theorem sourceVΛ_rootedPairing
    (μ τ : coClosed (srcComplex B)) :
    inner ℝ (τ.1 : EuclideanSpace ℝ (SourceDualOneCells B))
      (latticeVΛ (B := B) Cubical.originZero μ :
        EuclideanSpace ℝ (SourceDualOneCells B)) =
      dotProduct (physicalTestChord τ)
        ((reducedChordMatrix (srcTree B) (sourceFinitePoissonModel (B := B)
          Cubical.originZero))⁻¹ *ᵥ physicalTestChord μ) := by
  classical
  let M := sourceFinitePoissonModel (B := B) Cubical.originZero
  let u : SourcePoissonEdge B → ℝ := fun e =>
    (latticeVΛ (B := B) Cubical.originZero μ :
      EuclideanSpace ℝ (SourceDualOneCells B)) e
  have hsolve : M.K.mulVec u = fun e => μ.1 e := by
    change (sourcePoissonMatrix (B := B) Cubical.originZero).mulVec u = _
    rw [sourcePoissonMatrix_mulVec]
    have hinv := latticeVΛ_inverse_stencil
      (B := B) Cubical.originZero μ
    funext e
    have hcoord := congrArg (fun x : EuclideanSpace ℝ
      (SourceDualOneCells B) => x.ofLp e) hinv
    simpa [u, Gaussian.latticeStencilOperator] using hcoord
  have hvar := finiteModel_variational_identity_of_solution (srcTree B) M
    (physicalTest_rootedCoClosed μ) (physicalTest_rootedCoClosed τ) u hsolve
  calc
    inner ℝ (τ.1 : EuclideanSpace ℝ (SourceDualOneCells B))
        (latticeVΛ (B := B) Cubical.originZero μ :
          EuclideanSpace ℝ (SourceDualOneCells B)) =
        dotProduct (fun e => τ.1 e) u := by
          simp only [PiLp.inner_apply, dotProduct, u, Real.inner_apply]
    _ = dotProduct (physicalTestChord τ)
        ((reducedChordMatrix (srcTree B) M)⁻¹ *ᵥ physicalTestChord μ) := by
          exact hvar

private theorem dotProduct_mulVec_inv_symmetric
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : Matrix ι ι ℝ) (hR : R.PosDef) (x y : ι → ℝ) :
    dotProduct x (R⁻¹ *ᵥ y) = dotProduct y (R⁻¹ *ᵥ x) := by
  have hsym : R⁻¹.IsSymm := hR.isHermitian.inv.isSymm
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have hji : R⁻¹ j i = R⁻¹ i j := by
    have hh := congrArg (fun Q : Matrix ι ι ℝ => Q i j) hsym
    simpa [Matrix.transpose_apply] using hh
  rw [hji]
  ring

private theorem complex_matrix_quadratic_expand
    {ι : Type*} [Fintype ι]
    (M : Matrix ι ι ℂ) (hM : M.IsSymm) (x y : ι → ℂ) :
    (∑ i, ∑ j, (x i - Complex.I * y i) * M i j *
        (x j - Complex.I * y j)) =
      (∑ i, ∑ j, x i * M i j * x j) -
        2 * Complex.I * (∑ i, ∑ j, x i * M i j * y j) -
        (∑ i, ∑ j, y i * M i j * y j) := by
  have hsymm (i j : ι) : M j i = M i j := by
    have hh := congrArg (fun Q : Matrix ι ι ℂ => Q i j) hM
    simpa [Matrix.transpose_apply] using hh
  have hcross : (∑ i, ∑ j, y i * M i j * x j) =
      ∑ i, ∑ j, x i * M i j * y j := by
    calc
      _ = ∑ j, ∑ i, y i * M i j * x j := by rw [Finset.sum_comm]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        rw [hsymm i j]
        ring
  have hcrossRight : (∑ i, ∑ j, x i * M i j * (Complex.I * y j)) =
      Complex.I * (∑ i, ∑ j, x i * M i j * y j) := by
    calc
      _ = ∑ i, ∑ j, Complex.I * (x i * M i j * y j) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = ∑ i, Complex.I * (∑ j, x i * M i j * y j) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [← Finset.mul_sum]
      _ = _ := by rw [← Finset.mul_sum]
  have hyy : (∑ i, ∑ j, (Complex.I * y i) * M i j * (Complex.I * y j)) =
      -(∑ i, ∑ j, y i * M i j * y j) := by
    calc
      _ = ∑ i, ∑ j, -(y i * M i j * y j) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        calc
          (Complex.I * y i) * M i j * (Complex.I * y j) =
              Complex.I * Complex.I * (y i * M i j * y j) := by ring_nf
          _ = -(y i * M i j * y j) := by simp [Complex.I_mul_I]
      _ = _ := by simp only [← Finset.sum_neg_distrib]
  calc
    _ = ∑ i : ι, ∑ j : ι,
        ((x i * M i j * x j) - (x i * M i j * (Complex.I * y j)) -
          ((Complex.I * y i) * M i j * x j) +
          ((Complex.I * y i) * M i j * (Complex.I * y j))) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = (∑ i : ι, ∑ j : ι, x i * M i j * x j) -
          (∑ i, ∑ j, x i * M i j * (Complex.I * y j)) -
          (∑ i, ∑ j, (Complex.I * y i) * M i j * x j) +
          (∑ i, ∑ j, (Complex.I * y i) * M i j * (Complex.I * y j)) := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    _ = (∑ i, ∑ j, x i * M i j * x j) -
          2 * Complex.I * (∑ i, ∑ j, x i * M i j * y j) -
          (∑ i, ∑ j, y i * M i j * y j) := by
      have hxy (a b : ι → ℂ) :
          (∑ i : ι, ∑ j : ι, (Complex.I * a i) * M i j * b j) =
            Complex.I * (∑ i : ι, ∑ j : ι, a i * M i j * b j) := by
        calc
          _ = ∑ i : ι, ∑ j : ι, Complex.I * (a i * M i j * b j) := by
            apply Finset.sum_congr rfl
            intro i hi
            apply Finset.sum_congr rfl
            intro j hj
            ring
          _ = ∑ i : ι, Complex.I * (∑ j : ι, a i * M i j * b j) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [← Finset.mul_sum]
          _ = _ := by rw [← Finset.mul_sum]
      rw [hcrossRight, hxy y x, hcross, hyy]
      ring

private theorem dualQuadraticExp_scaledChord
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (β : ℝ) (_hβ : 0 < β) (A R : Matrix ι ι ℝ)
    (hAinv : A⁻¹ = (2 * Real.pi * β) • R⁻¹)
    (hR : R.PosDef) (x : ι → ℝ) (t : ℝ) (k : ι → ℤ) :
    dualQuadraticExp A (realTiltParameter x t) k =
      Complex.exp
        (((β / 2) * (t ^ 2 * dotProduct x (R⁻¹ *ᵥ x) : ℝ) : ℂ) +
          Complex.I * ((-2 * Real.pi * β * t *
            dotProduct x (R⁻¹ *ᵥ fun i => (k i : ℝ)) : ℝ) : ℂ) +
          ((-2 * Real.pi ^ 2 * β *
            dotProduct (fun i => (k i : ℝ))
              (R⁻¹ *ᵥ fun i => (k i : ℝ)) : ℝ) : ℂ)) := by
  classical
  have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hpic : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hsym : R⁻¹.IsSymm := hR.isHermitian.inv.isSymm
  unfold dualQuadraticExp
  apply congrArg Complex.exp
  let Q : Matrix ι ι ℂ := fun i j => ((A⁻¹ i j : ℝ) : ℂ)
  have hQ : Q.IsSymm := by
    have hInv : R⁻¹.IsSymm := hR.isHermitian.inv.isSymm
    apply Matrix.ext
    intro i j
    have hh := congrArg (fun Z : Matrix ι ι ℝ => Z i j) hInv
    have hji : R⁻¹ j i = R⁻¹ i j := by
      simpa [Matrix.transpose_apply] using hh
    change ((A⁻¹ j i : ℝ) : ℂ) = ((A⁻¹ i j : ℝ) : ℂ)
    rw [hAinv]
    simp [Matrix.smul_apply, hji]
  change (Real.pi : ℂ) * ∑ i, ∑ j,
    (realTiltParameter x t i - Complex.I * (k i : ℂ)) * Q i j *
      (realTiltParameter x t j - Complex.I * (k j : ℂ)) = _
  rw [complex_matrix_quadratic_expand Q hQ
    (realTiltParameter x t) (fun i => (k i : ℂ))]
  simp [Q, realTiltParameter, hAinv, Matrix.smul_apply,
    dotProduct, Matrix.mulVec, Finset.mul_sum]
  field_simp [hpi, hpic]
  ring_nf
  simp_rw [Finset.mul_sum]
  conv_lhs => rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  conv_rhs => rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  conv_lhs => rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  conv_rhs => rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  field_simp [hpic]

private theorem physicalCompletedSquare_eq_chordExp
    (β : ℝ) (hβ : 0 < β) (t : ℝ)
    (τ : coClosed (srcComplex B)) (m : SourcePoissonEdge B → ℤ)
    (hm : RootedTreeGauge.CoClosed (srcTree B) m) :
    physicalGaussianTiltCompletedSquareFactor (B := B) β hβ.le t τ
      (physicalGaugeCurrent (B := B) (fun e => -m e)) =
    dualQuadraticExp
      (scaledChordMatrix (srcTree B)
        (sourceFinitePoissonModel (B := B) Cubical.originZero) β)
      (realTiltParameter (physicalTestChord τ) t)
      ((srcTree B).restrictChord m) := by
  classical
  let T := srcTree B
  let M := sourceFinitePoissonModel (B := B) Cubical.originZero
  let R := reducedChordMatrix T M
  let A := scaledChordMatrix T M β
  let x := physicalTestChord τ
  let k : T.Chord → ℤ := T.restrictChord m
  have hneg : RootedTreeGauge.CoClosed T (fun e => -m e) := by
    intro v hv
    have htarget : (∑ e : SourcePoissonEdge B,
        if T.edgeTarget e = v then -m e else 0) =
        -(∑ e : SourcePoissonEdge B,
          if T.edgeTarget e = v then m e else 0) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro e he
      split_ifs <;> simp
    have hsource : (∑ e : SourcePoissonEdge B,
        if T.edgeSource e = v then -m e else 0) =
        -(∑ e : SourcePoissonEdge B,
          if T.edgeSource e = v then m e else 0) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro e he
      split_ifs <;> simp
    unfold RootedTreeGauge.divergence
    rw [htarget, hsource]
    have h := hm v hv
    change (∑ e : SourcePoissonEdge B,
        if T.edgeTarget e = v then m e else 0) -
      (∑ e : SourcePoissonEdge B,
        if T.edgeSource e = v then m e else 0) = 0 at h
    linarith
  have hdiv := physicalGaugeCurrent_divergence_zero (B := B)
    (fun e => -m e) hneg
  have hR : R.PosDef := by
    dsimp [R, T, M]
    exact reducedChordMatrix_posDef (sourceRootedTree B)
      (sourceFinitePoissonModel (B := B) Cubical.originZero)
  have hc : (2 * Real.pi * β : ℝ) ≠ 0 := by positivity
  have hdet : IsUnit R.det :=
    (Matrix.isUnit_iff_isUnit_det R).mp hR.isUnit
  have hAinv : A⁻¹ = (2 * Real.pi * β) • R⁻¹ := by
    letI : Invertible ((2 * Real.pi * β)⁻¹) :=
      invertibleOfNonzero (inv_ne_zero hc)
    change (((2 * Real.pi * β)⁻¹) • R)⁻¹ = _
    rw [Matrix.inv_smul R ((2 * Real.pi * β)⁻¹) hdet]
    simp
  have hxx := sourceVΛ_rootedPairing τ τ
  let hμ : coClosed (srcComplex B) :=
    sourcePhysicalCurrentCoClosed Cubical.originZero
      (physicalGaugeCurrent (B := B) (fun e => -m e)) hdiv
  have hμval : (hμ : EuclideanSpace ℝ (SourceDualOneCells B)) =
      (-2 * Real.pi) • gaugeRealVector (B := B) m := by
    have hmode := sourcePhysicalCurrentCoClosed_eq_two_pi_mode
      (B := B) (physicalGaugeCurrent (B := B) (fun e => -m e)) hdiv
    rw [physicalGaugeCurrent_modeVector_eq] at hmode
    rw [hmode]
    ext e
    simp [gaugeRealVector, PiLp.smul_apply, smul_eq_mul]
  have hμcoords : physicalTestChord hμ = fun c =>
      (-2 * Real.pi) * (T.restrictChord (fun e => (m e : ℝ))) c := by
    funext c
    simp [physicalTestChord, hμval, gaugeRealVector, PiLp.smul_apply,
      smul_eq_mul, RootedTreeGauge.restrictChord]
  have hxm := sourceVΛ_rootedPairing hμ τ
  have hcross : inner ℝ (τ : EuclideanSpace ℝ (SourceDualOneCells B))
      (latticeVΛ (B := B) Cubical.originZero hμ :
        EuclideanSpace ℝ (SourceDualOneCells B)) =
      (-2 * Real.pi) * dotProduct x (R⁻¹ *ᵥ fun c => (k c : ℝ)) := by
    rw [hxm, hμcoords]
    change dotProduct x (R⁻¹ *ᵥ fun c =>
        (-2 * Real.pi) * T.restrictChord (fun e => (m e : ℝ)) c) = _
    have hvec : (fun c => (-2 * Real.pi) *
        T.restrictChord (fun e => (m e : ℝ)) c) =
        (-2 * Real.pi) • (fun c => (k c : ℝ)) := by
      funext c
      simp [k, RootedTreeGauge.restrictChord]
    rw [hvec, Matrix.mulVec_smul, dotProduct_smul]
    rfl
  have hchar := sourceGaugePhysicalCharacter_eq_dualGaussianWeight
    (B := B) β hβ (fun e => -m e) hneg
  have hchar' : sourcePhysicalGaussianCharacter (B := B) β
      (physicalGaugeCurrent (B := B) (fun e => -m e)) hdiv =
      dualGaussianWeight A k := by
    simpa [A, k, T, M, RootedTreeGauge.restrictChord,
      dualGaussianWeight, dotProduct, Matrix.mulVec] using hchar
  have htilt := dualQuadraticExp_scaledChord β hβ A R hAinv hR x t k
  have hzero := dualQuadraticExp_scaledChord β hβ A R hAinv hR x 0 k
  have hweightExp : (dualGaussianWeight A k : ℂ) =
      Complex.exp ((-2 * Real.pi ^ 2 * β *
        dotProduct (fun i => (k i : ℝ))
          (R⁻¹ *ᵥ fun i => (k i : ℝ)) : ℝ) : ℂ) := by
    have hzArg : realTiltParameter x 0 = 0 := by
      funext i
      simp [realTiltParameter]
    rw [hzArg] at hzero
    change dualQuadraticExp A 0 k = _ at hzero
    have hzero' : dualQuadraticExp A 0 k = Complex.exp
        ((-2 * Real.pi ^ 2 * β *
          dotProduct (fun i => (k i : ℝ))
            (R⁻¹ *ᵥ fun i => (k i : ℝ)) : ℝ) : ℂ) := by
      simpa [realTiltParameter] using hzero
    exact (dualGaussianWeight_eq A k).symm.trans hzero'
  have hfirst : ((β / 2) * (t ^ 2 *
      inner ℝ τ (latticeVΛ (B := B) Cubical.originZero τ)) : ℝ) =
      (β / 2) * (t ^ 2 * dotProduct x (R⁻¹ *ᵥ x)) := by
    change ((β / 2) * (t ^ 2 *
      inner ℝ (τ : EuclideanSpace ℝ (SourceDualOneCells B))
        (latticeVΛ (B := B) Cubical.originZero τ)) : ℝ) = _
    rw [hxx]
  have hsecond : (β * t *
      inner ℝ τ (latticeVΛ (B := B) Cubical.originZero
        (sourcePhysicalCurrentCoClosed Cubical.originZero
          (physicalGaugeCurrent (B := B) (fun e => -m e)) hdiv)) : ℝ) =
      -2 * Real.pi * β * t *
        dotProduct x (R⁻¹ *ᵥ fun i => (k i : ℝ)) := by
    change (β * t * inner ℝ
      (τ : EuclideanSpace ℝ (SourceDualOneCells B))
      (latticeVΛ (B := B) Cubical.originZero hμ) : ℝ) = _
    rw [hcross]
    ring
  have hfirstCast : (((β / 2) * (t ^ 2 *
      inner ℝ τ (latticeVΛ (B := B) Cubical.originZero τ)) : ℝ) : ℂ) =
      (((β / 2) * (t ^ 2 * dotProduct x (R⁻¹ *ᵥ x)) : ℝ) : ℂ) :=
    congrArg Complex.ofReal hfirst
  have hsecondCast : Complex.I *
      ((β * t * inner ℝ τ (latticeVΛ (B := B) Cubical.originZero
        (sourcePhysicalCurrentCoClosed Cubical.originZero
          (physicalGaugeCurrent (B := B) (fun e => -m e)) hdiv)) : ℝ) : ℂ) =
      Complex.I * ((-2 * Real.pi * β * t *
        dotProduct x (R⁻¹ *ᵥ fun i => (k i : ℝ)) : ℝ) : ℂ) := by
    exact congrArg (fun z : ℂ => Complex.I * z) (congrArg Complex.ofReal hsecond)
  unfold physicalGaussianTiltCompletedSquareFactor
  simp only [hdiv, ↓reduceDIte]
  rw [hchar', hweightExp]
  push_cast at hfirstCast hsecondCast
  rw [hfirstCast, hsecondCast]
  rw [← Complex.exp_add]
  convert htilt.symm using 1
  push_cast
  ring_nf

private abbrev PhysicalClosedPattern (q : SourcePoissonEdge B → ℕ) :=
  {s : SourcePoissonEdge B → Option Bool //
    RootedTreeGauge.CoClosed (srcTree B) (sourceAssignmentCurrent q s)}

private abbrev GaugeAssignmentFiber (q : SourcePoissonEdge B → ℕ) :=
  {b : GaugeCharacterBranch (srcTree B) // GaugeCharacterBranch.assignment b = q}

private def flipSelection (s : Option Bool) : Option Bool :=
  match s with
  | none => none
  | some true => some false
  | some false => some true

private noncomputable def branchSourcePattern (b : GaugeCharacterBranch (srcTree B)) :
    SourcePoissonEdge B → Option Bool :=
  fun e => flipSelection (ModeBranch.selectionCode
    (fun j : {j : SourcePoissonEdge B → ℤ //
      RootedTreeGauge.CoClosed (srcTree B) j} => j.1) b e)

private theorem sourceAssignmentCurrent_eq_neg_branchCurrent
    (q : SourcePoissonEdge B → ℕ) (b : GaugeCharacterBranch (srcTree B))
    (hb : GaugeCharacterBranch.assignment b = q) :
    sourceAssignmentCurrent q (branchSourcePattern b) =
      fun e => -GaugeCharacterBranch.current b e := by
  classical
  funext e
  change sourceAssignmentCurrent q (branchSourcePattern b) e = -(b.1.1 e)
  have hassign := congrFun hb e
  change ModeBranch.assignment
      (fun j : {j : SourcePoissonEdge B → ℤ //
        RootedTreeGauge.CoClosed (srcTree B) j} => j.1) b = q at hb
  change ModeBranch.assignment
      (fun j : {j : SourcePoissonEdge B → ℤ //
        RootedTreeGauge.CoClosed (srcTree B) j} => j.1) b e = q e at hassign
  by_cases hz : GaugeCharacterBranch.current b e = 0
  · have hz' : b.1.1 e = 0 := by simpa [GaugeCharacterBranch.current] using hz
    simp [sourceAssignmentCurrent, sourceAssignmentSignedMode,
      branchSourcePattern, flipSelection, ModeBranch.selectionCode,
      hz']
  · have hnat : (GaugeCharacterBranch.current b e).natAbs - 1 = q e := by
      have hz' : b.1.1 e ≠ 0 := by
        simpa [GaugeCharacterBranch.current] using hz
      simpa [ModeBranch.assignment, GaugeCharacterBranch.current, hz'] using hassign
    have habs : (GaugeCharacterBranch.current b e).natAbs = q e + 1 := by omega
    by_cases hpos : 0 < GaugeCharacterBranch.current b e
    · have hcast : GaugeCharacterBranch.current b e = ((q e + 1 : ℕ) : ℤ) := by
        have hc : ((GaugeCharacterBranch.current b e).natAbs : ℤ) =
            ((q e + 1 : ℕ) : ℤ) := by exact_mod_cast habs
        rw [Int.natAbs_of_nonneg (by omega : 0 ≤ GaugeCharacterBranch.current b e)] at hc
        exact hc
      have hcast' : b.1.1 e = ((q e + 1 : ℕ) : ℤ) := by
        simpa [GaugeCharacterBranch.current] using hcast
      have hnotzero : (q e : ℤ) + 1 ≠ 0 := by omega
      simp [sourceAssignmentCurrent, sourceAssignmentSignedMode,
        branchSourcePattern, flipSelection, ModeBranch.selectionCode,
        sourceAssignmentFrequency, positiveMode, hcast', hnotzero]
    · have hneg : GaugeCharacterBranch.current b e < 0 := by omega
      have hcast : GaugeCharacterBranch.current b e = -((q e + 1 : ℕ) : ℤ) := by
        have hc : ((-(GaugeCharacterBranch.current b e)).natAbs : ℤ) =
            ((q e + 1 : ℕ) : ℤ) := by
          have hn : (-(GaugeCharacterBranch.current b e)).natAbs =
              (GaugeCharacterBranch.current b e).natAbs := by rw [Int.natAbs_neg]
          exact_mod_cast hn.trans habs
        rw [Int.natAbs_of_nonneg (by omega : 0 ≤ -GaugeCharacterBranch.current b e)] at hc
        omega
      have hcast' : b.1.1 e = -((q e + 1 : ℕ) : ℤ) := by
        simpa [GaugeCharacterBranch.current] using hcast
      have hnotzero : (-1 : ℤ) + -(q e : ℤ) ≠ 0 := by omega
      have hdecide : ¬ (q e : ℤ) < -1 := by omega
      simp [sourceAssignmentCurrent, sourceAssignmentSignedMode,
        branchSourcePattern, flipSelection, ModeBranch.selectionCode,
        sourceAssignmentFrequency, positiveMode, hcast', hnotzero, hdecide]

private theorem rootedCoClosed_neg
    (j : SourcePoissonEdge B → ℤ)
    (hj : RootedTreeGauge.CoClosed (srcTree B) j) :
    RootedTreeGauge.CoClosed (srcTree B) (fun e => -j e) := by
  intro v hv
  have h := hj v hv
  have htarget : (∑ e : SourcePoissonEdge B,
      if (srcTree B).edgeTarget e = v then -j e else 0) =
      -(∑ e : SourcePoissonEdge B,
        if (srcTree B).edgeTarget e = v then j e else 0) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro e he
    split_ifs <;> simp
  have hsource : (∑ e : SourcePoissonEdge B,
      if (srcTree B).edgeSource e = v then -j e else 0) =
      -(∑ e : SourcePoissonEdge B,
        if (srcTree B).edgeSource e = v then j e else 0) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro e he
    split_ifs <;> simp
  unfold RootedTreeGauge.divergence at h ⊢
  rw [htarget, hsource]
  linarith

private noncomputable def canonicalInactiveModes
    (q : SourcePoissonEdge B → ℕ)
    (j : {j : SourcePoissonEdge B → ℤ //
      RootedTreeGauge.CoClosed (srcTree B) j}) :
    Fin (Fintype.card {e : SourcePoissonEdge B // j.1 e = 0}) → ℕ :=
  fun i => q ((Fintype.equivFin {e : SourcePoissonEdge B // j.1 e = 0}).symm i).1

private theorem canonicalInactiveModes_heq
    (q : SourcePoissonEdge B → ℕ)
    (j j' : {j : SourcePoissonEdge B → ℤ //
      RootedTreeGauge.CoClosed (srcTree B) j})
    (h : j = j') : canonicalInactiveModes q j ≍ canonicalInactiveModes q j' := by
  cases h
  rfl

private theorem branch_modes_eq_canonical
    (q : SourcePoissonEdge B → ℕ) (b : GaugeCharacterBranch (srcTree B))
    (hb : GaugeCharacterBranch.assignment b = q) :
    b.2 = canonicalInactiveModes q b.1 := by
  classical
  funext i
  let e0 := (Fintype.equivFin
    {e : SourcePoissonEdge B // b.1.1 e = 0}).symm i
  have hq := congrFun hb e0.1
  have heq : b.1.1 e0.1 = 0 := e0.2
  have hmode : b.2 i = q e0.1 := by
    simpa [GaugeCharacterBranch.assignment, ModeBranch.assignment,
      heq, e0] using hq
  simpa [canonicalInactiveModes, e0] using hmode

private noncomputable def patternToBranch
    (q : SourcePoissonEdge B → ℕ) (s : PhysicalClosedPattern q) :
    GaugeAssignmentFiber q := by
  classical
  let j : SourcePoissonEdge B → ℤ := fun e => -sourceAssignmentCurrent q s.1 e
  have hj : RootedTreeGauge.CoClosed (srcTree B) j := by
    exact rootedCoClosed_neg (sourceAssignmentCurrent q s.1) s.2
  let b : GaugeCharacterBranch (srcTree B) :=
    ⟨⟨j, hj⟩, canonicalInactiveModes q ⟨j, hj⟩⟩
  have hb : GaugeCharacterBranch.assignment b = q := by
    funext e
    by_cases hz : j e = 0
    · simp [GaugeCharacterBranch.assignment, ModeBranch.assignment,
        b, j, canonicalInactiveModes, hz]
    · cases hs : s.1 e with
      | none =>
          simp [sourceAssignmentCurrent, sourceAssignmentSignedMode,
            sourceAssignmentFrequency, positiveMode, hs, j] at hz
      | some a =>
          cases a with
          | false =>
              have hval : j e = ((q e + 1 : ℕ) : ℤ) := by
                simp [j, sourceAssignmentCurrent, sourceAssignmentSignedMode,
                  sourceAssignmentFrequency, positiveMode, hs]
              simp [GaugeCharacterBranch.assignment, ModeBranch.assignment,
                b, j, canonicalInactiveModes, hval]; omega
          | true =>
              have hval : j e = -((q e + 1 : ℕ) : ℤ) := by
                simp [j, sourceAssignmentCurrent, sourceAssignmentSignedMode,
                  sourceAssignmentFrequency, positiveMode, hs]
              simp [GaugeCharacterBranch.assignment, ModeBranch.assignment,
                b, j, canonicalInactiveModes, hval]; omega
  exact ⟨b, hb⟩

private noncomputable def branchToPattern
    (q : SourcePoissonEdge B → ℕ) (b : GaugeAssignmentFiber q) :
    PhysicalClosedPattern q := by
  let s := branchSourcePattern b.1
  have hcurr := sourceAssignmentCurrent_eq_neg_branchCurrent q b.1 b.2
  have hs : RootedTreeGauge.CoClosed (srcTree B)
      (sourceAssignmentCurrent q s) := by
    rw [hcurr]
    exact rootedCoClosed_neg (GaugeCharacterBranch.current b.1) b.1.1.2
  exact ⟨s, hs⟩

private theorem branchToPattern_patternToBranch
    (q : SourcePoissonEdge B → ℕ) (s : PhysicalClosedPattern q) :
    branchToPattern q (patternToBranch q s) = s := by
  classical
  apply Subtype.ext
  funext e
  cases hs : s.1 e with
  | none =>
      simp [branchToPattern, patternToBranch, branchSourcePattern,
        flipSelection, ModeBranch.selectionCode, sourceAssignmentCurrent,
        sourceAssignmentSignedMode, sourceAssignmentFrequency, positiveMode, hs]
  | some a =>
      cases a with
      | false =>
          have hnotzero : (q e : ℤ) + 1 ≠ 0 := by omega
          simp [branchToPattern, patternToBranch, branchSourcePattern,
            flipSelection, ModeBranch.selectionCode, sourceAssignmentCurrent,
            sourceAssignmentSignedMode, sourceAssignmentFrequency, positiveMode,
            hs, hnotzero]
      | true =>
          have hnotzero : (-1 : ℤ) + -(q e : ℤ) ≠ 0 := by omega
          have hdecide : ¬ (q e : ℤ) < -1 := by omega
          simp [branchToPattern, patternToBranch, branchSourcePattern,
            flipSelection, ModeBranch.selectionCode, sourceAssignmentCurrent,
            sourceAssignmentSignedMode, sourceAssignmentFrequency, positiveMode,
            hs, hnotzero, hdecide]

private theorem patternToBranch_branchToPattern
    (q : SourcePoissonEdge B → ℕ) (b : GaugeAssignmentFiber q) :
    patternToBranch q (branchToPattern q b) = b := by
  classical
  rcases b with ⟨br, hb⟩
  apply Subtype.ext
  change (patternToBranch q (branchToPattern q ⟨br, hb⟩)).1 = br
  have hbase :
      (patternToBranch q (branchToPattern q ⟨br, hb⟩)).1.1 = br.1 := by
    apply Subtype.ext
    funext e
    have hcurr := sourceAssignmentCurrent_eq_neg_branchCurrent q br hb
    change -sourceAssignmentCurrent q (branchSourcePattern br) e = br.1.1 e
    rw [congrFun hcurr e]
    simp [GaugeCharacterBranch.current]
  refine Sigma.ext hbase ?_
  have hleft :
      (patternToBranch q (branchToPattern q ⟨br, hb⟩)).1.2 =
        canonicalInactiveModes q
          (patternToBranch q (branchToPattern q ⟨br, hb⟩)).1.1 := by
    rfl
  have hright : br.2 = canonicalInactiveModes q br.1 :=
    branch_modes_eq_canonical q br hb
  exact (heq_of_eq hleft).trans
    ((canonicalInactiveModes_heq q
      (patternToBranch q (branchToPattern q ⟨br, hb⟩)).1.1 br.1 hbase).trans
        (heq_of_eq hright).symm)

private noncomputable def physicalBranchEquiv
    (q : SourcePoissonEdge B → ℕ) :
    PhysicalClosedPattern q ≃ GaugeAssignmentFiber q where
  toFun := patternToBranch q
  invFun := branchToPattern q
  left_inv := branchToPattern_patternToBranch q
  right_inv := patternToBranch_branchToPattern q

private theorem sourceAssignmentFourierCoefficient_eq_branchRelative
    (q : SourcePoissonEdge B → ℕ) (z : ℕ → ℝ)
    (s : PhysicalClosedPattern q)
    (hz : ∀ n, 0 < z (positiveMode n)) :
    sourceAssignmentFourierCoefficient q z s.1 =
      GaugeCharacterBranch.assignmentRelativeCoefficient z q
        (patternToBranch q s).1 := by
  classical
  let b := patternToBranch q s
  have hcurr := sourceAssignmentCurrent_eq_neg_branchCurrent q b.1 b.2
  have hpattern : branchSourcePattern b.1 = s.1 := by
    have h := congrArg Subtype.val (branchToPattern_patternToBranch q s)
    simpa [branchToPattern] using h
  have hcurr' : sourceAssignmentCurrent q s.1 =
      fun e => -GaugeCharacterBranch.current b.1 e := by
    rw [← hpattern]
    exact hcurr
  have hactive (e : SourcePoissonEdge B) :
      (sourceAssignmentCurrent q s.1 e ≠ 0) ↔
        GaugeCharacterBranch.current b.1 e ≠ 0 := by
    rw [congrFun hcurr' e]
    simp [GaugeCharacterBranch.current]
  have hprod :
      sourceAssignmentFourierCoefficient q z s.1 =
        ∏ e ∈ (Finset.univ.filter fun e : SourcePoissonEdge B =>
          GaugeCharacterBranch.current b.1 e ≠ 0),
          z (positiveMode (q e)) / 2 := by
    unfold sourceAssignmentFourierCoefficient
    rw [Finset.prod_filter]
    apply Finset.prod_congr rfl
    intro e he
    by_cases hn : s.1 e = none
    · have hz0 : sourceAssignmentCurrent q s.1 e = 0 := by
        simp [sourceAssignmentCurrent, sourceAssignmentSignedMode, hn]
      have hbeq : GaugeCharacterBranch.current b.1 e = 0 := by
        have := congrFun hcurr' e
        rw [hz0] at this
        simpa [GaugeCharacterBranch.current] using this.symm
      simp [hn, hbeq]
    · have hn' : sourceAssignmentCurrent q s.1 e ≠ 0 := by
        rw [sourceAssignmentCurrent, sourceAssignmentSignedMode]
        cases hs : s.1 e with
        | none => exact (hn hs).elim
        | some a =>
          have hqpos : (0 : ℤ) < ((q e + 1 : ℕ) : ℤ) := by
            exact_mod_cast Nat.zero_lt_succ (q e)
          cases a <;> simp [sourceAssignmentFrequency, positiveMode] <;> omega
      have hbeq : GaugeCharacterBranch.current b.1 e ≠ 0 :=
        (hactive e).mp hn'
      cases hs : s.1 e with
      | none => exact (hn hs).elim
      | some a => simp [hbeq]
  rw [hprod]
  exact (gaugeCharacterBranch_assignmentRelativeCoefficient_eq_selectedProduct
    (T := srcTree B) z q (patternToBranch q s).1
    (patternToBranch q s).2 hz).symm

private theorem physicalClosedPattern_term_eq_branchTerm
    (β : ℝ) (hβ : 0 < β) (t : ℝ)
    (τ : coClosed (srcComplex B)) (q : SourcePoissonEdge B → ℕ)
    (z : ℕ → ℝ) (s : PhysicalClosedPattern q)
    (hz : ∀ n, 0 < z (positiveMode n)) :
    (sourceAssignmentFourierCoefficient q z s.1 : ℂ) *
        physicalGaussianTiltCompletedSquareFactor (B := B) β hβ.le t τ
          (physicalGaugeCurrent (B := B) (sourceAssignmentCurrent q s.1)) =
      (GaugeCharacterBranch.assignmentRelativeCoefficient z q
          (patternToBranch q s).1 : ℂ) *
        dualQuadraticExp
          (scaledChordMatrix (srcTree B)
            (sourceFinitePoissonModel (B := B) Cubical.originZero) β)
          (realTiltParameter (physicalTestChord τ) t)
          ((srcTree B).restrictChord (GaugeCharacterBranch.current
            (patternToBranch q s).1)) := by
  have hcurr := sourceAssignmentCurrent_eq_neg_branchCurrent q
    (patternToBranch q s).1 (patternToBranch q s).2
  have hpattern : branchSourcePattern (patternToBranch q s).1 = s.1 := by
    have h := congrArg Subtype.val (branchToPattern_patternToBranch q s)
    simpa [branchToPattern] using h
  have hcurr' : sourceAssignmentCurrent q s.1 =
      fun e => -GaugeCharacterBranch.current (patternToBranch q s).1 e := by
    rw [← hpattern]
    exact hcurr
  rw [sourceAssignmentFourierCoefficient_eq_branchRelative q z s hz]
  congr 1
  rw [show sourceAssignmentCurrent q s.1 =
      fun e => -GaugeCharacterBranch.current (patternToBranch q s).1 e from hcurr']
  exact physicalCompletedSquare_eq_chordExp β hβ t τ
    (GaugeCharacterBranch.current (patternToBranch q s).1)
    (patternToBranch q s).1.1.2

theorem sourceAssignmentGaussianMoment_eq_gaugeAssignmentMoment
    (β : ℝ) (hβ : 0 < β) (t : ℝ)
    (τ : coClosed (srcComplex B))
    (q : SourcePoissonEdge B → ℕ) (z : ℕ → ℝ)
    (hz : ∀ n, 0 < z (positiveMode n)) :
    sourceAssignmentGaussianMoment β hβ.le t τ q z =
      gaugeAssignmentMoment (srcTree B)
        (scaledChordMatrix (srcTree B)
          (sourceFinitePoissonModel (B := B) Cubical.originZero) β)
        (physicalTestChord τ) t z q := by
  classical
  let p : (SourcePoissonEdge B → Option Bool) → Prop := fun s =>
    RootedTreeGauge.CoClosed (srcTree B) (sourceAssignmentCurrent q s)
  let f : (SourcePoissonEdge B → Option Bool) → ℂ := fun s =>
    (sourceAssignmentFourierCoefficient q z s : ℂ) *
      physicalGaussianTiltCompletedSquareFactor (B := B) β hβ.le t τ
        (physicalGaugeCurrent (B := B) (sourceAssignmentCurrent q s))
  have hnonclosed : ∀ s, ¬ p s → f s = 0 := by
    intro s hs
    have hdiv : currentDivergence
        (physicalGaugeCurrent (B := B) (sourceAssignmentCurrent q s)) ≠ 0 := by
      intro hzero
      exact hs (physicalCurrent_divergence_to_rootedCoClosed
        (sourceAssignmentCurrent q s) hzero)
    simp [f, physicalGaussianTiltCompletedSquareFactor, hdiv]
  have hsplit := Fintype.sum_subtype_add_sum_subtype p f
  change (∑ s : {s : SourcePoissonEdge B → Option Bool // p s}, f s.1) +
      (∑ s : {s : SourcePoissonEdge B → Option Bool // ¬ p s}, f s.1) =
      ∑ s : SourcePoissonEdge B → Option Bool, f s at hsplit
  have hzero : (∑ s : {s : SourcePoissonEdge B → Option Bool // ¬ p s}, f s.1) = 0 := by
    apply Finset.sum_eq_zero
    intro s hs
    exact hnonclosed s.1 s.2
  have hclosedSum :
      sourceAssignmentGaussianMoment β hβ.le t τ q z =
        ∑ s : PhysicalClosedPattern q, f s.1 := by
    unfold sourceAssignmentGaussianMoment
    rw [show (∑ s : SourcePoissonEdge B → Option Bool, f s) =
        (∑ s : {s : SourcePoissonEdge B → Option Bool // p s}, f s.1) +
          ∑ s : {s : SourcePoissonEdge B → Option Bool // ¬ p s}, f s.1 from hsplit.symm]
    rw [hzero, add_zero]
  haveI : Finite (GaugeAssignmentFiber q) :=
    gaugeCharacterBranch_assignmentFiber_finite (srcTree B) q
  letI : Fintype (GaugeAssignmentFiber q) := Fintype.ofFinite _
  have hreindex :
      (∑ s : PhysicalClosedPattern q, f s.1) =
        ∑ b : GaugeAssignmentFiber q,
          (GaugeCharacterBranch.assignmentRelativeCoefficient z q b.1 : ℂ) *
            dualQuadraticExp
              (scaledChordMatrix (srcTree B)
                (sourceFinitePoissonModel (B := B) Cubical.originZero) β)
              (realTiltParameter (physicalTestChord τ) t)
              ((srcTree B).restrictChord (GaugeCharacterBranch.current b.1)) := by
    refine Fintype.sum_equiv (physicalBranchEquiv q) _ _ ?_
    intro s
    exact physicalClosedPattern_term_eq_branchTerm β hβ t τ q z s hz
  rw [hclosedSum, hreindex]
  simp [gaugeAssignmentMoment, assignmentFiberMoment, tsum_fintype,
    GaugeCharacterBranch.current]

end FroehlichSpencer.FS82.Moment.PhysicalChordIdentity

end
