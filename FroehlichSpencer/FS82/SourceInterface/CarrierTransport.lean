module
public import FroehlichSpencer.FS82.SourceInterface.SourceOperators
public import FroehlichSpencer.FS82.SourceInterface.OperatorInvariance

@[expose] public section

open scoped InnerProductSpace
open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Gaussian
open FroehlichSpencer.FS82.Surface

namespace FroehlichSpencer.FS82.Surface

theorem lambdaStarBoundary_coordinate_expansion (R : RectBox4)
    (μ : RealDualField R) (v : DualVertices R) :
    fullLatticeDivergence R μ (dualCellEmbeddingC1 R v.1) =
      ∑ e : DualLinks R, μ e *
        (((Cubical.latticeBoundaryBasis
          (Cubical.lambdaStarEmbedding (B := R.side) R.origin e) :
            Cubical.LatticeChain 4)
          (Cubical.dualCellEmbedding (B := R.side) R.origin v.1) : ℤ) : ℝ) := by
  classical
  let q : LambdaStarRealChain R := euclideanToFinsupp R μ
  have hrepr : fullLatticeDivergence R μ =
      Finsupp.linearCombination ℝ
        (fun e : DualLinks R =>
          realLatticeBoundary
            (Finsupp.single (lambdaStarEmbeddingC1 R e) 1)) q := by
    change realLatticeBoundary (lambdaStarRealZeroExtension R q) = _
    change realLatticeBoundary
        (Finsupp.linearCombination ℝ
          (fun e : DualLinks R =>
            Finsupp.single (lambdaStarEmbeddingC1 R e) 1) q) = _
    rw [realLinearMap_linearCombination]
  rw [hrepr]
  rw [Finsupp.linearCombination_apply, Finsupp.sum_apply]
  simp only [realLatticeBoundary_single, c1Cell_bridge, c1LambdaStar_bridge, Finsupp.smul_apply,
    smul_eq_mul]
  rw [Finsupp.sum_fintype (h := by intro e; simp)]
  apply Finset.sum_congr rfl
  intro e he
  have hq : q e = μ e := by simp [q, euclideanToFinsupp]
  rw [hq]
  by_cases hμ : μ e = 0
  · simp [hμ]
  · rfl


theorem latticeExactOneComplex_d0_adjoint_coordinate_eq_divergence
    (R : RectBox4) (μ : RealDualField R) (v : DualVertices R) :
    ((latticeExactOneComplex (B := R.side) R.origin).d₀.adjoint
      (μ : EuclideanSpace ℝ (SourceDualOneCells R.side)))
        (v : SourceDualZeroCells R.side) =
      lambdaStarVertexDivergence R μ v := by
  classical
  let v' : SourceDualZeroCells R.side := v
  let μ' : EuclideanSpace ℝ (SourceDualOneCells R.side) := μ
  let basisV : EuclideanSpace ℝ (SourceDualZeroCells R.side) :=
    Gaussian.finsuppToEuclidean (Finsupp.single v' (1 : ℝ))
  have hcoord := euclideanCoordinate_eq_inner_single
    ((latticeExactOneComplex (B := R.side) R.origin).d₀.adjoint μ') v'
  rw [LinearMap.adjoint_inner_right] at hcoord
  have hsum : inner ℝ
      ((latticeExactOneComplex (B := R.side) R.origin).d₀
        basisV) μ' =
      fullLatticeDivergence R μ (dualCellEmbeddingC1 R v.1) := by
    rw [← Gaussian.finsuppToEuclidean_euclideanToFinsupp
      ((latticeExactOneComplex (B := R.side) R.origin).d₀ basisV),
      ← Gaussian.finsuppToEuclidean_euclideanToFinsupp μ',
      Gaussian.inner_finsuppToEuclidean]
    calc
      (∑ e : SourceDualOneCells R.side,
          Gaussian.euclideanToFinsupp
            ((latticeExactOneComplex (B := R.side) R.origin).d₀ basisV) e *
              Gaussian.euclideanToFinsupp μ' e) =
          ∑ e : SourceDualOneCells R.side, μ' e *
            (((Cubical.latticeBoundaryBasis
              (Cubical.lambdaStarEmbedding (B := R.side) R.origin e) :
                Cubical.LatticeChain 4)
              (Cubical.dualCellEmbedding (B := R.side) R.origin v.1) : ℤ) : ℝ) := by
        apply Finset.sum_congr rfl
        intro e he
        have heq := sourceD0_vertexBasis_coefficient R v' e
        have hbasis : basisV = WithLp.toLp 2 (Pi.single v' (1 : ℝ)) := by
          ext x
          simp [basisV, Gaussian.finsuppToEuclidean,
            Finsupp.linearEquivFunOnFinite_single, Pi.single_apply, eq_comm]
        have heq' :
            ((latticeExactOneComplex (B := R.side) R.origin).d₀ basisV) e =
              (((Cubical.latticeCoboundaryBasis
                (Cubical.dualCellEmbedding (B := R.side) R.origin v'.1) :
                  Cubical.LatticeChain 4)
                (Cubical.lambdaStarEmbedding (B := R.side) R.origin e) : ℤ) : ℝ) := by
          rw [hbasis]
          exact heq
        calc
          Gaussian.euclideanToFinsupp
              ((latticeExactOneComplex (B := R.side) R.origin).d₀ basisV) e *
                Gaussian.euclideanToFinsupp μ' e =
              ((latticeExactOneComplex (B := R.side) R.origin).d₀ basisV) e * μ' e := by
                simp [Gaussian.euclideanToFinsupp]
          _ = μ' e * (((Cubical.latticeBoundaryBasis
              (Cubical.lambdaStarEmbedding (B := R.side) R.origin e) :
                Cubical.LatticeChain 4)
              (Cubical.dualCellEmbedding (B := R.side) R.origin v.1) : ℤ) : ℝ) := by
                rw [heq', Gaussian.latticeCoboundaryBasis_transpose]
                ring
      _ = ∑ e : DualLinks R, μ e *
            (((Cubical.latticeBoundaryBasis
              (Cubical.lambdaStarEmbedding (B := R.side) R.origin e) :
                Cubical.LatticeChain 4)
              (Cubical.dualCellEmbedding (B := R.side) R.origin v.1) : ℤ) : ℝ) := by
        let hLinks : DualLinks R = SourceDualOneCells R.side := rfl
        let linkEquiv : SourceDualOneCells R.side ≃ DualLinks R :=
          Equiv.cast hLinks.symm
        refine Fintype.sum_equiv linkEquiv _ _ ?_
        intro e
        cases hLinks
        rfl
      _ = fullLatticeDivergence R μ (dualCellEmbeddingC1 R v.1) :=
        (lambdaStarBoundary_coordinate_expansion R μ v).symm
  rw [hcoord, hsum]
  change fullLatticeDivergence R μ (dualCellEmbeddingC1 R v.1) =
    fullLatticeDivergence R μ (dualCellEmbeddingC1 R v.1)
  rfl


theorem coClosed_iff_W (R : RectBox4) (μ : RealDualField R) :
    μ ∈ Gaussian.coClosed (Gaussian.latticeExactOneComplex
      (B := R.side) R.origin) ↔ μ ∈ W R := by
  change (Gaussian.latticeExactOneComplex (B := R.side) R.origin).d₀.adjoint
      (μ : EuclideanSpace ℝ (SourceDualOneCells R.side)) = 0 ↔
    lambdaStarVertexDivergence R μ = 0
  constructor
  · intro h
    ext v
    calc
      lambdaStarVertexDivergence R μ v =
          ((Gaussian.latticeExactOneComplex (B := R.side) R.origin).d₀.adjoint
            (μ : EuclideanSpace ℝ (SourceDualOneCells R.side)))
              (v : SourceDualZeroCells R.side) :=
        (latticeExactOneComplex_d0_adjoint_coordinate_eq_divergence R μ v).symm
      _ = 0 := congrArg (fun f : EuclideanSpace ℝ (SourceDualZeroCells R.side) =>
        f (v : SourceDualZeroCells R.side)) h
  · intro h
    ext v
    calc
      ((Gaussian.latticeExactOneComplex (B := R.side) R.origin).d₀.adjoint
          (μ : EuclideanSpace ℝ (SourceDualOneCells R.side)))
            (v : SourceDualZeroCells R.side) =
          lambdaStarVertexDivergence R μ v :=
        latticeExactOneComplex_d0_adjoint_coordinate_eq_divergence R μ v
      _ = 0 := congrArg (fun f : EuclideanSpace ℝ (DualVertices R) => f v) h


theorem W_eq_coClosed (R : RectBox4) :
    W R = Gaussian.coClosed (Gaussian.latticeExactOneComplex
      (B := R.side) R.origin) := by
  ext μ
  exact (coClosed_iff_W R μ).symm


noncomputable def literalWEquivCoClosed (R : RectBox4) :
    W R ≃ₗ[ℝ] Gaussian.coClosed (Gaussian.latticeExactOneComplex
      (B := R.side) R.origin) where
  toFun x := ⟨x.1, by
    let W' : Submodule ℝ (EuclideanSpace ℝ (Gaussian.SourceDualOneCells R.side)) := W R
    have hW : W' = Gaussian.coClosed (Gaussian.latticeExactOneComplex
        (B := R.side) R.origin) := W_eq_coClosed R
    have hx : (x.1 : EuclideanSpace ℝ (Gaussian.SourceDualOneCells R.side)) ∈ W' := x.2
    exact (congrArg (fun S : Submodule ℝ
        (EuclideanSpace ℝ (Gaussian.SourceDualOneCells R.side)) =>
        (x.1 : EuclideanSpace ℝ (Gaussian.SourceDualOneCells R.side)) ∈ S) hW).mp hx⟩
  invFun x := ⟨x.1, by
    let W' : Submodule ℝ (EuclideanSpace ℝ (Gaussian.SourceDualOneCells R.side)) := W R
    have hW : W' = Gaussian.coClosed (Gaussian.latticeExactOneComplex
        (B := R.side) R.origin) := W_eq_coClosed R
    have hx : (x.1 : EuclideanSpace ℝ (Gaussian.SourceDualOneCells R.side)) ∈
        Gaussian.coClosed (Gaussian.latticeExactOneComplex (B := R.side) R.origin) := x.2
    exact (congrArg (fun S : Submodule ℝ
        (EuclideanSpace ℝ (Gaussian.SourceDualOneCells R.side)) =>
        (x.1 : EuclideanSpace ℝ (Gaussian.SourceDualOneCells R.side)) ∈ S) hW).mpr hx⟩
  left_inv x := by apply Subtype.ext; rfl
  right_inv x := by apply Subtype.ext; rfl
  map_add' x y := by apply Subtype.ext; rfl
  map_smul' a x := by apply Subtype.ext; rfl

theorem literalWEquivCoClosed_apply_val (R : RectBox4) (x : W R) :
    ((literalWEquivCoClosed R x : Gaussian.coClosed
        (Gaussian.latticeExactOneComplex (B := R.side) R.origin)) :
      EuclideanSpace ℝ (Gaussian.SourceDualOneCells R.side)) =
    (((x : W R) : RealDualField R) :
      EuclideanSpace ℝ (Gaussian.SourceDualOneCells R.side)) := by rfl

theorem literalWEquivCoClosed_symm_apply_val (R : RectBox4)
    (x : Gaussian.coClosed (Gaussian.latticeExactOneComplex (B := R.side) R.origin)) :
    (((literalWEquivCoClosed R).symm x : W R) : RealDualField R) =
    (x : EuclideanSpace ℝ (Gaussian.SourceDualOneCells R.side)) := by rfl

theorem finiteLatticeHodgeOperator_preservesCoClosed_internal (R : RectBox4)
    (μ : W R) :
  finiteLatticeHodgeOperator R (μ : RealDualField R) ∈ W R := by
  change lambdaStarVertexDivergence R
      (finiteLatticeHodgeOperator R (μ : RealDualField R)) = 0
  ext v
  let μ' : EuclideanSpace ℝ (SourceDualOneCells R.side) :=
    (μ : RealDualField R)
  have hmem := Gaussian.latticeStencil_mem_coClosed
    (B := R.side) R.origin μ'
  change (latticeExactOneComplex (B := R.side) R.origin).d₀.adjoint
      (latticeStencilOperator (B := R.side) R.origin μ') = 0 at hmem
  have hker : (latticeExactOneComplex (B := R.side) R.origin).d₀.adjoint
      (finiteLatticeHodgeOperator R (μ : RealDualField R)) = 0 := by
    rw [finiteLatticeHodgeOperator_bridge R]
    convert hmem using 1
  have hcoord := latticeExactOneComplex_d0_adjoint_coordinate_eq_divergence
    R (finiteLatticeHodgeOperator R (μ : RealDualField R)) v
  rw [← hcoord]
  exact congrFun (congrArg WithLp.ofLp hker) v


end FroehlichSpencer.FS82.Surface
end
