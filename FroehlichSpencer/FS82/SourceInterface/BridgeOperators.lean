module

public import FroehlichSpencer.FS82.SourceInterface.CarrierIdentities
public import FroehlichSpencer.FS82.Gaussian.LatticeComplex

@[expose] public section

namespace FroehlichSpencer.FS82.Surface

open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Gaussian

theorem lambdaStarRealZeroExtension_eq_embDomain (R : RectBox4)
    (q : LambdaStarRealChain R) :
    lambdaStarRealZeroExtension R q = Finsupp.embDomain (lambdaStarEmbeddingC1 R) q := by
  induction q using Finsupp.induction_linear with
  | zero => simp [lambdaStarRealZeroExtension]
  | add q₁ q₂ hq₁ hq₂ =>
      rw [map_add]
      have hE : Finsupp.embDomain (lambdaStarEmbeddingC1 R) (q₁ + q₂) =
          Finsupp.embDomain (lambdaStarEmbeddingC1 R) q₁ +
            Finsupp.embDomain (lambdaStarEmbeddingC1 R) q₂ := by
        ext x
        simp [Finsupp.embDomain_apply]
      rw [hE, hq₁, hq₂]
  | single e a => simp [lambdaStarRealZeroExtension, Finsupp.embDomain_single]

theorem zero_extension_bridge_pointwise (R : RectBox4)
    (q : LambdaStarRealChain R) (c : Cubical.LatticeCell 4) :
    lambdaStarRealZeroExtension R q c =
      Cubical.lambdaStarRealZeroExtension (B := R.side) R.origin
        (q : Cubical.LambdaStarRealChain R.side) c := by
  classical
  let q' : Cubical.LambdaStarRealChain R.side := q
  rw [FroehlichSpencer.FS82.Surface.lambdaStarRealZeroExtension_eq_embDomain R q]
  rw [Cubical.lambdaStarRealZeroExtension_eq_embDomain (B := R.side) R.origin q']
  have hEmbed : lambdaStarEmbeddingC1 R =
      Cubical.lambdaStarEmbedding (B := R.side) R.origin := c1LambdaStar_bridge R
  change Finsupp.embDomain (lambdaStarEmbeddingC1 R) q c =
    Finsupp.embDomain (Cubical.lambdaStarEmbedding (B := R.side) R.origin) q' c
  rw [hEmbed]
  rfl

theorem compression_bridge_pointwise (R : RectBox4)
    (q : Cubical.RealLatticeChain 4) (e : DualLinks R) :
    lambdaStarRealCompression R q e =
      Cubical.lambdaStarRealCompression (B := R.side) R.origin q e := by
  have hEmbed : lambdaStarEmbeddingC1 R =
      Cubical.lambdaStarEmbedding (B := R.side) R.origin := c1LambdaStar_bridge R
  change q (lambdaStarEmbeddingC1 R e) =
    q (Cubical.lambdaStarEmbedding (B := R.side) R.origin e)
  rw [hEmbed]
  rfl

theorem operator_definition_bridge (R : RectBox4) :
    piLambdaStarDeltaDReal R =
      Cubical.piLambdaStarDeltaDReal (B := R.side) R.origin := by
  apply LinearMap.ext
  intro q
  let q' : Cubical.LambdaStarRealChain R.side := q
  apply Finsupp.ext
  intro e
  have hext : lambdaStarRealZeroExtension R q =
      Cubical.lambdaStarRealZeroExtension (B := R.side) R.origin q' := by
    apply Finsupp.ext
    intro c
    exact zero_extension_bridge_pointwise R q c
  change lambdaStarRealCompression R
      (realLatticeDeltaD (lambdaStarRealZeroExtension R q)) e =
    Cubical.lambdaStarRealCompression (B := R.side) R.origin
      (Cubical.realLatticeDeltaD
        (Cubical.lambdaStarRealZeroExtension (B := R.side) R.origin q')) e
  rw [hext, realLatticeDeltaD_bridge]
  exact compression_bridge_pointwise R _ e

theorem finiteLatticeHodgeOperator_bridge (R : RectBox4) :
    finiteLatticeHodgeOperator R =
      Gaussian.latticeStencilOperator (B := R.side) R.origin := by
  apply LinearMap.ext
  intro x
  let x' : EuclideanSpace ℝ (Cubical.LambdaStarLinks R.side) := x
  change finsuppToEuclidean R
      (piLambdaStarDeltaDReal R (euclideanToFinsupp R x)) =
    Gaussian.finsuppToEuclidean
      (Cubical.piLambdaStarDeltaDReal (B := R.side) R.origin
        (Gaussian.euclideanToFinsupp x'))
  have hq : euclideanToFinsupp R x = Gaussian.euclideanToFinsupp x' := by
    rfl
  rw [hq, operator_definition_bridge R, finsuppToEuclidean_bridge R]
  rfl

theorem latticeCurl_bridge (R : RectBox4) (x : RealDualField R) :
    latticeCurl R x =
      Cubical.realifyLatticeLinearMap Cubical.latticeCoboundary
        (Cubical.lambdaStarRealZeroExtension (B := R.side) R.origin
          (Gaussian.euclideanToFinsupp
            (x : EuclideanSpace ℝ (Cubical.LambdaStarLinks R.side)))) := by
  change realLatticeCoboundary
      (lambdaStarRealZeroExtension R (euclideanToFinsupp R x)) = _
  rw [realLatticeCoboundary_bridge]
  have hq : euclideanToFinsupp R x = Gaussian.euclideanToFinsupp
      (x : EuclideanSpace ℝ (Cubical.LambdaStarLinks R.side)) := rfl
  rw [hq]
  have hext : lambdaStarRealZeroExtension R
      (Gaussian.euclideanToFinsupp
        (x : EuclideanSpace ℝ (Cubical.LambdaStarLinks R.side))) =
      Cubical.lambdaStarRealZeroExtension (B := R.side) R.origin
        (Gaussian.euclideanToFinsupp
          (x : EuclideanSpace ℝ (Cubical.LambdaStarLinks R.side))) := by
    apply Finsupp.ext
    intro c
    exact zero_extension_bridge_pointwise R _ c
  rw [hext]

end FroehlichSpencer.FS82.Surface
end
