module

public import FroehlichSpencer.FS82.SourceInterface.LiteralSurface
public import FroehlichSpencer.FS82.Gaussian.LatticePath
public import FroehlichSpencer.FS82.Gaussian.IntegerGauge

@[expose] public section

namespace FroehlichSpencer.FS82.Surface

open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Gaussian


theorem realLatticeCoboundary_bridge :
    realLatticeCoboundary = Cubical.realifyLatticeLinearMap Cubical.latticeCoboundary := rfl


example (R : RectBox4) (q : LambdaStarRealChain R) :
    Cubical.LambdaStarRealChain R.side := q

example (R : RectBox4) (x : RealDualField R) :
    EuclideanSpace ℝ (SourceDualOneCells R.side) := x


theorem c1Coord_bridge (R : RectBox4) (i : Fin 4) :
    dualEmbedCoordC1 R i = Cubical.dualEmbedCoord (B := R.side) R.origin i := by
  apply Function.Embedding.ext
  intro x
  cases x <;> rfl

theorem c1Cell_bridge (R : RectBox4) :
    dualCellEmbeddingC1 R = Cubical.dualCellEmbedding (B := R.side) R.origin := by
  apply Function.Embedding.ext
  intro c
  funext i
  exact congrArg (fun f => f (c i)) (c1Coord_bridge R i)

theorem c1LambdaStar_bridge (R : RectBox4) :
    lambdaStarEmbeddingC1 R = Cubical.lambdaStarEmbedding (B := R.side) R.origin := by
  apply Function.Embedding.ext
  intro e
  exact congrArg (fun f => f e.1) (c1Cell_bridge R)


theorem finsuppToEuclidean_bridge (R : RectBox4) :
    finsuppToEuclidean R = Gaussian.finsuppToEuclidean := rfl

theorem realLatticeDeltaD_bridge :
    realLatticeDeltaD = Cubical.realLatticeDeltaD := rfl


end FroehlichSpencer.FS82.Surface
end
