module

public import FroehlichSpencer.FS82.SurfaceInfinite.All
public import FroehlichSpencer.FS82.Infinite.NonsummabilityRoot
public import Mathlib.Tactic
@[expose] public section

open FroehlichSpencer.FS82.Surface
open FroehlichSpencer.FS82.Infinite
open FroehlichSpencer.FS82.Infinite.Nonsummability

namespace FroehlichSpencer.FS82.SurfaceInfinite


theorem sourceShiftUniform_eq_internal (n : ℕ) :
    sourceShiftUniform n = Infinite.Nonsummability.latticeShiftUniform n := rfl

theorem sourceTranslatePlaquetteEquiv_eq_internal (a : SourceLatticeShift) :
    sourceTranslatePlaquetteEquiv a = Infinite.Nonsummability.translatePlaquetteEquiv a := by
  apply Equiv.ext
  intro p
  apply Subtype.ext
  rfl

theorem sourceTranslatePlaquettes_eq_internal (a : SourceLatticeShift)
    (P : Finset GlobalPlaquette) :
    sourceTranslatePlaquettes a P = Infinite.Nonsummability.translatePlaquettes a P := by
  unfold sourceTranslatePlaquettes Infinite.Nonsummability.translatePlaquettes
  rw [sourceTranslatePlaquetteEquiv_eq_internal]
  rfl


noncomputable def CurvatureCylinderState.toInternal
    (S : CurvatureCylinderState) : Infinite.Nonsummability.CurvatureCylinderState where
  law := S.law
  consistent := S.consistent

theorem sourceTranslateCylinderLaw_eq_internal
    (S : CurvatureCylinderState) (a : SourceLatticeShift)
    (P : Finset GlobalPlaquette) :
    sourceTranslateCylinderLaw S a P =
      Infinite.Nonsummability.translateCylinderLaw S.toInternal a P := by
  unfold sourceTranslateCylinderLaw Infinite.Nonsummability.translateCylinderLaw
  have hset := sourceTranslatePlaquettes_eq_internal a P
  cases hset
  change PMF.map (sourceUntranslateCurvatureAssignment a P)
      (S.law (sourceTranslatePlaquettes a P)) =
    PMF.map (Infinite.Nonsummability.untranslateCurvatureAssignment a P)
      (S.law (sourceTranslatePlaquettes a P))
  congr 1

theorem sourceFiniteShiftAverage_eq_internal {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] [Countable α] [DecidableEq α]
    (n : ℕ) (f : SourceLatticeShift → PMF α) :
    sourceFiniteShiftAverage n f =
      Infinite.Nonsummability.finiteShiftAverage n f := by
  unfold sourceFiniteShiftAverage Infinite.Nonsummability.finiteShiftAverage
  rw [sourceShiftUniform_eq_internal]

theorem sourceAveragedCylinderLaw_eq_internal
    (S : CurvatureCylinderState) (n : ℕ) (P : Finset GlobalPlaquette) :
    sourceAveragedCylinderLaw S n P =
      Infinite.Nonsummability.averagedCylinderLaw S.toInternal n P := by
  unfold sourceAveragedCylinderLaw Infinite.Nonsummability.averagedCylinderLaw
  rw [sourceFiniteShiftAverage_eq_internal]
  congr 1

end FroehlichSpencer.FS82.SurfaceInfinite
