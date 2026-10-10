module
public import FroehlichSpencer.FS82.CovarianceTransport.QuotientChordCore

/-!
# Literal gauge quotient in source rooted-tree chord coordinates
-/

@[expose] public section

open FroehlichSpencer.FS82.Surface
open FroehlichSpencer.FS82.SourceModels.IntegerDualModel
open FroehlichSpencer.FS82.Poisson
open FroehlichSpencer.FS82.Surface.IntegerGaugeTransport

namespace FroehlichSpencer.FS82.SourceCovarianceBridge

open Classical

local instance sourceRelationEquivalenceGateCovariance : SourceRelationEquivalenceGate :=
  ⟨FroehlichSpencer.FS82.SourceInterfaceResults.sourceIntegerGaugeRelation_isEquivalence_gate⟩

variable (R : RectBox4)

/-- Read a literal field in the finite source-edge carrier. -/
noncomputable def sourceRootNormalize (α : IntegerDualField R) :
    SourcePoissonEdge R.side → ℤ :=
  rootNormalizeSource R α

/-- The quotient class represented by the zero extension of chord coordinates. -/
noncomputable def rootChordToQuotient
    (n : (sourceRootedTree R.side).Chord → ℤ) : IntegerDualGaugeQuotient R :=
  Quotient.mk (sourceIntegerGaugeRelationSetoid R)
    (fun e => (sourceRootedTree R.side).extendChord n
      (linksEquivSource R e))

/-- The chord values of the unique normalized representative. -/
noncomputable def quotientClassToChord
    (c : IntegerDualGaugeQuotient R) : (sourceRootedTree R.side).Chord → ℤ :=
  Quotient.lift
    (fun α => (sourceRootedTree R.side).restrictChord (sourceRootNormalize R α))
    (by
      intro α α' hrel
      have h := rootNormalize_eq_of_relation R α α' hrel
      exact congrArg (sourceRootedTree R.side).restrictChord h) c

private theorem normalize_extendChord
    (n : (sourceRootedTree R.side).Chord → ℤ) :
    RootedTreeGauge.normalize (sourceRootedTree R.side)
      ((sourceRootedTree R.side).extendChord n) =
        (sourceRootedTree R.side).extendChord n := by
  let T := sourceRootedTree R.side
  let x := T.extendChord n
  have hx : RootedTreeGauge.InTreeGauge T x := by
    intro w
    simp [x, RootedTreeGauge.extendChord]
  have hp : ∀ w : {x : SourcePoissonVertex R.side // x ≠ T.root},
      RootedTreeGauge.coboundary T (RootedTreeGauge.treePotential T x)
        (T.treeEdge w) = 0 := by
    intro w
    rw [RootedTreeGauge.treePotential_coboundary_treeEdge]
    exact hx w
  have hconst := T.potential_constant_of_tree_zero
    (RootedTreeGauge.treePotential T x) hp
  funext e
  change x e - (RootedTreeGauge.treePotential T x (T.edgeTarget e) -
    RootedTreeGauge.treePotential T x (T.edgeSource e)) = x e
  rw [hconst (T.edgeTarget e), hconst (T.edgeSource e)]
  simp [RootedTreeGauge.treePotential_root]

private theorem sourceRootNormalize_extendChord
    (n : (sourceRootedTree R.side).Chord → ℤ) :
    sourceRootNormalize R (fun e => (sourceRootedTree R.side).extendChord n
        (linksEquivSource R e)) = (sourceRootedTree R.side).extendChord n := by
  let T := sourceRootedTree R.side
  have hfield : (fun e : SourcePoissonEdge R.side =>
      (T.extendChord n) (linksEquivSource R ((linksEquivSource R).symm e))) =
      T.extendChord n := by
    funext e
    exact congrArg (T.extendChord n)
      ((linksEquivSource R).apply_symm_apply e)
  change RootedTreeGauge.normalize T
      (fun e => (T.extendChord n) (linksEquivSource R
        ((linksEquivSource R).symm e))) = T.extendChord n
  rw [hfield]
  exact normalize_extendChord R n

theorem quotientChord_left_inverse (c : IntegerDualGaugeQuotient R) :
    rootChordToQuotient R (quotientClassToChord R c) = c := by
  refine Quotient.inductionOn c ?_
  intro α
  let T := sourceRootedTree R.side
  have hextSource : T.extendChord (T.restrictChord (sourceRootNormalize R α)) =
      sourceRootNormalize R α :=
    T.extend_restrictChord (rootNormalize_treeGauge R α)
  have hext : (fun e : DualLinks R =>
      T.extendChord (T.restrictChord (sourceRootNormalize R α))
        (linksEquivSource R e)) = rootNormalize R α := by
    funext e
    change T.extendChord (T.restrictChord (sourceRootNormalize R α))
        (linksEquivSource R e) = sourceRootNormalize R α (linksEquivSource R e)
    rw [hextSource]
  change Quotient.mk (sourceIntegerGaugeRelationSetoid R)
      (fun e : DualLinks R =>
        T.extendChord (T.restrictChord (sourceRootNormalize R α))
          (linksEquivSource R e)) =
    Quotient.mk (sourceIntegerGaugeRelationSetoid R) α
  rw [hext]
  apply Quotient.sound
  exact (SourceModels.IntegerDualModel.sourceIntegerGaugeRelation_isEquivalence_internal R).symm
    (GaugeCurrentEquivalence.sourceCurl_eq_implies_gauge R α (rootNormalize R α)
      (rootNormalize_integerCurl_eq R α))

theorem quotientChord_right_inverse (n : (sourceRootedTree R.side).Chord → ℤ) :
    quotientClassToChord R (rootChordToQuotient R n) = n := by
  simp only [rootChordToQuotient, quotientClassToChord, Quotient.lift_mk]
  funext c
  rw [sourceRootNormalize_extendChord R n]
  exact congrFun ((sourceRootedTree R.side).restrict_extendChord n) c

/-- Literal integer gauge classes are exactly integer assignments on the
chords of the source rooted tree. -/
noncomputable def literalIntegerDualGaugeQuotientEquivChord :
    IntegerDualGaugeQuotient R ≃ ((sourceRootedTree R.side).Chord → ℤ) where
  toFun := quotientClassToChord R
  invFun := rootChordToQuotient R
  left_inv := quotientChord_left_inverse R
  right_inv := quotientChord_right_inverse R

end FroehlichSpencer.FS82.SourceCovarianceBridge
end
