/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.SourceInterface.SourceTheorems
public import FroehlichSpencer.FS82.Surface.SourceIntegerGaugeRelationSetoid
public import FroehlichSpencer.FS82.Surface.IntegerDualGaugeQuotient

/-!
The SourceInterface equivalence sends
  the class of `α` to `integerLatticeCurl R α`, and that property determines it.
-/

@[expose] public section

open FroehlichSpencer.FS82.Surface

namespace FroehlichSpencer.FS82.SourceCharacterizations

/--
The two sign
twists and the orientation sign of the internal condition cancel, and the internal carriers are
the literal ones up to the C1 embedding bridge.
-/
theorem sourceExactShiftSupportCondition226_signTwist_iff_literal
    (R : RectBox4) (α α' : IntegerDualField R) :
    FroehlichSpencer.FS82.Gaussian.sourceExactShiftSupportCondition226 R.origin
        (FroehlichSpencer.FS82.Gaussian.sourceIntegerSignTwist α')
        (FroehlichSpencer.FS82.Gaussian.sourceIntegerSignTwist α) ↔
      ∃ ζ : LatticeChain,
        (∀ c : LatticeCell, ¬ (∀ i : Fin 4, (c i).isLeft) → ζ c = 0) ∧
        ((latticeCoboundary ζ).support : Set LatticeCell) ⊆
          Set.range (lambdaStarEmbeddingC1 R) ∧
        ∀ e : DualLinks R,
          α' e - α e = latticeCoboundary ζ (lambdaStarEmbeddingC1 R e) := by
  have hα' : FroehlichSpencer.FS82.Gaussian.sourceIntegerSignTwist
      (FroehlichSpencer.FS82.Gaussian.sourceIntegerSignTwist α') = α' :=
    FroehlichSpencer.FS82.Gaussian.sourceIntegerSignTwist_involutive (B := R.side) α'
  have hα : FroehlichSpencer.FS82.Gaussian.sourceIntegerSignTwist
      (FroehlichSpencer.FS82.Gaussian.sourceIntegerSignTwist α) = α :=
    FroehlichSpencer.FS82.Gaussian.sourceIntegerSignTwist_involutive (B := R.side) α
  rw [FroehlichSpencer.FS82.Gaussian.sourceExactShiftSupportCondition226_iff_sourceRelation,
    hα', hα]
  constructor
  · rintro ⟨γ, hsupport, hshift⟩
    refine ⟨γ.1, γ.2, ?_, fun e => ?_⟩
    · rw [lambdaStarEmbeddingC1_range_bridge R]
      exact hsupport
    · rw [lambdaStarEmbeddingC1_apply_bridge R e]
      exact hshift e
  · rintro ⟨ζ, hvertex, hsupport, hshift⟩
    refine Exists.intro (⟨ζ, hvertex⟩ : FroehlichSpencer.FS82.Gaussian.SourceIntegerPotential)
      ⟨?_, fun e => ?_⟩
    · rw [lambdaStarEmbeddingC1_range_bridge R] at hsupport
      exact hsupport
    · have h := hshift e
      rw [lambdaStarEmbeddingC1_apply_bridge R e] at h
      exact h


theorem sourceIntegerGaugeRelation_iff_sourceExactShiftSupportCondition226
    (R : RectBox4) (α α' : IntegerDualField R) :
    sourceIntegerGaugeRelation R α α' ↔
      ∃ ζ : LatticeChain,
        (∀ c : LatticeCell, ¬ (∀ i : Fin 4, (c i).isLeft) → ζ c = 0) ∧
        ((latticeCoboundary ζ).support : Set LatticeCell) ⊆
          Set.range (lambdaStarEmbeddingC1 R) ∧
        ∀ e : DualLinks R,
          α' e - α e = latticeCoboundary ζ (lambdaStarEmbeddingC1 R e) :=
  (FroehlichSpencer.FS82.SourceInterfaceTheorems.sourceIntegerGaugeRelation_iff_sourceExactShiftSupportCondition226_gate
    R α α').trans (sourceExactShiftSupportCondition226_signTwist_iff_literal R α α')

/-- The SourceInterface class-to-current equivalence sends the class of `α` to the curl of `α`. -/
theorem sourceGaugeClass_closedCurrentEquiv_gate_mk (R : RectBox4) (α : IntegerDualField R) :
    (FroehlichSpencer.FS82.SourceInterfaceTheorems.sourceGaugeClass_closedCurrentEquiv_gate R
      (Quotient.mk (sourceIntegerGaugeRelationSetoid R) α)).1 = integerLatticeCurl R α :=
  rfl


theorem existsUnique_sourceGaugeClass_closedCurrentEquiv (R : RectBox4) :
    ∃! e : IntegerDualGaugeQuotient R ≃ SourceClosedIntegerCurrent R,
      ∀ α : IntegerDualField R,
        (e (Quotient.mk (sourceIntegerGaugeRelationSetoid R) α)).1 =
          integerLatticeCurl R α := by
  refine ⟨FroehlichSpencer.FS82.SourceInterfaceTheorems.sourceGaugeClass_closedCurrentEquiv_gate R,
    sourceGaugeClass_closedCurrentEquiv_gate_mk R, ?_⟩
  intro e he
  apply Equiv.ext
  intro q
  refine Quotient.inductionOn q ?_
  intro α
  apply Subtype.ext
  exact (he α).trans (sourceGaugeClass_closedCurrentEquiv_gate_mk R α).symm

end FroehlichSpencer.FS82.SourceCharacterizations

end
