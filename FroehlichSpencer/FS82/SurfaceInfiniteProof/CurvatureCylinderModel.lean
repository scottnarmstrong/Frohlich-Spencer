module

public import Mathlib
public import Mathlib.Probability.ProbabilityMassFunction.Basic
public import FroehlichSpencer.FS82.Infinite.LimitStateLaw
public import FroehlichSpencer.FS82.Infinite.NonsummabilityPrimal
public import FroehlichSpencer.FS82.Infinite.FourierParseval
public import FroehlichSpencer.FS82.Infinite.GlobalVariational
public import FroehlichSpencer.FS82.Surface.RectBox4
public import FroehlichSpencer.FS82.Surface.LatticeCell
public import FroehlichSpencer.FS82.Surface.LatticeIsEdge
public import FroehlichSpencer.FS82.Surface.DualCellEmbeddingC1
public import FroehlichSpencer.FS82.Surface.DualPlaquettes
public import FroehlichSpencer.FS82.Surface.SourceClosedIntegerCurrent
public import FroehlichSpencer.FS82.Surface.IntegerDualGaugeQuotient
public import FroehlichSpencer.FS82.Surface.DiscreteDualMeasure
public import FroehlichSpencer.FS82.Surface.DiscreteDualMeasure_isProbabilityMeasure
public import FroehlichSpencer.FS82.Surface.ExistsUnique_sourceGaugeClass_closedCurrentEquiv
@[expose] public section

open MeasureTheory
open Filter Topology
open FroehlichSpencer.FS82.Surface
open FroehlichSpencer.FS82.Infinite
open FroehlichSpencer.FS82.Infinite.Fourier
open FroehlichSpencer.FS82.Root
open FroehlichSpencer.FS82.Moment.Comparison
open FroehlichSpencer.FS82.Infinite.Nonsummability

namespace FroehlichSpencer.FS82.CurvatureStateBridge

noncomputable section


noncomputable def globalPlaquetteAxes (c : LatticeCell) : Finset (Fin 4) := by
  classical
  exact Finset.univ.filter fun i => latticeIsEdge (c i)

abbrev GlobalPlaquette := {c : LatticeCell // (globalPlaquetteAxes c).card = 2}


abbrev SourceLatticePoint := ℤ × (ℤ × (ℤ × ℤ))
abbrev SourceTorus4 := AddCircle (1 : ℝ) ×
  (AddCircle (1 : ℝ) × (AddCircle (1 : ℝ) × AddCircle (1 : ℝ)))


def sourceCellBaseCoordinate (c : LatticeCell) (i : Fin 4) : ℤ :=
  Sum.elim id id (c i)

def sourceCellPoint (c : LatticeCell) : SourceLatticePoint :=
  (sourceCellBaseCoordinate c 0,
    (sourceCellBaseCoordinate c 1,
      (sourceCellBaseCoordinate c 2, sourceCellBaseCoordinate c 3)))


def sourceFourierLaplacianSymbol (k : SourceTorus4) : ℝ :=
  ∑ i : Fin 4, ‖(1 : ℂ) - fourier 1 (match i.val with
    | 0 => k.1 | 1 => k.2.1 | 2 => k.2.2.1 | _ => k.2.2.2)‖ ^ 2


def sourcePointCoordinate (p : SourceLatticePoint) (i : Fin 4) : ℤ :=
  match i.val with
  | 0 => p.1
  | 1 => p.2.1
  | 2 => p.2.2.1
  | _ => p.2.2.2

def sourceDualCurvatureCell (x : SourceLatticePoint) : LatticeCell :=
  fun i => if i = 0 ∨ i = 1 then
    Sum.inr (sourcePointCoordinate x i)
  else Sum.inl (sourcePointCoordinate x i)

noncomputable def sourceDualCurvatureAt (x : SourceLatticePoint) : GlobalPlaquette := by
  refine ⟨sourceDualCurvatureCell x, ?_⟩
  classical
  have haxes : globalPlaquetteAxes (sourceDualCurvatureCell x) = {0, 1} := by
    classical
    ext i
    change i ∈ Finset.univ.filter (fun j : Fin 4 =>
      latticeIsEdge (sourceDualCurvatureCell x j)) ↔ i ∈ ({0, 1} : Finset (Fin 4))
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton]
    by_cases hi : i = 0 ∨ i = 1
    · simp [sourceDualCurvatureCell, hi, latticeIsEdge]
    · simp [sourceDualCurvatureCell, hi, latticeIsEdge]
  rw [haxes]
  decide

def sourcePairPlaquettes (x y : SourceLatticePoint) : Finset GlobalPlaquette :=
  insert (sourceDualCurvatureAt x) {sourceDualCurvatureAt y}

def sourcePairProduct (x y : SourceLatticePoint)
    (ω : sourcePairPlaquettes x y → ℤ) : ℝ :=
  (ω ⟨sourceDualCurvatureAt x, by simp [sourcePairPlaquettes]⟩ : ℝ) *
    (ω ⟨sourceDualCurvatureAt y, by simp [sourcePairPlaquettes]⟩ : ℝ)

structure SourceCurvatureCylinderState where
  law : (P : Finset GlobalPlaquette) → PMF (P → ℤ)
  consistent : ∀ (P₀ P₁ : Finset GlobalPlaquette) (hP : P₀ ⊆ P₁),
    PMF.map (fun x p => x ⟨p.1, hP p.2⟩) (law P₁) = law P₀

noncomputable def SourceCurvatureCylinderState.toInternal
    (S : SourceCurvatureCylinderState) :
    FroehlichSpencer.FS82.Infinite.Nonsummability.CurvatureCylinderState where
  law := S.law
  consistent := by
    intro P₀ P₁ hP
    exact S.consistent P₀ P₁ hP

noncomputable def SourceCurvatureCylinderState.ofInternal
    (S : FroehlichSpencer.FS82.Infinite.Nonsummability.CurvatureCylinderState) :
    SourceCurvatureCylinderState where
  law := S.law
  consistent := by
    intro P₀ P₁ hP
    exact S.consistent P₀ P₁ hP

theorem SourceCurvatureCylinderState.toInternal_ofInternal
    (S : FroehlichSpencer.FS82.Infinite.Nonsummability.CurvatureCylinderState) :
    (SourceCurvatureCylinderState.ofInternal S).toInternal = S := by
  cases S
  rfl

noncomputable def sourceFieldStrengthCorrelation
    (S : SourceCurvatureCylinderState) (d : SourceLatticePoint) : ℝ :=
  ∫ ω, sourcePairProduct 0 d ω ∂ (S.law (sourcePairPlaquettes 0 d)).toMeasure

def AbsolutelySummableCorrelation (C : SourceLatticePoint → ℝ) : Prop :=
  Summable fun d => |C d|

 theorem sourceFieldStrengthCorrelation_eq_internal
    (S : SourceCurvatureCylinderState) (d : SourceLatticePoint) :
    sourceFieldStrengthCorrelation S d =
      FroehlichSpencer.FS82.Infinite.Nonsummability.spectralFieldStrengthCorrelation
        S.toInternal d := by
  rfl


theorem source_stationary_nonsummability_from_internal_root :
    ∃ B : ℝ,
      (∀ β, B ≤ β → 0 < FroehlichSpencer.FS82.Moment.Comparison.betaDoublePrime
        rootPackingCoefficient β) ∧
      ∀ (β : ℝ) (hβ : max rootBetaThreshold B ≤ β),
        ∃ L : CubeCurvatureLimitState β
            (rootBeta_pos (le_trans (le_max_left rootBetaThreshold B) hβ)),
          ∃ s : ℕ → ℕ, StrictMono s ∧
            ∃ S : SourceCurvatureCylinderState,
              (∀ P x, Tendsto
                (fun k => (averagedCylinderLaw (cubeStateToCylinderState L) (s k) P x).toReal)
                atTop (𝓝 (((S.toInternal).law P x).toReal))) ∧
              (∀ a P, translateCylinderLaw S.toInternal a P = S.toInternal.law P) ∧
              ¬ AbsolutelySummableCorrelation (sourceFieldStrengthCorrelation S) := by
  obtain ⟨B, hB, hroot⟩ := fs82_root_nonsummable_fieldStrengthCorrelation
  refine ⟨B, hB, ?_⟩
  intro β hβ
  obtain ⟨L, s, hs, Sint, hpoint, hinv, hns⟩ := hroot β hβ
  let S := SourceCurvatureCylinderState.ofInternal Sint
  have hβlo : 0 < FroehlichSpencer.FS82.Moment.Comparison.betaDoublePrime
      rootPackingCoefficient β := hB β (le_trans (le_max_right rootBetaThreshold B) hβ)
  have hprimal := primal_selectedTwoStagePrimal_not_absSummable
    (le_trans (le_max_left rootBetaThreshold B) hβ) L s Sint hpoint hinv hβlo
  have hS : S.toInternal = Sint := by
    dsimp [S]
    exact SourceCurvatureCylinderState.toInternal_ofInternal Sint
  refine ⟨L, s, hs, S, ?_, ?_, ?_⟩
  · simpa only [hS] using hpoint
  · simpa only [hS] using hinv
  · simpa [AbsolutelySummableCorrelation, sourceFieldStrengthCorrelation_eq_internal,
      hS] using hprimal


end

end FroehlichSpencer.FS82.CurvatureStateBridge

end
