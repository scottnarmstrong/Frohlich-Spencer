/- Controlled fillings and arbitrary-field Jensen bounds for the FS82 Wilson argument. -/
module

public import FroehlichSpencer.FS82.Currents.ShortComponentPacking
public import FroehlichSpencer.FS82.Moment.PositivePacking
public import FroehlichSpencer.FS82.Currents.PlaquetteCarrierPacking
public import FroehlichSpencer.FS82.Wilson.CubeLoopField
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Controlled component fillings and arbitrary-field Jensen bounds

The estimates apply controlled component fillings to the Wilson-loop Jensen bound.
-/

public section

open scoped BigOperators
open Filter

namespace FroehlichSpencer.FS82.Wilson

open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Currents
open FroehlichSpencer.FS82.Currents.ShortPhase
open FroehlichSpencer.FS82.Currents.PlaquetteCarrierPacking
open FroehlichSpencer.FS82.Currents.ShortPhaseAggregate
open FroehlichSpencer.FS82.Currents.ShortComponentPhase
open FroehlichSpencer.FS82.Gaussian
open FroehlichSpencer.FS82.Moment.SourceConstructor
open FroehlichSpencer.FS82.Moment.Packing
open FroehlichSpencer.FS82.Wilson

noncomputable section

variable {B : Box 4}


/-- The lower corner of the component cube furnished by ShortComponentPhase's source construction. -/
noncomputable def componentCubeData (j : IntegerCurrent B) (c : CurrentComponentClass j) :
    {lo : Fin 4 → ℕ // (∀ i, lo i ≤ B i + 1) ∧
      supportInSourceCube (currentComponentSupport j c) lo
        (2 * (currentComponentSupport j c).card)} := by
  classical
  by_cases hc : c ∈ currentComponents j
  · let h := exists_component_cube j hc
    exact ⟨Classical.choose h, Classical.choose_spec h⟩
  · have hempty : ¬ (currentComponentSupport j c).Nonempty := by
      rintro ⟨e, he⟩
      exact hc (Finset.mem_image.mpr ⟨e, (Finset.mem_filter.mp he).1,
        (Finset.mem_filter.mp he).2⟩)
    rw [Finset.not_nonempty_iff_eq_empty] at hempty
    refine ⟨fun _ => 0, ?_⟩
    constructor
    · intro i
      exact Nat.zero_le _
    · rw [hempty]
      intro i e he
      simp at he

@[expose] noncomputable def componentCubeLower (j : IntegerCurrent B)
    (c : CurrentComponentClass j) : Fin 4 → ℕ := (componentCubeData j c).1

@[expose] noncomputable def componentCubeSide (j : IntegerCurrent B)
    (c : CurrentComponentClass j) : ℕ := 2 * (currentComponentSupport j c).card

theorem componentCubeLower_le (j : IntegerCurrent B) (c : CurrentComponentClass j) (i : Fin 4) :
    componentCubeLower j c i ≤ B i + 1 :=
  (componentCubeData j c).2.1 i

theorem componentSupport_in_componentCube (j : IntegerCurrent B)
    (c : CurrentComponentClass j) :
    supportInSourceCube (currentComponentSupport j c) (componentCubeLower j c)
      (componentCubeSide j c) :=
  (componentCubeData j c).2.2


/-- The actual arbitrary two-form pairing with the controlled, physical filling. -/
@[expose] noncomputable def controlledPlaquetteFieldCell
    (field : SourcePlaquette B → ℝ) (d : Cell 4 (bumpedBox B)) : ℝ :=
  if hd : cellDegree d = 2 then field ⟨d, hd⟩ else 0


/-- A connected component is inside the side-six box around every plaquette in its fill cube. -/
theorem component_subset_controlledCenteredLinkBox
    {S : Finset (Link B)} {lo : Fin 4 → ℕ} {L : ℕ}
    (hL : 1 ≤ L) (hcube : supportInSourceCube S lo (2 * L))
    {p : SourcePlaquette B} (hp : p ∈ sourceOmega (B := B) lo (2 * L)) :
    S ⊆ sourceCenteredLinkBox (sourcePlaquetteCoord p) (3 * L) := by
  exact component_subset_centeredLinkBox hL hcube hp


/-- Pairing an integer-valued plaquette cochain with an integer chain is integer-valued. -/
theorem chainPairing_integer_valued (sheet : Cell 4 (bumpedBox B) → ℤ)
    (μ : Chain 4 (bumpedBox B)) :
    ∃ n : ℤ, chainPairing (fun d => (sheet d : ℝ)) μ = (n : ℝ) := by
  refine ⟨∑ d ∈ μ.support, sheet d * μ d, ?_⟩
  rw [chainPairing_eq_support_sum]
  rw [Int.cast_sum]
  apply Finset.sum_congr rfl
  intro d hd
  simp [Int.cast_mul]


/-- The coordinate-oriented extension of a source-dual two-form to primal plaquettes. -/
@[expose] noncomputable def controlledOrientedDualFieldOnPlaquettes
    (f : SourceDualTwoCells B → ℝ) (p : SourcePlaquette B) : ℝ := by
  classical
  exact if hp : sourcePlaquetteInDualImage p then
    dualCellOrientationSign (sourcePlaquetteDualPreimage p hp).1 *
      f (sourcePlaquetteDualPreimage p hp)
  else 0

theorem controlledOrientedDualFieldOnPlaquettes_apply
    (f : SourceDualTwoCells B → ℝ) (q : SourceDualTwoCells B) :
    controlledOrientedDualFieldOnPlaquettes f (sourceDualTwoPlaquette q) =
      dualCellOrientationSign q.1 * f q := by
  have hp := sourceDualTwoPlaquette_interior q
  have hpre : sourcePlaquetteDualPreimage (sourceDualTwoPlaquette q) hp = q := by
    apply sourceDualTwoPlaquette_injective
    exact Classical.choose_spec
      (sourcePlaquetteInDualImage_iff_exists (sourceDualTwoPlaquette q) |>.mp hp)
  simp [controlledOrientedDualFieldOnPlaquettes, hp, hpre]


end

end FroehlichSpencer.FS82.Wilson

end
