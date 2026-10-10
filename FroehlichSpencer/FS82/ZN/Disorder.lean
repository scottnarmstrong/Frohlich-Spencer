/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.ZN.Model
public import FroehlichSpencer.FS82.ZN.SourceResidual
public import FroehlichSpencer.FS82.Wilson.PrimalStokes

/-!
# Rectangular disorder sheets and normalized insertions

The source's twist is supported on primal `2–3` plaquettes whose positions
vary in coordinates `0–1`.

The finite
box uses the existing oriented cubical chain and boundary operators; the twist
angle is represented in `UnitAddCircle` by the fraction `ξ/N`.

The direct
normalized integral is the finite-volume insertion of (3.21), with its
`Z^h_{β,Λ}` denominator as in (3.28).
-/

public section

namespace FroehlichSpencer.FS82.ZN

noncomputable section

open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Infinite
open FroehlichSpencer.FS82.Gaussian
open FroehlichSpencer.FS82.Wilson
open Classical
open MeasureTheory
open scoped BigOperators

local instance : Fact (0 < (1 : ℝ)) := ⟨one_pos⟩
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

/-- The vertex cell at the lower corner of the box. -/
@[expose] def rectangleBaseCell (B : Box 4) : Cell 4 B := fun k =>
  Sum.inl ⟨0, Nat.zero_lt_succ (B k)⟩

/-- The primal `2–3` plaquette dual to a source `0–1` plaquette, positioned
at `(x₀+i,x₁+j,x₂,x₃)`.  In particular the varying indices are the *positions*
in coordinates `0–1`; the oriented interval coordinates are fixed in `2–3`.
-/
@[expose] def rectangularTwistPlaquetteAt {B : Box 4} {L T : ℕ}
    (x₀ x₁ x₂ x₃ : ℕ)
    (hx₀ : x₀ + L ≤ B 0 + 1) (hx₁ : x₁ + T ≤ B 1 + 1)
    (hx₂ : x₂ < B 2) (hx₃ : x₃ < B 3)
    (i : Fin L) (j : Fin T) : Cell 4 B :=
  edgeCell (edgeCell
    (vertexUpdate (vertexUpdate (rectangleBaseCell B) 0
        ⟨x₀ + i.val, by omega⟩) 1 ⟨x₁ + j.val, by omega⟩)
    2 ⟨x₂, hx₂⟩) 3 ⟨x₃, hx₃⟩


/-- A source `2–3` plaquette in the centered C1 box.  The C1 dual-cell index
is shifted by `N` in the centered carrier, while its physical position is
`(i+1,j+1,0,0)`. -/
@[expose] def centeredRectangularTwistPlaquette {L T N : ℕ}
    (hL : L ≤ N) (hT : T ≤ N) (hN : 0 < N)
    (i : Fin L) (j : Fin T) : Cell 4 (cube N) :=
  rectangularTwistPlaquetteAt (N + 1) (N + 1) N N
    (by simp [cube]; omega) (by simp [cube]; omega)
    (by simp [cube]; omega) (by simp [cube]; omega) i j

/-- A cell belongs to a finite rectangular sheet when it is one of its
indexed plaquettes. -/
@[expose] def rectangularTwistSheetSupport {B : Box 4} {L T : ℕ}
    (plaq : Fin L → Fin T → Cell 4 B) (c : Cell 4 B) : Prop :=
  ∃ i j, plaq i j = c


@[expose] def centeredRectangularTwistSheet {L T N : ℕ}
    (hL : L ≤ N) (hT : T ≤ N) (hN : 0 < N) : Chain 4 (cube N) :=
  Finsupp.equivFunOnFinite.symm (fun c =>
    if rectangularTwistSheetSupport (centeredRectangularTwistPlaquette hL hT hN) c
      then (1 : ℤ) else 0)


theorem centeredRectangularTwistSheet_apply {L T N : ℕ}
    (hL : L ≤ N) (hT : T ≤ N) (hN : 0 < N)
    (c : Cell 4 (cube N)) :
    centeredRectangularTwistSheet hL hT hN c =
      if rectangularTwistSheetSupport
          (centeredRectangularTwistPlaquette hL hT hN) c
      then 1 else 0 := by
  simp [centeredRectangularTwistSheet]


/-- Add the sheet-supported source twist (3.22) to a plaquette flux. -/
@[expose] def disorderTwistedFlux {B : Box 4} (N ξ : ℕ) (S : Chain 4 B)
    (θ : PrimalAngleConfig B) (p : PrimalPlaquettes B) : UnitAddCircle :=
  primalPlaquetteFlux θ p +
    ((((S p.1 : ℝ) * (ξ : ℝ) / (N : ℝ)) : ℝ) : UnitAddCircle)

theorem continuous_disorderTwistedFlux {B : Box 4} (N ξ : ℕ) (S : Chain 4 B)
    (p : PrimalPlaquettes B) :
    Continuous (fun θ : PrimalAngleConfig B => disorderTwistedFlux N ξ S θ p) := by
  unfold disorderTwistedFlux
  exact (continuous_primalPlaquetteFlux p).add continuous_const

/-- The Wilson action with the disorder insertion on the spanning sheet. -/
@[expose] def twistedWilsonActionDensity {B : Box 4} (β : ℝ) (N ξ : ℕ)
    (S : Chain 4 B) (θ : PrimalAngleConfig B) : ℝ :=
  ∏ p : PrimalPlaquettes B,
    Real.exp (β * circleCosCharacter 1 (disorderTwistedFlux N ξ S θ p))

theorem continuous_twistedWilsonActionDensity {B : Box 4} (β : ℝ) (N ξ : ℕ)
    (S : Chain 4 B) : Continuous (twistedWilsonActionDensity (B := B) β N ξ S) := by
  classical
  unfold twistedWilsonActionDensity
  refine continuous_finsetProd Finset.univ ?_
  intro p hp
  exact Real.continuous_exp.comp
    (continuous_const.mul ((continuous_circleCosCharacter 1).comp
      (continuous_disorderTwistedFlux N ξ S p)))


/-- The unnormalized insertion integral in (3.21), with the finite free-box
base law selected by the finite clock construction. -/
@[expose] def finiteDisorderNumerator {B : Box 4} (β : ℝ) (N ξ : ℕ) (h : NNReal)
    (S : Chain 4 B) : ℝ :=
  ∫ θ : PrimalAngleConfig B,
    twistedWilsonActionDensity β N ξ S θ * znPinningDensity N h θ


/-- The normalized finite-`h` disorder expectation, divided by the same
`Z^h_{β,B}` as the interpolating law. -/
@[expose] def finiteDisorderExpectation {B : Box 4} (β : ℝ) (N ξ : ℕ)
    (h : NNReal) (S : Chain 4 B) : ℝ :=
  finiteDisorderNumerator β N ξ h S / finiteZNPartitionFunction (B := B) β N h


/-- The numerator of the literal discrete `ℤ_N` disorder expectation. -/
@[expose] def discreteDisorderNumerator {B : Box 4} (β : ℝ) (N ξ : ℕ)
    (S : Chain 4 B) : ℝ :=
  ∑ a : ZNConfig B N,
    twistedWilsonActionDensity β N ξ S (znConfigAsCircle N a)


/-- The normalized disorder expectation in the literal finite discrete law. -/
@[expose] def discreteDisorderExpectation {B : Box 4} (β : ℝ) (N ξ : ℕ)
    (S : Chain 4 B) : ℝ :=
  discreteDisorderNumerator β N ξ S / discreteZNPartitionFunction (B := B) β N


/-- The source finite-volume disorder expectation on a centered cube.  This
specialization fixes the insertion to the C1-positioned rectangle represented
by `cubeSourcePlaquetteField`; `N_box` is the cube radius and `N` is the clock
order. -/
@[expose] def finiteCenteredDisorderExpectation
    (β : ℝ) (N ξ L T N_box : ℕ) (h : NNReal)
    (hL : L ≤ N_box) (hT : T ≤ N_box) (hbox : 0 < N_box) : ℝ :=
  finiteDisorderExpectation β N ξ h
    (centeredRectangularTwistSheet hL hT hbox)


/-- The source endpoint expectation on the centered finite `ℤ_N` cube. -/
@[expose] def discreteCenteredDisorderExpectation
    (β : ℝ) (N ξ L T N_box : ℕ)
    (hL : L ≤ N_box) (hT : T ≤ N_box) (hbox : 0 < N_box) : ℝ :=
  discreteDisorderExpectation β N ξ
    (centeredRectangularTwistSheet hL hT hbox)


end

end FroehlichSpencer.FS82.ZN

end
