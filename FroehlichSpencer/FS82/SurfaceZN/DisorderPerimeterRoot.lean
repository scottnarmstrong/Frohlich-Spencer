/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.ZN.DisorderRoot
public import FroehlichSpencer.FS82.SurfaceZN.All

public import Mathlib.Tactic

@[expose] public section

namespace FroehlichSpencer.FS82.SurfaceZN

open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Wilson
open FroehlichSpencer.FS82.ZN

example {B : Box4} (c : Cell4 B) : basisChain c = Cubical.basisChain c := rfl

example {B : Box4} (c : Cell4 B) (i : Fin 4) (e : Fin (B i)) :
    upperFace c i e = Cubical.upperFace c i e := rfl

example {B : Box4} (c : Cell4 B) (i : Fin 4) (e : Fin (B i)) :
    lowerFace c i e = Cubical.lowerFace c i e := rfl

example {B : Box4} (c : Cell4 B) (i : Fin 4) :
    cellRankBefore c i = Cubical.cellRankBefore c i := by
  rfl

example {B : Box4} (c : Cell4 B) :
    cellAxes c = Cubical.cellAxes c := by
  rfl

private theorem axisBoundaryBasis_eq {B : Box4} (c : Cell4 B) (i : Fin 4) :
    axisBoundaryBasis c i = Cubical.axisBoundaryBasis c i := by
  classical
  apply Finsupp.ext
  intro x
  cases hci : c i <;>
    simp [axisBoundaryBasis, Cubical.axisBoundaryBasis, hci,
      cellRankBefore, Cubical.cellRankBefore, coordIsEdge, Cubical.coordIsEdge,
      basisChain, Cubical.basisChain, upperFace, Cubical.upperFace,
      lowerFace, Cubical.lowerFace, vertexUpdate, Cubical.vertexUpdate] ;
      first | rfl | exact Or.inl rfl

private theorem axisBoundary_eq {B : Box4} (i : Fin 4) :
    axisBoundary (B := B) i = Cubical.axisBoundary i := by
  unfold axisBoundary Cubical.axisBoundary
  have h : (fun c : Cell4 B => axisBoundaryBasis c i) =
      (fun c : Cell4 B => Cubical.axisBoundaryBasis c i) :=
    funext fun c => axisBoundaryBasis_eq c i
  rw [h]

private theorem boundary_eq {B : Box4} :
    boundary (B := B) = Cubical.boundary := by
  unfold boundary Cubical.boundary
  apply Finset.sum_congr rfl
  intro i hi
  exact axisBoundary_eq i

private theorem circleCochain_eq {B : Box4} (θ : Config B) :
    primalCircleCochain θ = Wilson.primalCircleCochain θ := by
  change (fun c => if h : Cubical.cellDegree c = 1 then θ ⟨c, h⟩ else 0) =
    (fun c => if h : Cubical.cellDegree c = 1 then θ ⟨c, h⟩ else 0)
  rfl

private theorem flux_eq {B : Box4} (θ : Config B) (p : Plaquettes B) :
    primalPlaquetteFlux θ p = Wilson.primalPlaquetteFlux θ p := by
  unfold primalPlaquetteFlux Wilson.primalPlaquetteFlux
  change Finsupp.linearCombination ℤ (primalCircleCochain θ)
      (boundary (Finsupp.single p.1 1)) =
    Finsupp.linearCombination ℤ (Wilson.primalCircleCochain θ)
      (Cubical.boundary (Finsupp.single p.1 1))
  rw [boundary_eq, circleCochain_eq]

private theorem wilsonAction_eq {B : Box4} (β : ℝ) (θ : Config B) :
    wilsonActionDensity β θ = ZN.wilsonActionDensity β θ := by
  classical
  unfold wilsonActionDensity ZN.wilsonActionDensity
  have hset : (Finset.univ : Finset (Plaquettes B)) = Finset.univ := by
    ext p
    simp
  rw [hset]
  apply Finset.prod_congr rfl
  intro p hp
  simp [wilsonPlaquetteFactor, ZN.wilsonPlaquetteFactor,
    circleCosCharacter, ZN.circleCosCharacter, flux_eq]

private theorem znPinningDensity_eq {B : Box4} (N : ℕ) (h : NNReal) (θ : Config B) :
    znPinningDensity N h θ = ZN.znPinningDensity N h θ := rfl

private theorem finiteZNWeight_eq {B : Box4} (β : ℝ) (N : ℕ) (h : NNReal)
    (θ : Config B) :
    finiteZNWeight β N h θ = ZN.finiteZNWeight β N h θ := by
  unfold finiteZNWeight ZN.finiteZNWeight
  rw [wilsonAction_eq, znPinningDensity_eq]

private theorem finiteZNPartitionFunction_eq {B : Box4} (β : ℝ) (N : ℕ) (h : NNReal) :
    finiteZNPartitionFunction (B := B) β N h =
      ZN.finiteZNPartitionFunction (B := B) β N h := by
  unfold finiteZNPartitionFunction ZN.finiteZNPartitionFunction
  apply MeasureTheory.integral_congr_ae
  exact Filter.Eventually.of_forall (fun θ => finiteZNWeight_eq β N h θ)

private theorem znConfigAsCircle_eq {B : Box4} (N : ℕ) (a : ZNConfig B N) :
    znConfigAsCircle N a = ZN.znConfigAsCircle N a := rfl

private theorem circleCosCharacter_eq (n : ℕ) (z : UnitAddCircle) :
    circleCosCharacter n z = ZN.circleCosCharacter n z := rfl

private theorem twistedFlux_eq {B : Box4} (N ξ : ℕ) (S : Chain4 B)
    (θ : Config B) (p : Plaquettes B) :
    disorderTwistedFlux N ξ S θ p = ZN.disorderTwistedFlux N ξ S θ p := by
  unfold disorderTwistedFlux ZN.disorderTwistedFlux
  rw [flux_eq]

private theorem twistedAction_eq {B : Box4} (β : ℝ) (N ξ : ℕ) (S : Chain4 B)
    (θ : Config B) :
    twistedWilsonActionDensity β N ξ S θ =
      ZN.twistedWilsonActionDensity β N ξ S θ := by
  classical
  unfold twistedWilsonActionDensity ZN.twistedWilsonActionDensity
  apply Finset.prod_congr rfl
  intro p hp
  rw [twistedFlux_eq, circleCosCharacter_eq]

private theorem finiteDisorderIntegrand_eq {B : Box4} (β : ℝ) (N ξ : ℕ)
    (h : NNReal) (S : Chain4 B) (θ : Config B) :
    twistedWilsonActionDensity β N ξ S θ * znPinningDensity N h θ =
      ZN.twistedWilsonActionDensity β N ξ S θ * ZN.znPinningDensity N h θ := by
  rw [twistedAction_eq, znPinningDensity_eq]

private theorem finiteDisorderNumerator_eq {B : Box4} (β : ℝ) (N ξ : ℕ)
    (h : NNReal) (S : Chain4 B) :
    finiteDisorderNumerator β N ξ h S = ZN.finiteDisorderNumerator β N ξ h S := by
  unfold finiteDisorderNumerator ZN.finiteDisorderNumerator
  apply MeasureTheory.integral_congr_ae
  exact Filter.Eventually.of_forall (finiteDisorderIntegrand_eq β N ξ h S)

private theorem finiteDisorderExpectation_eq {B : Box4} (β : ℝ) (N ξ : ℕ)
    (h : NNReal) (S : Chain4 B) :
    finiteDisorderExpectation β N ξ h S = ZN.finiteDisorderExpectation β N ξ h S := by
  unfold finiteDisorderExpectation ZN.finiteDisorderExpectation
  rw [finiteDisorderNumerator_eq, finiteZNPartitionFunction_eq]

private theorem centeredSheet_eq {L T M : ℕ} (hL : L ≤ M) (hT : T ≤ M) (hM : 0 < M) :
    centeredRectangularTwistSheet hL hT hM =
      ZN.centeredRectangularTwistSheet hL hT hM := rfl

private theorem finiteCenteredExpectation_eq
    (β : ℝ) (N ξ L T M : ℕ) (h : NNReal)
    (hL : L ≤ M) (hT : T ≤ M) (hM : 0 < M) :
    finiteCenteredDisorderExpectation β N ξ L T M h hL hT hM =
      ZN.finiteCenteredDisorderExpectation β N ξ L T M h hL hT hM := by
  unfold finiteCenteredDisorderExpectation ZN.finiteCenteredDisorderExpectation
  rw [centeredSheet_eq]
  exact finiteDisorderExpectation_eq β N ξ h _

example {B : Box4} : Links B = Wilson.PrimalLinks B := by
  rfl

example {B : Box4} (N : ℕ) : ZNConfig B N = ZN.ZNConfig B N := by
  rfl

private theorem discreteAction_eq {B : Box4} (β : ℝ) (N : ℕ) (a : ZNConfig B N) :
    discreteZNWeight β N a = ZN.discreteZNWeight β N a := by
  unfold discreteZNWeight ZN.discreteZNWeight
  rw [← znConfigAsCircle_eq]
  exact wilsonAction_eq β (znConfigAsCircle N a)

private theorem discreteZNPartitionFunction_eq {B : Box4} (β : ℝ) (N : ℕ) :
    discreteZNPartitionFunction (B := B) β N =
      ZN.discreteZNPartitionFunction (B := B) β N := by
  unfold discreteZNPartitionFunction ZN.discreteZNPartitionFunction
  apply Finset.sum_congr rfl
  intro a ha
  exact discreteAction_eq β N a

private theorem discreteNumerator_eq {B : Box4} (β : ℝ) (N ξ : ℕ) (S : Chain4 B) :
    discreteDisorderNumerator β N ξ S = ZN.discreteDisorderNumerator β N ξ S := by
  unfold discreteDisorderNumerator ZN.discreteDisorderNumerator
  apply Finset.sum_congr rfl
  intro a ha
  rw [← znConfigAsCircle_eq]
  exact twistedAction_eq β N ξ S (znConfigAsCircle N a)

private theorem discreteExpectation_eq {B : Box4} (β : ℝ) (N ξ : ℕ) (S : Chain4 B) :
    discreteDisorderExpectation β N ξ S = ZN.discreteDisorderExpectation β N ξ S := by
  unfold discreteDisorderExpectation ZN.discreteDisorderExpectation
  rw [discreteNumerator_eq, discreteZNPartitionFunction_eq]

private theorem discreteCenteredExpectation_eq
    (β : ℝ) (N ξ L T M : ℕ)
    (hL : L ≤ M) (hT : T ≤ M) (hM : 0 < M) :
    discreteCenteredDisorderExpectation β N ξ L T M hL hT hM =
      ZN.discreteCenteredDisorderExpectation β N ξ L T M hL hT hM := by
  unfold discreteCenteredDisorderExpectation ZN.discreteCenteredDisorderExpectation
  rw [centeredSheet_eq]
  exact discreteExpectation_eq β N ξ _

/-- The literal source root is inherited from the independently proved internal root. -/
theorem fs82_zn_disorder_perimeter_root_provider :
    ∃ C : ℝ, 0 < C ∧ ∀ β : ℝ, 0 < β → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ ξ : ℕ, 1 ≤ ξ → ξ < N → ∀ L T : ℕ, 1 ≤ L → 1 ≤ T →
        ∀ (M : ℕ) (hL : L ≤ M) (hT : T ≤ M) (hbox : 0 < M),
          (∀ h : NNReal,
            Real.exp (-(C * β * ((ξ : ℝ) / (N : ℝ)) ^ 2 * ((L : ℝ) + T))) ≤
              finiteCenteredDisorderExpectation β N ξ L T M h hL hT hbox) ∧
          Real.exp (-(C * β * ((ξ : ℝ) / (N : ℝ)) ^ 2 * ((L : ℝ) + T))) ≤
            discreteCenteredDisorderExpectation β N ξ L T M hL hT hbox := by
  simpa only [finiteCenteredExpectation_eq, discreteCenteredExpectation_eq] using
    ZN.fs82_zn_disorder_perimeter_root

end FroehlichSpencer.FS82.SurfaceZN
end
