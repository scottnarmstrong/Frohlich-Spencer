/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Bridge.WiredBoxCarrier
public import FroehlichSpencer.BKT.FiniteGraph.Laplacian
public import FroehlichSpencer.BKT.Rotator.BesselSchwartz
public import FroehlichSpencer.BKT.Rotator.FiniteComb
public import FroehlichSpencer.BKT.Rotator.SchwartzFiniteProduct

/-!
# Schwartz decay of the pinned interpolated density

The pinned face-coordinate gradient is injective: a field with zero edge differences is constant
on the connected wired face graph, and its pinned exterior value makes that constant zero. The
edge product of one-dimensional Bessel-Schwartz functions is therefore Schwartz after pullback
along this finite-dimensional anti-Lipschitz gradient map.
-/

@[expose] public section

open Complex
open scoped SchwartzMap
open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Duality
open FroehlichSpencer.BKT.Lattice2D
open FroehlichSpencer.BKT.Rotator
open FroehlichSpencer.BKT.Rotator.BesselInterp

noncomputable section

namespace FroehlichSpencer.BKT.Rotator

private theorem rotatorCrossedFreeEdge_adj {L : ℕ} (e : Lattice2D.SquareFreeEdge L) :
    (wiredBoxGraph L).Adj (some ((squareFreeGraph L).src e))
      (some ((squareFreeGraph L).tgt e) : WiredVertex L) := by
  classical
  let c := crossInternalFreeEdge L e
  cases e with
  | inl e =>
      have hstep : e.1.val + 1 < L := e.1.property
      refine ⟨c, Or.inl ⟨?_, ?_⟩⟩
      · simp [c, crossInternalFreeEdge, squareFreeGraph, wiredBoxGraph, wiredBoxSrc,
          verticalPrimalSrc, verticalDualEdge, verticalDualEdgeData, verticalFaceY,
          wiredBoxFinSuccCast]
      · simp [c, crossInternalFreeEdge, squareFreeGraph, wiredBoxGraph, wiredBoxTgt,
          verticalPrimalTgt, verticalDualEdge, verticalDualEdgeData, verticalFaceY,
          wiredBoxFinSuccCast, hstep]
  | inr e =>
      have hstep : e.2.1.val + 1 < L := e.2.2
      refine ⟨c, Or.inr ⟨?_, ?_⟩⟩
      · simp [c, crossInternalFreeEdge, squareFreeGraph, wiredBoxGraph, wiredBoxSrc,
          horizontalPrimalSrc, horizontalDualEdge, horizontalDualEdgeData,
          horizontalFaceX, wiredBoxFinSuccCast, hstep]
      · simp [c, crossInternalFreeEdge, squareFreeGraph, wiredBoxGraph, wiredBoxTgt,
          horizontalPrimalTgt, horizontalDualEdge, horizontalDualEdgeData,
          horizontalFaceX, wiredBoxFinSuccCast]

private theorem rotatorCrossedFreeEdge_adj_map {L : ℕ} (e : Lattice2D.SquareFreeEdge L)
    {a b : SquareFreeVertex L}
    (hs : (squareFreeGraph L).src e = a) (ht : (squareFreeGraph L).tgt e = b) :
    (wiredBoxGraph L).Adj (some a) (some b) := by
  rcases rotatorCrossedFreeEdge_adj e with ⟨ce, hc | hc⟩
  · rcases hc with ⟨hcs, hct⟩
    exact ⟨ce, Or.inl ⟨hcs.trans (congrArg some hs), hct.trans (congrArg some ht)⟩⟩
  · rcases hc with ⟨hcs, hct⟩
    exact ⟨ce, Or.inr ⟨hcs.trans (congrArg some ht), hct.trans (congrArg some hs)⟩⟩

private theorem rotatorCrossedFreeEdge_adj_map_rev {L : ℕ} (e : Lattice2D.SquareFreeEdge L)
    {a b : SquareFreeVertex L}
    (hs : (squareFreeGraph L).src e = b) (ht : (squareFreeGraph L).tgt e = a) :
    (wiredBoxGraph L).Adj (some a) (some b) := by
  rcases rotatorCrossedFreeEdge_adj e with ⟨ce, hc | hc⟩
  · rcases hc with ⟨hcs, hct⟩
    exact ⟨ce, Or.inr ⟨hcs.trans (congrArg some hs), hct.trans (congrArg some ht)⟩⟩
  · rcases hc with ⟨hcs, hct⟩
    exact ⟨ce, Or.inl ⟨hcs.trans (congrArg some ht), hct.trans (congrArg some hs)⟩⟩

/-- The dual face graph of a positive side free box is connected, including the wired exterior
vertex. -/
theorem rotatorDualGraph_connected {L : ℕ} (hL : 0 < L) :
    (rotatorDualGraph L).Connected := by
  classical
  change (wiredBoxGraph L).Connected
  let G := wiredBoxGraph L
  let v0 : SquareFreeVertex L := (⟨0, by omega⟩, ⟨0, by omega⟩)
  let e0 : WiredEdge L := verticalDualEdge ⟨0, by omega⟩ ⟨0, by omega⟩
  have hadj : G.Adj none (some v0) := by
    refine ⟨e0, Or.inl ⟨?_, ?_⟩⟩
    · simp [e0, G, wiredBoxGraph, wiredBoxSrc, verticalPrimalSrc, verticalDualEdge,
        verticalDualEdgeData]
    · simp [e0, v0, G, wiredBoxGraph, wiredBoxTgt, verticalPrimalTgt, verticalDualEdge,
        verticalDualEdgeData, verticalFaceY, hL]
  have hadjSimple : G.toSimpleGraph.Adj none (some v0) := by
    rw [Multigraph.toSimpleGraph_eq_fromRel_adj]
    exact (SimpleGraph.fromRel_adj G.Adj none (some v0)).mpr ⟨by simp, Or.inl hadj⟩
  let H : (squareFreeGraph L).toSimpleGraph →g G.toSimpleGraph := {
    toFun := some
    map_rel' := by
      intro a b hab
      rw [Multigraph.toSimpleGraph_eq_fromRel_adj] at hab
      rcases (SimpleGraph.fromRel_adj (squareFreeGraph L).Adj a b).mp hab with
        ⟨hne, hrel | hrel⟩
      · rcases hrel with ⟨e, hedge | hedge⟩
        · rw [Multigraph.toSimpleGraph_eq_fromRel_adj]
          apply (SimpleGraph.fromRel_adj G.Adj (some a) (some b)).mpr
          refine ⟨?_, Or.inl (rotatorCrossedFreeEdge_adj_map e hedge.1 hedge.2)⟩
          intro h
          exact hne (Option.some.inj h)
        · rw [Multigraph.toSimpleGraph_eq_fromRel_adj]
          apply (SimpleGraph.fromRel_adj G.Adj (some a) (some b)).mpr
          refine ⟨?_, Or.inl (rotatorCrossedFreeEdge_adj_map_rev e hedge.1 hedge.2)⟩
          intro h
          exact hne (Option.some.inj h)
      · rcases hrel with ⟨e, hedge | hedge⟩
        · rw [Multigraph.toSimpleGraph_eq_fromRel_adj]
          apply (SimpleGraph.fromRel_adj G.Adj (some a) (some b)).mpr
          refine ⟨?_, Or.inl (rotatorCrossedFreeEdge_adj_map_rev e hedge.1 hedge.2)⟩
          intro h
          exact hne (Option.some.inj h)
        · rw [Multigraph.toSimpleGraph_eq_fromRel_adj]
          apply (SimpleGraph.fromRel_adj G.Adj (some a) (some b)).mpr
          refine ⟨?_, Or.inl (rotatorCrossedFreeEdge_adj_map e hedge.1 hedge.2)⟩
          intro h
          exact hne (Option.some.inj h)
  }
  have hgrid : (squareFreeGraph L).Connected := squareFreeGraph_connected hL
  have hroot (v : WiredVertex L) : G.toSimpleGraph.Reachable none v := by
    cases v with
    | none => exact SimpleGraph.Reachable.refl _
    | some p =>
        have hp : G.toSimpleGraph.Reachable (some v0) (some p) :=
          (hgrid.preconnected v0 p).map H
        have h0 : G.toSimpleGraph.Reachable none (some v0) := hadjSimple.reachable
        exact h0.trans hp
  change G.Connected
  rw [Multigraph.Connected, SimpleGraph.connected_iff]
  constructor
  · intro u v
    exact (hroot u).symm.trans (hroot v)
  · exact ⟨none⟩

/-- The pinned real face field associated with bounded-face coordinates. -/
def rotatorPinnedCoordsField {L : ℕ} (x : SquareFreeVertex L → ℝ) :
    RotatorDualFace L → ℝ := fun p => p.elim 0 x

/-- The real edge-gradient map from pinned face coordinates to oriented spin-bond coordinates. -/
def rotatorCoordsGradientLinearMap (L : ℕ) :
    (SquareFreeVertex L → ℝ) →ₗ[ℝ] (RotatorInternalBond L → ℝ) where
  toFun x e :=
    rotatorPinnedCoordsField x ((rotatorDualGraph L).src e) -
      rotatorPinnedCoordsField x ((rotatorDualGraph L).tgt e)
  map_add' x y := by
    funext e
    have hcoord (p : RotatorDualFace L) :
        rotatorPinnedCoordsField (x + y) p =
          rotatorPinnedCoordsField x p + rotatorPinnedCoordsField y p := by
      cases p <;> simp [rotatorPinnedCoordsField]
    simp only [hcoord, Pi.add_apply]
    ring
  map_smul' c x := by
    funext e
    have hcoord (p : RotatorDualFace L) :
        rotatorPinnedCoordsField (c • x) p =
          c * rotatorPinnedCoordsField x p := by
      cases p <;> simp [rotatorPinnedCoordsField]
    simp only [hcoord, Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    ring

/-- The coordinate gradient is injective: zero edge gradients make the pinned field constant on
the connected dual face graph. -/
theorem rotatorCoordsGradientLinearMap_injective (L : ℕ) :
    Function.Injective (rotatorCoordsGradientLinearMap L) := by
  by_cases hL : 0 < L
  · intro x y hxy
    let G := rotatorDualGraph L
    let z := x - y
    let φ : RotatorDualFace L → ℝ := rotatorPinnedCoordsField z
    have hzero : rotatorCoordsGradientLinearMap L z = 0 := by
      calc
        rotatorCoordsGradientLinearMap L z =
            rotatorCoordsGradientLinearMap L x - rotatorCoordsGradientLinearMap L y :=
              (rotatorCoordsGradientLinearMap L).map_sub x y
        _ = 0 := by rw [hxy]; simp
    have hgrad (e : RotatorInternalBond L) : G.grad φ e = 0 := by
      have h := congrFun hzero e
      simpa [G, z, φ, rotatorCoordsGradientLinearMap, Multigraph.grad] using h
    have henergy : G.energy φ = 0 := by
      unfold Multigraph.energy
      apply Finset.sum_eq_zero
      intro e he
      have h0 : (G.grad φ e) ^ 2 = 0 := by rw [hgrad e]; simp
      simpa [Multigraph.grad] using h0
    obtain ⟨c, hc⟩ := (G.energy_eq_zero_iff_exists_const
      (rotatorDualGraph_connected hL) φ).mp henergy
    have hc0 : c = 0 := by
      have h := congrFun hc none
      simpa [φ, rotatorPinnedCoordsField] using h.symm
    apply funext
    intro v
    have h := congrFun hc (some v)
    have hv : x v - y v = c := by
      simpa [φ, z, rotatorPinnedCoordsField] using h
    rw [hc0] at hv
    exact sub_eq_zero.mp hv
  · have hLzero : L = 0 := by omega
    subst L
    intro x y hxy
    exact Subsingleton.elim _ _

/-- The pinned interpolated density in bounded-face coordinates has an actual Schwartz
representative for every positive interpolation parameter `β ≥ 1`. -/
theorem exists_rotatorPinnedInterpolatedDensityCoords_schwartz {L : ℕ} {β : ℝ}
    (hβ : 1 ≤ β) :
    ∃ f : 𝓢(SquareFreeVertex L → ℝ, ℂ),
      ∀ x, f x = rotatorPinnedInterpolatedDensityCoords L β x := by
  let bessel : 𝓢(ℝ, ℂ) := besselInterpRealSchwartz β hβ
  obtain ⟨edgeProduct, hedgeProduct⟩ :=
    exists_schwartz_pi_product (ι := RotatorInternalBond L) bessel
  let grad : (SquareFreeVertex L → ℝ) →L[ℝ] (RotatorInternalBond L → ℝ) :=
    (rotatorCoordsGradientLinearMap L).toContinuousLinearMap
  obtain ⟨K, hK, hanti⟩ :=
    (rotatorCoordsGradientLinearMap L).injective_iff_antilipschitz.mp
      (rotatorCoordsGradientLinearMap_injective L)
  have hanti' : AntilipschitzWith K grad := by
    change AntilipschitzWith K (rotatorCoordsGradientLinearMap L)
    exact hanti
  let f : 𝓢(SquareFreeVertex L → ℝ, ℂ) :=
    (SchwartzMap.compCLMOfAntilipschitz ℂ grad.hasTemperateGrowth hanti') edgeProduct
  refine ⟨f, fun x => ?_⟩
  have hcomp : f x = edgeProduct (grad x) := by
    change ((SchwartzMap.compCLMOfAntilipschitz ℂ grad.hasTemperateGrowth hanti')
      edgeProduct) x = edgeProduct (grad x)
    simp only [SchwartzMap.compCLMOfAntilipschitz_apply, Function.comp_apply]
  rw [hcomp]
  calc
    edgeProduct (grad x) = ∏ e : RotatorInternalBond L,
        besselInterp β ((grad x e : ℝ) : ℂ) := by
      rw [hedgeProduct]
      apply Finset.prod_congr rfl
      intro e he
      rfl
    _ = rotatorPinnedInterpolatedDensityCoords L β x := by
      symm
      simp [rotatorPinnedInterpolatedDensityCoords, rotatorPinnedInterpolatedDensity,
        rotatorCoordsGradientLinearMap, rotatorPinnedCoordsField,
        rotatorPinnedRealFieldOfCoords, grad]

end FroehlichSpencer.BKT.Rotator

end
