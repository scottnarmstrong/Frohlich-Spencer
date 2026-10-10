/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.VillainDisorder.Dirichlet.MarkedGeometryAssemblyRemainderWaves
public import FroehlichSpencer.BKT.VillainDisorder.Dirichlet.MarkedGeometryAssemblyNeighbour
public import FroehlichSpencer.BKT.VillainDisorder.Dirichlet.MarkedGeometryAssemblyWitness
public import FroehlichSpencer.BKT.VillainDisorder.Dirichlet.MarkedGeometryBudget
import Mathlib.Tactic

/-!
`RootedFejerMarkedExtension` (`MarkedInterface.lean`) asks, on every branch of some rooted Fejér witness,
for:
* a monotone adjacency;
* the neighbour count;
* the renormalization data of every marked term.

**`rootedFejerMarkedExtension_holds` proves it unconditionally.** It uses:
* `γ₀ = markedBudgetConstant`, `s₀ = 1`, `K_nb = rootedMarkNeighbourConst`, the buffer `R₀ = 2n`;
* the adjacency `RootedMarkAdjacent chargeCoverScale chargeCoverExponent`;
* the witness `rootedFejerLayer_exists_comb`, whose branch ensembles are comb terminals.

It is
  orthogonal to the remainder charges, and its energy is at least the profile budget's right-hand
  side over `τ`.

C1's `rootedMarkedProfileBudget` (`MarkedGeometryBudget.lean`, buffer `2n ≤ R`)
  turns that into the gain `γ₀ η²/τ (∑_C A + log₂(n + 1))`.
* `exists_rootedMarkedRemainderWaves`: the remainder waves, built for this explicit `a₀` from the
  same extended family as its profiles.
* `sum_exp_neg_layerA_rootedMarkNeighbour_le`: the neighbour count.

The opaque `rootedMarkedCompositeWaveGoal` (an `∃ a₀`) is not consumed as such.

The remainder goal
for an arbitrary composite wave is strictly stronger than the term field; see
`not_remainderWaveGoalForAll_triangle` in `MarkedGeometryAssemblyObstruction.lean`.

The remainder
waves must avoid the gradient of the particular `a₀`.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.VillainDisorder.Dirichlet

open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Generic
open FroehlichSpencer.BKT.Generic.SpinWave
open FroehlichSpencer.BKT.Generic.Marked
open FroehlichSpencer.BKT.Generic.PinnedCharges
open FroehlichSpencer.BKT.Generic.PinnedCharges.Layer
open FroehlichSpencer.BKT.Generic.PinnedCharges.SelectionG
open FroehlichSpencer.BKT.Rotator
open FroehlichSpencer.BKT.Lattice2D

variable {R n : ℕ}


theorem pairing_add_sum {V : Type*} [Fintype V] (c₀ : ℝ) (b : V → ℝ) {ι : Type*} [Fintype ι]
    (q : ι → ℝ) (ψ : ι → V → ℝ) (g : V → ℝ) :
    Multigraph.pairing (fun j => c₀ * b j + ∑ t, q t * ψ t j) g =
      c₀ * Multigraph.pairing b g + ∑ t, q t * Multigraph.pairing (ψ t) g := by
  unfold Multigraph.pairing
  simp only [add_mul, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm (f := fun j t => q t * ψ t j * g j)]
  congr 1
  · exact Finset.sum_congr rfl fun j _ => by ring
  · exact Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun j _ => by ring


theorem rootedMarkedProfileWave_composite (hn : n ≤ R) (hn0 : 0 < n) {ξ τ : ℝ} (hξ0 : 0 < ξ)
    (hξ1 : ξ < 1) (hτ : 0 < τ) (F : Finset (ChargeDensity (sideLength R)))
    (hgeo : AppendixDChargeGeometry (chargeCoverScale : ℝ) chargeCoverExponent F)
    (C : Finset (RotatorDualFace (sideLength R) → ℤ))
    (hC : C ∈ clusters (RootedMarkAdjacent (chargeCoverScale : ℝ) chargeCoverExponent R n hn)
      (F.image neutralizeAtWiredRoot))
    (T : Finset (RotatorDualFace (sideLength R) → ℤ)) (hT : T ⊆ C)
    (hL : 1 < sideLength R) :
    let σ := rootedMarkedComposite ξ (rootedDipoleMark R n hn) C T
    let p := rootedMarkedProxy R n hn C T
    let ψ := rootedMarkedP4Wave (rootedMarkedExtFaces R n hn (F.image neutralizeAtWiredRoot) C T) p
    let a₀ := rootedMarkedProfileWave R n hn ξ (F.image neutralizeAtWiredRoot) C T (1 / (4 * τ))
      (fun t => Multigraph.pairing (ψ t) σ / (τ * 6400))
    (∀ ϱ ∈ remainder (RootedMarkAdjacent (chargeCoverScale : ℝ) chargeCoverExponent R n hn)
        (F.image neutralizeAtWiredRoot) C, Multigraph.pairing a₀ (fun j => (ϱ j : ℝ)) = 0) ∧
      ((∑ x : SquareFreeVertex (sideLength R), σ (some x) ^ 2) / 16 +
        dipoleGap ξ ^ 2 / 12800 * Fintype.card (rootedMarkedP4Index p)) / τ ≤
        gffTranslationEnergy (squareZero (sideLength R)) τ a₀ σ := by
  intro σ p ψ a₀
  classical
  obtain ⟨hroot, -, hgap, hdisj, hbaseDisj, hbaseOrth, hprofileOrth⟩ :=
    rootedMarkedComposite_profileGeometry hn hn0 (M := (chargeCoverScale : ℝ))
      (α := chargeCoverExponent) (ξ := ξ) (by norm_num [chargeCoverScale])
      (le_trans zero_le_one one_le_chargeCoverExponent) rfl rfl hξ0 hξ1 F hgeo C hC T hT hL
  refine ⟨fun ϱ hϱ => ?_, ?_⟩
  · show Multigraph.pairing (fun j => 1 / (4 * τ) * rootedRealSquareBaseWave σ j +
      ∑ t, Multigraph.pairing (ψ t) σ / (τ * 6400) * ψ t j) (fun j => (ϱ j : ℝ)) = 0
    rw [pairing_add_sum, hbaseOrth ϱ hϱ, mul_zero, zero_add]
    exact Finset.sum_eq_zero fun t _ => mul_eq_zero_of_right _ (hprofileOrth t ϱ hϱ)
  · exact rootedMarkedProfileEnergyLowerBound hτ σ ψ (fun t => Multigraph.pairing (ψ t) σ)
      (le_of_lt (dipoleGap_pos hξ0 hξ1)) (fun _ => rfl) hgap (fun t => (hroot t).2) hdisj
      hbaseDisj

/-! ### The term data of one marked term -/

/-- **The renormalization data of one marked term**, from the profile budget of its composite. -/
theorem rootedMarkedTermData_of_budget (hn : n ≤ R) (hn0 : 0 < n)
    {ξ τ gain : ℝ} (hξ0 : 0 < ξ) (hξ1 : ξ < 1) (hτ : 0 < τ)
    (F : Finset (ChargeDensity (sideLength R)))
    (hgeo : AppendixDChargeGeometry (chargeCoverScale : ℝ) chargeCoverExponent F)
    (hbad : ∀ ϱ ∈ F.image neutralizeAtWiredRoot, badSelectedSum ϱ ≤ ∑ j, |(ϱ j : ℝ)|)
    (K : (RotatorDualFace (sideLength R) → ℤ) → ℝ)
    (hK : ∀ ϱ ∈ F.image neutralizeAtWiredRoot, |K ϱ| ≤ Real.exp (fejerLayerD₂ * layerA ϱ))
    {amp : ℝ} {k₀ : ℕ} (hamp : 0 ≤ amp) (hk₀ : 1 ≤ k₀)
    (hs : 0 ≤ amp / (8 * fejerLayerD₁) - fejerLayerD₂)
    (hquad₂ : amp ≤ (2 : ℝ) ^ (gradExponent (7 / 4) * k₀) / 8)
    (hexp : 100 * 4 ^ k₀ * costMajorant (τ / 2) (τ / 2) (amp * 8) ≤ amp / 2)
    (hquad₁ : amp ≤ 1 / (2 * (τ / 2) * 6400))
    (C : Finset (RotatorDualFace (sideLength R) → ℤ))
    (hC : C ∈ clusters (RootedMarkAdjacent (chargeCoverScale : ℝ) chargeCoverExponent R n hn)
      (F.image neutralizeAtWiredRoot))
    (T : Finset (RotatorDualFace (sideLength R) → ℤ)) (hT : T ⊆ C)
    (hL : 1 < sideLength R)
    (hbudget : gain ≤ ((∑ x : SquareFreeVertex (sideLength R),
        (rootedMarkedComposite ξ (rootedDipoleMark R n hn) C T (some x)) ^ 2) / 16 +
        dipoleGap ξ ^ 2 / 12800 *
          Fintype.card (rootedMarkedP4Index (rootedMarkedProxy R n hn C T))) / τ) :
    RootedMarkedTermData (squareZero (sideLength R)) τ K
      (rootedMarkedComposite ξ (rootedDipoleMark R n hn) C T)
      (remainder (RootedMarkAdjacent (chargeCoverScale : ℝ) chargeCoverExponent R n hn)
        (F.image neutralizeAtWiredRoot) C) gain := by
  obtain ⟨horth, henergy⟩ :=
    rootedMarkedProfileWave_composite hn hn0 hξ0 hξ1 hτ F hgeo C hC T hT hL
  obtain ⟨a, h₁, h₂, h₃, h₄, h₅⟩ := exists_rootedMarkedRemainderWaves hn hn0 hξ0 hξ1 hτ F hgeo
    hbad K hK hamp hk₀ hs hquad₂ hexp hquad₁ C hC T hT hL (1 / (4 * τ))
    (fun t => Multigraph.pairing (rootedMarkedP4Wave
      (rootedMarkedExtFaces R n hn (F.image neutralizeAtWiredRoot) C T)
      (rootedMarkedProxy R n hn C T) t)
        (rootedMarkedComposite ξ (rootedDipoleMark R n hn) C T) / (τ * 6400))
  exact ⟨_, a, horth, h₁, h₂, h₃, h₄, h₅, hbudget.trans henergy⟩

/-! ### The marked extension -/

theorem fejerLayerD₁_pos : 0 < fejerLayerD₁ := by
  unfold fejerLayerD₁
  have := layerD₁_pos
  positivity

/-- **The marked extension of the rooted Fejér layer** (D2's input `RootedFejerMarkedExtension`),
with `γ₀ = markedBudgetConstant`, `s₀ = 1`, `K_nb = rootedMarkNeighbourConst` and the buffer
`R₀ = 2n`. -/
theorem rootedFejerMarkedExtension_holds : RootedFejerMarkedExtension := by
  refine ⟨markedBudgetConstant, 1, rootedMarkNeighbourConst, markedBudgetConstant_pos,
    rootedMarkNeighbourConst_nonneg, ?_⟩
  intro η hη0 hη1
  obtain ⟨amp, k₀, τ₁, hamp, hk₀, hτ₁, hs, hquad₂, hτpar⟩ :=
    exists_gaussianActivity_params (α := 7 / 4) (K₀ := 6400) (K₁ := 8) (D₁ := fejerLayerD₁)
      (D₂ := fejerLayerD₂) (by norm_num) (by norm_num) (by norm_num) fejerLayerD₁_pos 0
  refine ⟨τ₁, hτ₁, ?_⟩
  intro τ hτ hττ ξ hξ0 hξ1 hηξ hηξ' n hn1
  refine ⟨2 * n, by omega, ?_⟩
  intro R hR hn N hN
  have hn0 : 0 < n := by omega
  have hRn : 2 * n ≤ R := hR
  have hL2 : 2 ≤ sideLength R := by unfold sideLength; omega
  have hL : 1 < sideLength R := by omega
  obtain ⟨hexp, hquad₁⟩ := hτpar τ hτ hττ
  have hs' : 0 ≤ amp / (8 * fejerLayerD₁) - fejerLayerD₂ := by linarith
  obtain ⟨W, hW⟩ := rootedFejerLayer_exists_comb hL2 hN
  refine ⟨W, RootedMarkAdjacent (chargeCoverScale : ℝ) chargeCoverExponent R n hn, fun i => ?_⟩
  obtain ⟨T, hT, hNi⟩ := hW i
  have hgeo := hT.geometry
  have hK : ∀ ϱ ∈ T.F.image neutralizeAtWiredRoot,
      |W.layer.K i ϱ| ≤ Real.exp (fejerLayerD₂ * layerA ϱ) := by
    intro ϱ hϱ
    have h := W.layer.entropy i ϱ (hNi ▸ hϱ)
    simpa only [mul_one] using h
  have hℓ : 0 ≤ Real.logb 2 ((n : ℝ) + 1) :=
    Real.logb_nonneg (by norm_num) (by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)
  rw [hNi]
  refine ⟨rootedMarkAdjacent_monotone (by norm_num [chargeCoverScale])
    (le_trans zero_le_one one_le_chargeCoverExponent) hn, ?_, ?_⟩
  · intro C _
    exact sum_exp_neg_layerA_rootedMarkNeighbour_le hn hn0 T.F hgeo C hℓ
  · intro C hC T' hT'
    have hbudget := rootedMarkedProfileBudget hn hn0 hRn hξ0 hξ1 hgeo hC hT'
    refine rootedMarkedTermData_of_budget hn hn0 hξ0 hξ1 hτ T.F hgeo
      (badSelectedBound_proof _ N T hT) (W.layer.K i) hK hamp hk₀ hs' hquad₂ hexp hquad₁ C hC
      T' hT' hL ?_
    rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hτ]
    have hηg : η ^ 2 ≤ dipoleGap ξ ^ 2 := by
      have : η ≤ dipoleGap ξ := le_min hηξ hηξ'
      nlinarith
    have hcost : 0 ≤ ∑ m ∈ C, layerA m + Real.logb 2 ((n : ℝ) + 1) :=
      add_nonneg (Finset.sum_nonneg fun m _ => layerA_nonneg_of_sum m) hℓ
    calc markedBudgetConstant * η ^ 2 * (∑ m ∈ C, layerA m + Real.logb 2 ((n : ℝ) + 1))
        ≤ markedBudgetConstant * dipoleGap ξ ^ 2 *
            (∑ m ∈ C, layerA m + Real.logb 2 ((n : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hηg markedBudgetConstant_pos.le) hcost
      _ ≤ _ := hbudget

end FroehlichSpencer.BKT.VillainDisorder.Dirichlet

end
