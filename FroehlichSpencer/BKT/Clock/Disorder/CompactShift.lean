/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Clock.Compact.Assembly
public import FroehlichSpencer.BKT.Clock.Disorder.VortexProfile
import Mathlib.Tactic

/-!
# Compact clock shift for the disorder seam

The vortex decomposition turns the twisted bond product into an offset clock bond product after
translating the angle field. The compact-law charge-layer assembly then handles the translated
comb through compatible-character phases.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Clock.Disorder

open MeasureTheory
open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Generic
open FroehlichSpencer.BKT.Clock.Compact
open FroehlichSpencer.BKT.Clock.Periodic

/-- The finite compact-angle edge product with an additive bond field. -/
def compactClockBondProduct {V E : Type*} [Fintype E]
    (G : Multigraph V E) (β n : ℝ) (φ : V → ℝ) (t : E → ℝ) : ℝ :=
  ∏ e, Real.exp (β * Real.cos ((G.grad φ e + t e) / n))

private theorem grad_add_local {V E : Type*} (G : Multigraph V E)
    (φ ψ : V → ℝ) : G.grad (φ + ψ) = G.grad φ + G.grad ψ := by
  funext e
  simp [Multigraph.grad]
  ring

/-- A bond twist equal to `∇ψ + θ` is the offset weight evaluated at `φ + ψ`. This is the
pointwise change of variables used before applying the compact-law charge-layer assembly. -/
theorem compactClockBondProduct_twist_eq_shiftedOffset {V E : Type*} [Fintype E]
    (G : Multigraph V E) (β n : ℝ) (φ ψ : V → ℝ) (t θ : E → ℝ)
    (ht : ∀ e, t e = G.grad ψ e + θ e) :
    compactClockBondProduct G β n φ t =
      compactClockBondProduct G β n (φ + ψ) θ := by
  unfold compactClockBondProduct
  rw [grad_add_local]
  apply Finset.prod_congr rfl
  intro e he
  congr 1
  rw [ht e]
  congr 1
  simp only [Pi.add_apply]
  ring_nf

/-- The compact clock charge-layer identity specialized to the shift produced by the vortex
profile. In a free square, use `clockLaw_renormalization_kp` to construct `CL` and its root clause. -/
theorem clockLaw_chargeLayer_expansion_atShift {V E : Type} [Fintype V] [Fintype E]
    [DecidableEq V] {G : Multigraph V E} {lam : V → ℝ → ℝ}
    {centerOf : (V → ℤ) → V} {A Zent : (V → ℤ) → ℝ}
    {D₁ D₂ α K₀ K₁ : ℝ} {n : ℕ} (hn : 0 < n) {β : ℝ} (hβ : 0 ≤ β)
    (CL : ChargeLayer G lam centerOf A Zent D₁ D₂ α K₀ K₁)
    (hroot : ∀ i, CL.R i = neutralPart (CL.N i) ∧ AtMostOneNonNeutral (CL.N i))
    {κ κ' W : ℝ} (hc : IsCostEnvelope (clockShiftCost β n) κ κ' W)
    (hκ : 0 < κ) (hK₀ : 0 < K₀) (hK₁ : 0 < K₁) (hD₁ : 0 < D₁)
    {amp : ℝ} (hamp : 0 ≤ amp) (hampW : amp * K₁ ≤ W) (hW1 : 1 ≤ W)
    {k₀ : ℕ} (hk₀ : 1 ≤ k₀)
    (hexp : 100 * 4 ^ k₀ * costMajorant κ κ' (amp * K₁) ≤ amp / 2)
    (hquad₁ : amp ≤ 1 / (2 * κ * K₀))
    (hquad₂ : amp ≤ (2 : ℝ) ^ (gradExponent α * k₀) / K₁)
    (ψ : V → ℝ) :
    ∃ (z : Fin CL.n → (V → ℤ) → ℝ) (a : Fin CL.n → (V → ℤ) → V → ℝ),
      ∫ φ, ((∏ j, lam j (φ j + ψ j) : ℝ) : ℂ) ∂clockLaw β n G =
        ∑ i, (CL.c i : ℂ) * ∫ φ, ∏ ϱ ∈ CL.R i, ((1 : ℂ) + (z i ϱ : ℂ) *
          localFactor (clockEdgeWeight β n) (clockShiftCost β n)
            (gradLinear G (a i ϱ)) (gradLinear G φ)
            (∑ j, φ j * (ϱ j : ℝ) + ∑ j, ψ j * (ϱ j : ℝ))) ∂clockLaw β n G := by
  obtain ⟨z, a, hid, _⟩ := clockLaw_renormalization_of_chargeLayer hn hβ CL hroot hc hκ
    hK₀ hK₁ hD₁ hamp hampW hW1 hk₀ hexp hquad₁ hquad₂
  exact ⟨z, a, hid ψ⟩

end FroehlichSpencer.BKT.Clock.Disorder

end
