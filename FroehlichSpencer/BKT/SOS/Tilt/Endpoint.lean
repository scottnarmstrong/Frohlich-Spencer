/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.SOS.Tilt.Translate
public import FroehlichSpencer.BKT.Generic.Rooted.LayerD
public import FroehlichSpencer.BKT.Generic.Rooted.LocalPacking
import Mathlib.Algebra.Order.Chebyshev

/-!
# The endpoint sum of a rooted D-layer (the dipole tilt construction: condition (★), generic form)

Under the tilt `e^{⟨∇φ, b⟩}` the renormalized factor of the density `ρ` acquires the endpoint phase
`⟨∇a_ρ, b⟩` (`rootedD_identity_of_law_phased`), and the tilted moment bound
(`integral_tilt_ge_of_rootedLayerD`) loses `16 Λ` with `Λ ≥ ∑_ρ |z(ρ)| ⟨∇a_ρ, b⟩²`. This is
FS81's endpoint term `Λ_end` of (★).

The endpoint sum is packed like the phase errors of the real shift (KP Claim 3.2): the gradient of
`a_ρ` lives on the local edge set `S(ρ)` and is bounded by `M`, so by Cauchy–Schwarz
`⟨∇a_ρ, b⟩² ≤ |S(ρ)| M² ∑_{e ∈ S(ρ)} b(e)² ≤ K_v M² (d(ρ)+1)² ∑_{e ∈ S(ρ)} b(e)²`, and the bounded
same-scale overlap of the sets `S(ρ)` gives (`sum_abs_mul_le_of_overlap`)

`∑_ρ |z(ρ)| ⟨∇a_ρ, b⟩² ≤ ε_end ∑_e b(e)²`,

with `ε_end` the threshold of the activity decay. No locality of the waves themselves is needed:
only the layer's own local edge sets and overlap bound (`RootedChargeLayerD.IsLocal`).

* `tiltExponent_rootedSpinWaveD_sq_le`: the per-density bound;
* `sum_abs_mul_tiltExponent_sq_le`: the packed endpoint sum.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.SOS.Tilt

open Finset
open FroehlichSpencer.BKT.Generic

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V]
  {G : Multigraph V E} {root : V} {lam : V → ℝ → ℝ} {centerOf : (V → ℤ) → V}
  {A Zent : (V → ℤ) → ℝ} {D₁ D₂ α K₀ K₁ : ℝ}

/-- **One endpoint phase**: `⟨∇a_ρ, b⟩² ≤ K_v M² (d(ρ)+1)² ∑_{e ∈ S(ρ)} b(e)²`. -/
theorem tiltExponent_rootedSpinWaveD_sq_le
    (CL : RootedChargeLayerD G root lam centerOf A Zent D₁ D₂ α K₀ K₁)
    {dsc : (V → ℤ) → ℕ} {Kv : ℝ} {Kov : ℕ} (hloc : CL.IsLocal dsc Kv Kov) (κ amp : ℝ) (k₀ : ℕ)
    {Mw : ℝ} (hMw : ∀ i, ∀ ϱ ∈ CL.N i, ∀ e, |G.grad (rootedSpinWaveD CL κ amp k₀ i ϱ) e| ≤ Mw)
    (bt : E → ℝ) (i : Fin CL.n) (ϱ : V → ℤ) (hϱ : ϱ ∈ CL.N i) :
    tiltExponent (gradLinear G) bt (rootedSpinWaveD CL κ amp k₀ i ϱ) ^ 2 ≤
      Kv * Mw ^ 2 * ((dsc ϱ : ℝ) + 1) ^ 2 * ∑ e ∈ CL.S i ϱ, bt e ^ 2 := by
  set a := rootedSpinWaveD CL κ amp k₀ i ϱ with ha
  have h1 : tiltExponent (gradLinear G) bt a = ∑ e ∈ CL.S i ϱ, bt e * G.grad a e := by
    unfold tiltExponent
    simp only [gradLinear_apply]
    refine (Finset.sum_subset (Finset.subset_univ _) fun e _ he => ?_).symm
    by_contra hne
    exact he (grad_rootedSpinWaveD_mem CL κ amp k₀ i ϱ hϱ e (right_ne_zero_of_mul hne))
  have h2 := sq_sum_le_card_mul_sum_sq (s := CL.S i ϱ) (f := fun e => bt e * G.grad a e)
  have h3 : ∀ e, (bt e * G.grad a e) ^ 2 ≤ Mw ^ 2 * bt e ^ 2 := fun e => by
    have hg : G.grad a e ^ 2 ≤ Mw ^ 2 := by
      rw [← sq_abs (G.grad a e)]
      exact pow_le_pow_left₀ (abs_nonneg _) (hMw i ϱ hϱ e) 2
    rw [mul_pow, mul_comm (Mw ^ 2)]
    exact mul_le_mul_of_nonneg_left hg (sq_nonneg _)
  have h4 : ∑ e ∈ CL.S i ϱ, (bt e * G.grad a e) ^ 2 ≤ Mw ^ 2 * ∑ e ∈ CL.S i ϱ, bt e ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun e _ => h3 e
  have hcard := hloc.card_le i ϱ hϱ
  have hS0 : 0 ≤ ∑ e ∈ CL.S i ϱ, bt e ^ 2 := Finset.sum_nonneg fun e _ => sq_nonneg _
  have hM0 : 0 ≤ Mw ^ 2 * ∑ e ∈ CL.S i ϱ, bt e ^ 2 := mul_nonneg (sq_nonneg _) hS0
  rw [h1]
  calc (∑ e ∈ CL.S i ϱ, bt e * G.grad a e) ^ 2
      ≤ ((CL.S i ϱ).card : ℝ) * ∑ e ∈ CL.S i ϱ, (bt e * G.grad a e) ^ 2 := h2
    _ ≤ ((CL.S i ϱ).card : ℝ) * (Mw ^ 2 * ∑ e ∈ CL.S i ϱ, bt e ^ 2) :=
        mul_le_mul_of_nonneg_left h4 (Nat.cast_nonneg _)
    _ ≤ (Kv * ((dsc ϱ : ℝ) + 1) ^ 2) * (Mw ^ 2 * ∑ e ∈ CL.S i ϱ, bt e ^ 2) :=
        mul_le_mul_of_nonneg_right hcard hM0
    _ = Kv * Mw ^ 2 * ((dsc ϱ : ℝ) + 1) ^ 2 * ∑ e ∈ CL.S i ϱ, bt e ^ 2 := by ring

/-- **The packed endpoint sum** (FS81's `Λ_end`, generic form):
`∑_ρ |z(ρ)| ⟨∇a_ρ, b⟩² ≤ ε_end ∑_e b(e)²` whenever the activities decay as
`e^{−b(‖ρ‖₁ + log₂(d(ρ)+1))}` and `ε_end` is above the threshold. -/
theorem sum_abs_mul_tiltExponent_sq_le
    (CL : RootedChargeLayerD G root lam centerOf A Zent D₁ D₂ α K₀ K₁)
    {dsc : (V → ℤ) → ℕ} {Kv : ℝ} {Kov : ℕ} (hloc : CL.IsLocal dsc Kv Kov) (hKv : 0 ≤ Kv)
    (κ amp : ℝ) (k₀ : ℕ) {Mw : ℝ}
    (hMw : ∀ i, ∀ ϱ ∈ CL.N i, ∀ e, |G.grad (rootedSpinWaveD CL κ amp k₀ i ϱ) e| ≤ Mw)
    (z : Fin CL.n → (V → ℤ) → ℝ) (b εe : ℝ)
    (hz : ∀ i, ∀ ϱ ∈ CL.N i, |z i ϱ| ≤
      Real.exp (-b * (∑ j, |(ϱ j : ℝ)| + Real.logb 2 (dsc ϱ + 1))))
    (hthr : ∀ d u : ℝ, 1 ≤ d → 2 ≤ u →
      (Kov : ℝ) * (Kv * Mw ^ 2) * (d + 1) ^ (2 + 1) * u ^ 0 *
        Real.exp (-b * (u + Real.logb 2 (d + 1))) ≤ εe)
    (bt : E → ℝ) (i : Fin CL.n) :
    ∑ ϱ ∈ CL.N i, |z i ϱ| *
        tiltExponent (gradLinear G) bt (rootedSpinWaveD CL κ amp k₀ i ϱ) ^ 2 ≤
      εe * ∑ e, bt e ^ 2 :=
  sum_abs_mul_le_of_overlap dsc (CL.S i) Kov (Kv * Mw ^ 2) (mul_nonneg hKv (sq_nonneg _)) 2 0
    (fun e => bt e ^ 2) (fun e => sq_nonneg _)
    (fun ϱ => tiltExponent (gradLinear G) bt (rootedSpinWaveD CL κ amp k₀ i ϱ) ^ 2) (CL.N i)
    (hloc.ne_zero i) (CL.neutral i) (hloc.one_le_dsc i)
    (fun ϱ hϱ => by
      rw [pow_zero, mul_one]
      exact tiltExponent_rootedSpinWaveD_sq_le CL hloc κ amp k₀ hMw bt i ϱ hϱ)
    (hloc.overlap i) (z i) b εe (hz i) hthr

end FroehlichSpencer.BKT.SOS.Tilt

end
