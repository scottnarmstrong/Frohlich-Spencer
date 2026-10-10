/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Gaussian.Normalization
public import FroehlichSpencer.BKT.FiniteGraph.Green
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Tactic.Ring

/-!
# Exponential moments of the rooted finite-volume Gaussian free field

The real zero-sum exponential moment is KP (1.4), p. 2. Its proof translates
by the pinned solution of KP (1.5) and completes the square in the edge energy.
-/

@[expose] public section

namespace FroehlichSpencer.BKT

universe u v

open MeasureTheory Multigraph

variable {V : Type u} {E : Type v}

/-- The pinned translate solving `-Δ σ = f / β`, as in KP (1.5), p. 2. -/
noncomputable def gffShift (G : Multigraph V E) [Fintype V] [Fintype E]
    [DecidableEq V] (hG : G.Connected) (β : ℝ) (f : V → ℝ)
    (root : V) : V → ℝ :=
  fun j => -(G.greenOp hG f j) / β + G.greenOp hG f root / β

/-- The KP translate is pinned at the selected root. -/
@[simp]
theorem gffShift_root (G : Multigraph V E) [Fintype V] [Fintype E]
    [DecidableEq V] (hG : G.Connected) (β : ℝ) (f : V → ℝ) (root : V) :
    gffShift G hG β f root root = 0 := by
  simp only [gffShift]
  ring

/-- The translate satisfies `-Δ σ = f / β` for zero-sum `f`, KP (1.5). -/
theorem neg_laplacian_gffShift (G : Multigraph V E) [Fintype V] [Fintype E]
    [DecidableEq V] (hG : G.Connected) (β : ℝ) (f : V → ℝ)
    (hf : ∑ j, f j = 0) (root : V) :
    G.laplacian (gffShift G hG β f root) = fun j => -f j / β := by
  have hfun : gffShift G hG β f root =
      (-β⁻¹) • G.greenOp hG f + fun _ => G.greenOp hG f root / β := by
    funext j
    simp [gffShift, div_eq_mul_inv]
    ring
  rw [hfun]
  funext j
  change (G.laplacianₗ ℝ
    ((-β⁻¹) • G.greenOp hG f + fun _ => G.greenOp hG f root / β)) j = _
  rw [(G.laplacianₗ ℝ).map_add, (G.laplacianₗ ℝ).map_smul]
  simp only [laplacianₗ_apply, G.laplacian_const,
    G.laplacian_greenOp_of_sum_eq_zero hG f hf, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  simp [div_eq_mul_inv, neg_mul]
  ring

/-- Expansion of the edge energy under addition. -/
theorem energy_add (G : Multigraph V E) [Fintype E] (u w : V → ℝ) :
    G.energy (u + w) = G.energy u + 2 * (∑ e, G.grad u e * G.grad w e) +
      G.energy w := by
  unfold energy
  calc
    (∑ e, G.grad (u + w) e ^ 2) =
        ∑ e, (G.grad u e ^ 2 + 2 * (G.grad u e * G.grad w e) +
          G.grad w e ^ 2) := by
      apply Finset.sum_congr rfl
      intro e he
      simp only [Pi.add_apply, grad]
      ring
    _ = (∑ e, G.grad u e ^ 2) + 2 * (∑ e, G.grad u e * G.grad w e) +
        ∑ e, G.grad w e ^ 2 := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]

/-- The cross term in the energy expansion is the vertex pairing with the
negative Laplacian. -/
theorem sum_grad_mul_eq_neg_pairing_laplacian (G : Multigraph V E)
    [Fintype V] [Fintype E] [DecidableEq V] (u w : V → ℝ) :
    (∑ e, G.grad u e * G.grad w e) = -pairing u (G.laplacian w) := by
  have h := G.pairing_laplacian_eq_neg_sum_grad_mul u w
  linarith

/-- Pairing is additive in its first argument. -/
theorem pairing_add_left (u w f : V → ℝ) [Fintype V] :
    pairing (u + w) f = pairing u f + pairing w f := by
  unfold pairing
  simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]

/-- Pairing commutes with scalar multiplication in its first argument. -/
theorem pairing_smul_left (a : ℝ) (u f : V → ℝ) [Fintype V] :
    pairing (a • u) f = a * pairing u f := by
  unfold pairing
  simp only [Pi.smul_apply, smul_eq_mul]
  calc
    (∑ j, a * u j * f j) = ∑ j, a * (u j * f j) := by
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = a * ∑ j, u j * f j := (Finset.mul_sum _ _ _).symm

/-- Pairing is linear in its second argument. -/
theorem pairing_smul_right (a : ℝ) (u f : V → ℝ) [Fintype V] :
    pairing u (a • f) = a * pairing u f := by
  unfold pairing
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Energy of the pinned translate, expressed by KP's covariance quadratic
form. -/
theorem energy_gffShift (G : Multigraph V E) [Fintype V] [Fintype E]
    [DecidableEq V] (hG : G.Connected) (β : ℝ) (f : V → ℝ)
    (hf : ∑ j, f j = 0) (root : V) :
    G.energy (gffShift G hG β f root) =
      pairing f (-G.greenOp hG f) / β ^ 2 := by
  have hfun : gffShift G hG β f root =
      (-β⁻¹) • G.greenOp hG f + fun _ => G.greenOp hG f root / β := by
    funext j
    simp [gffShift, div_eq_mul_inv]
    ring
  rw [hfun, energy_add]
  have hconst : G.energy (fun _ : V => G.greenOp hG f root / β) = 0 := by
    simp [energy, grad]
  have hcross :
      (∑ e, G.grad ((-β⁻¹) • G.greenOp hG f) e *
          G.grad (fun _ : V => G.greenOp hG f root / β) e) = 0 := by
    simp [grad]
  rw [hconst, hcross]
  simp only [mul_zero, add_zero]
  have hscale : G.energy ((-β⁻¹) • G.greenOp hG f) =
      ((-β⁻¹) ^ 2) * G.energy (G.greenOp hG f) := by
    unfold energy
    calc
      (∑ e, G.grad ((-β⁻¹) • G.greenOp hG f) e ^ 2) =
          ∑ e, ((-β⁻¹) ^ 2 * G.grad (G.greenOp hG f) e ^ 2) := by
        apply Finset.sum_congr rfl
        intro e he
        simp only [grad, Pi.smul_apply, smul_eq_mul]
        ring
      _ = (-β⁻¹) ^ 2 * ∑ e, G.grad (G.greenOp hG f) e ^ 2 :=
        (Finset.mul_sum _ _ _).symm
  rw [hscale]
  rw [G.pairing_eq_energy_greenOp hG f hf]
  ring

/-- The pinned shift pairs with a zero-sum field as the unpinned inverse
solution does. -/
theorem pairing_gffShift_eq (G : Multigraph V E) [Fintype V]
    [Fintype E] [DecidableEq V] (hG : G.Connected) (β : ℝ)
    (f : V → ℝ) (hf : ∑ j, f j = 0) (root : V) :
    pairing (gffShift G hG β f root) f =
      pairing f (-G.greenOp hG f) / β := by
  have hfun : gffShift G hG β f root =
      (-β⁻¹) • G.greenOp hG f + fun _ => G.greenOp hG f root / β := by
    funext j
    simp [gffShift, div_eq_mul_inv]
    ring
  rw [hfun, pairing_add_left, pairing_smul_left,
    pairing_const_left, hf, mul_zero, add_zero]
  have hQ : pairing f (-G.greenOp hG f) =
      -pairing (G.greenOp hG f) f := by
    rw [pairing_neg_right, pairing_comm]
  rw [hQ]
  simp only [div_eq_mul_inv]
  ring

/-- Completing the square at a translated field, with the root window
preserved by the pinned shift, KP (1.4)–(1.5), p. 2. -/
theorem gff_shift_integrand (G : Multigraph V E) [Fintype V] [Fintype E]
    [DecidableEq V] (hG : G.Connected) (β : ℝ) (hβ : 0 < β)
    (f : V → ℝ) (hf : ∑ j, f j = 0) (root : V) (φ : V → ℝ) :
    Real.exp (pairing (φ + gffShift G hG β f root) f) *
        gffDensity G β root (φ + gffShift G hG β f root) =
      Real.exp (pairing f (-G.greenOp hG f) / (2 * β)) *
        gffDensity G β root φ := by
  by_cases hroot : φ root ∈ Set.Ico (-Real.pi) Real.pi
  · have hshiftroot : (φ + gffShift G hG β f root) root = φ root := by
      simp [gffShift_root]
    rw [gffDensity_of_root_mem G β root (φ + gffShift G hG β f root)
        (by simpa [hshiftroot] using hroot),
      gffDensity_of_root_mem G β root φ hroot]
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    rw [pairing_add_left]
    have hΔ := neg_laplacian_gffShift G hG β f hf root
    have hcross := sum_grad_mul_eq_neg_pairing_laplacian G φ
      (gffShift G hG β f root)
    rw [hΔ] at hcross
    have hshiftfun : (fun j => -f j / β) = (-β⁻¹) • f := by
      funext j
      simp [div_eq_mul_inv, neg_mul]
      ring
    have hcross' :
        (∑ e, G.grad φ e * G.grad (gffShift G hG β f root) e) =
          pairing φ f / β := by
      rw [hcross, hshiftfun, pairing_smul_right]
      field_simp
    rw [energy_add, hcross', energy_gffShift G hG β f hf root,
      pairing_gffShift_eq G hG β f hf root]
    field_simp [ne_of_gt hβ]
    ring
  · have hshiftroot : (φ + gffShift G hG β f root) root = φ root := by
      simp [gffShift_root]
    rw [gffDensity_of_root_not_mem G β root φ hroot,
      gffDensity_of_root_not_mem G β root (φ + gffShift G hG β f root)]
    · simp
    · simpa [hshiftroot] using hroot

/-- The translated exponential tilt times the KP density is a fixed multiple
of the original density, in the pointwise form used in KP (1.4). -/
theorem gff_tilted_density_integrable (G : Multigraph V E)
    [Fintype V] [Fintype E] [DecidableEq V] (hG : G.Connected)
    (β : ℝ) (hβ : 0 < β) (f : V → ℝ) (hf : ∑ j, f j = 0)
    (root : V) :
    Integrable (fun φ => Real.exp (pairing φ f) * gffDensity G β root φ)
      (volume : Measure (V → ℝ)) := by
  have hshift : Integrable
      ((fun φ => Real.exp (pairing φ f) * gffDensity G β root φ) ∘
        (fun ψ => ψ + gffShift G hG β f root))
      (volume : Measure (V → ℝ)) := by
    have hbase := integrable_gffDensity G hG β hβ root
    have hmul := hbase.const_mul (Real.exp
      (pairing f (-G.greenOp hG f) / (2 * β)))
    convert hmul using 1
    funext φ
    exact gff_shift_integrand G hG β hβ f hf root φ
  have hback := hshift.comp_add_right (-(gffShift G hG β f root))
  convert hback using 1
  simp

/-- KP (1.4), p. 2: the real zero-sum exponential moment of the normalized
rooted finite-volume GFF. -/
theorem gff_exponential_moment (G : Multigraph V E) [Fintype V]
    [Fintype E] [DecidableEq V] (hG : G.Connected) (β : ℝ) (hβ : 0 < β)
    (f : V → ℝ) (hf : ∑ j, f j = 0) (root : V) :
    Integrable (fun φ => Real.exp (pairing φ f))
      (gffMeasure G hG β hβ root) ∧
    (∫ φ, Real.exp (pairing φ f) ∂gffMeasure G hG β hβ root) =
      Real.exp (pairing f (-G.greenOp hG f) / (2 * β)) := by
  have hnum := gff_tilted_density_integrable G hG β hβ f hf root
  have hchar := gffMeasure_integral_eq_div G hG β hβ root
    (fun φ => Real.exp (pairing φ f)) hnum
  refine ⟨hchar.1, ?_⟩
  rw [hchar.2]
  have hshift := integral_add_right_eq_self
    (μ := (volume : Measure (V → ℝ)))
    (fun φ : V → ℝ => Real.exp (pairing φ f) * gffDensity G β root φ)
    (gffShift G hG β f root)
  rw [← hshift]
  rw [integral_congr_ae (ae_of_all _ fun φ =>
    gff_shift_integrand G hG β hβ f hf root φ)]
  rw [integral_const_mul]
  rw [← gffPartitionFunction_eq_integral]
  field_simp [ne_of_gt (gffPartitionFunction_pos G hG β hβ root)]

end FroehlichSpencer.BKT
