/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.Infra.Spectral.QuadForm
public import FroehlichSpencer.Infra.Spectral.Regularity
public import FroehlichSpencer.Infra.Resolvent

/-!
# Finite-volume restrictions of a kernel plus a potential

Generic setting for infinite-volume Green functions: an index type `X`, a kernel
`a : X → X → ℂ` (the "hopping" part) and a real potential `v : X → ℝ`.

For a finite set
`Λ : Finset X`, `restrictedOp a v Λ` is the matrix `a|_Λ + diagonal v|_Λ` on the subtype `Λ`, and
`resolventColumn a v Λ z y` is the column `y` of `(restrictedOp a v Λ - z • 1)⁻¹`, extended by
zero outside `Λ`.

Motivation: the finite-volume Hamiltonians `H_Λ` and Green functions `G_Λ` of
Fröhlich–Spencer (1983), (1.9), (1.28)–(1.29), Fröhlich–Spencer (1983); no lattice or
Laplacian is defined here.
-/

@[expose] public section

open Matrix
open scoped Matrix.Norms.L2Operator

namespace FroehlichSpencer.Infra

variable {X : Type*} [DecidableEq X]

/-- The matrix `a|_Λ + diagonal v|_Λ` on the finite set `Λ`. -/
noncomputable def restrictedOp (a : X → X → ℂ) (v : X → ℝ) (Λ : Finset X) : Matrix Λ Λ ℂ :=
  Matrix.of (fun x y : Λ => a x y) + Matrix.diagonal (fun x : Λ => (v x : ℂ))

/-- Column `y` of the finite-volume resolvent `(restrictedOp a v Λ - z • 1)⁻¹`, extended by zero
outside `Λ` (and identically zero if `y ∉ Λ`). -/
noncomputable def resolventColumn (a : X → X → ℂ) (v : X → ℝ) (Λ : Finset X) (z : ℂ) (y : X) :
    X → ℂ :=
  fun x => if h : x ∈ Λ ∧ y ∈ Λ then
    ((restrictedOp a v Λ - z • (1 : Matrix Λ Λ ℂ))⁻¹) ⟨x, h.1⟩ ⟨y, h.2⟩ else 0

theorem restrictedOp_apply (a : X → X → ℂ) (v : X → ℝ) (Λ : Finset X) (x y : Λ) :
    restrictedOp a v Λ x y = a x y + if x = y then (v x : ℂ) else 0 := by
  simp [restrictedOp, Matrix.diagonal_apply]

theorem isHermitian_restrictedOp {a : X → X → ℂ} (ha : ∀ x y, a y x = star (a x y))
    (v : X → ℝ) (Λ : Finset X) : (restrictedOp a v Λ).IsHermitian := by
  refine isHermitian_add_diagonal (Matrix.IsHermitian.ext fun x y => ?_) (fun x : Λ => v x)
  simp only [Matrix.of_apply]
  rw [ha x y, star_star]

theorem resolventColumn_of_mem (a : X → X → ℂ) (v : X → ℝ) {Λ : Finset X} (z : ℂ) {x y : X}
    (hx : x ∈ Λ) (hy : y ∈ Λ) :
    resolventColumn a v Λ z y x =
      ((restrictedOp a v Λ - z • (1 : Matrix Λ Λ ℂ))⁻¹) ⟨x, hx⟩ ⟨y, hy⟩ := by
  simp [resolventColumn, hx, hy]

theorem resolventColumn_of_notMem_left (a : X → X → ℂ) (v : X → ℝ) {Λ : Finset X} (z : ℂ)
    {x : X} (y : X) (hx : x ∉ Λ) : resolventColumn a v Λ z y x = 0 := by
  simp [resolventColumn, hx]

theorem resolventColumn_of_notMem_right (a : X → X → ℂ) (v : X → ℝ) {Λ : Finset X} (z : ℂ)
    (x : X) {y : X} (hy : y ∉ Λ) : resolventColumn a v Λ z y x = 0 := by
  simp [resolventColumn, hy]

/-- The finite-dimensional resolvent bound in vector form:
`‖(H - z • 1)⁻¹ u‖² ≤ ‖u‖² / (Im z)²` for Hermitian `H` (from the operator-norm bound). -/
theorem re_star_dotProduct_inv_mulVec_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : Matrix ι ι ℂ} (hH : H.IsHermitian) {z : ℂ} (hz : z.im ≠ 0) (u : ι → ℂ) :
    (star ((H - z • (1 : Matrix ι ι ℂ))⁻¹ *ᵥ u) ⬝ᵥ ((H - z • (1 : Matrix ι ι ℂ))⁻¹ *ᵥ u)).re ≤
      (star u ⬝ᵥ u).re / z.im ^ 2 := by
  set R := (H - z • (1 : Matrix ι ι ℂ))⁻¹
  have hR : ‖R‖ ≤ 1 / |z.im| :=
    FroehlichSpencer.Matrix.IsHermitian.norm_ringInverse_sub_zsmul_one_le H hH z hz
  have h1 := Matrix.l2_opNorm_mulVec R (WithLp.toLp 2 u)
  have h2 : ‖WithLp.toLp 2 (R *ᵥ u)‖ ≤ ‖WithLp.toLp 2 u‖ / |z.im| := by
    calc ‖WithLp.toLp 2 (R *ᵥ u)‖ ≤ ‖R‖ * ‖WithLp.toLp 2 u‖ := by simpa using h1
      _ ≤ 1 / |z.im| * ‖WithLp.toLp 2 u‖ := by gcongr
      _ = ‖WithLp.toLp 2 u‖ / |z.im| := by ring
  have hpos : 0 < |z.im| := abs_pos.mpr hz
  rw [← norm_toLp_sq, ← norm_toLp_sq, ← sq_abs z.im, ← div_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) h2 2

end FroehlichSpencer.Infra
