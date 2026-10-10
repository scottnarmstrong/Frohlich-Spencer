/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.XY.SpinRootD
public import FroehlichSpencer.FS82.XY.FanFlowD

/-!
# (4.40) on cubes for every `d ≥ 3`, with the residual bound of the spin residual estimate

`XY/SpinRootD.lean` takes a bound on the residual energy as a hypothesis.

The theorems of this file still take `BranchJensenInterface` (see `XY/SpinRootD.lean`) as a
hypothesis.

It is proved in `XY/SpinTheoremD.lean`, which gives the unconditional root.
-/

open scoped BigOperators

@[expose] public section

namespace FroehlichSpencer.FS82.XY.DualD

open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Gaussian
open FroehlichSpencer.FS82.Wilson

variable {d : ℕ} {B : Box d}

/-- The endpoint path is integer-valued on the dual cells of degree `d − 1`. -/
theorem xyDualDEndpointPathVector_int (x y : XYSites B) (p : DualDForm B (d - 1)) :
    ∃ n : ℤ, xyDualDEndpointPathVector x y p = (n : ℝ) := by
  refine ⟨xyEndpointPath x y (primalDualCellEquiv.symm p.1), ?_⟩
  simp [xyDualDEndpointPathVector, xyDualDStarCompressLinear, starMap, castIntegerChain,
    dualDFormEmbedding, Finsupp.equivMapDomain_apply]

/-- The Hodge potential of the endpoint path: `d₁ τ = φ − ε`. -/
theorem xyDualD_d₁_pathTau (hd : 3 ≤ d) (x y : XYSites B) :
    (dualDExactOneComplex hd B).d₁ (xyDualDEndpointPathTau hd x y).1 =
      xyDualDEndpointPathVector x y -
        loopFieldResidual (dualDExactOneComplex hd B) (xyDualDEndpointPathVector x y) := by
  set C := dualDExactOneComplex hd B with hC
  set φ := xyDualDEndpointPathVector x y with hφ
  set τ := (xyDualDEndpointPathTau hd x y).1 with hτ
  have hval : formLaplacian C τ = C.d₁.adjoint φ :=
    congrArg Subtype.val (hodgeOnCoClosed_hodgeInverse C (xyDualDEndpointPathSourceCoClosed hd x y))
  have horth : ∀ α : EuclideanSpace ℝ (DualDForm B (d - 2)), inner ℝ (φ - C.d₁ τ) (C.d₁ α) = 0 := by
    intro α
    rw [← LinearMap.adjoint_inner_left, map_sub]
    have h2 : C.d₁.adjoint (C.d₁ τ) = formLaplacian C τ := rfl
    rw [h2, hval, sub_self, inner_zero_left]
  have heq := eq_loopFieldResidual C φ (φ - C.d₁ τ) ⟨τ, by abel⟩ horth
  rw [← heq]
  abel

/-- The squared norm of the residual field of the endpoint path is the residual energy of the fan flow. -/
theorem sum_sq_pathResidual (hd : 3 ≤ d) (x y : XYSites B) :
    ∑ p, (loopFieldResidual (dualDExactOneComplex hd B) (xyDualDEndpointPathVector x y) p) ^ 2 =
      xyDualDEndpointResidualEnergy hd x y := by
  unfold xyDualDEndpointResidualEnergy
  rw [PiLp.inner_apply]
  exact Finset.sum_congr rfl fun p _ => by simp [sq]

/-- **FS82 (4.40) on a cube for every `d ≥ 3`, from the interface.** The residual bound is the spin residual estimate's. -/
theorem xyD_cube_spinCorrelation_lower (hd : 3 ≤ d) {β κ b : ℝ} (hβ : 0 < β) (hκ : 0 < κ)
    (ha : (d : ℝ) ≤ κ * β - b) (hCube : ∀ i j : Fin d, B i = B j) (x y : XYSites B)
    (hI : BranchJensenInterface hd β x y (xyDualDEndpointPathVector x y)
      (xyDualDEndpointPathTau hd x y).1 (κ * β - b)) :
    Real.exp (-(rootConstantD d κ b (72 * (d : ℝ) ^ 2) / β)) ≤ xyEndpointCosExpectation β x y := by
  have hd0 : 0 < d := by omega
  have hres : ∑ p, (loopFieldResidual (dualDExactOneComplex hd B)
      (xyDualDEndpointPathVector x y) p) ^ 2 ≤ 72 * (d : ℝ) ^ 2 := by
    rw [sum_sq_pathResidual]
    exact xyDualDEndpointResidualEnergy_le_uniform_cube hd hCube x y
  exact cube_spinCorrelation_root_of_interface hd hβ hκ (by positivity) ha
    (B ⟨0, hd0⟩) (fun k => hCube k ⟨0, hd0⟩) x y (xyDualDEndpointPathVector x y)
    (xyDualDEndpointPathVector_int x y) (xyDualDEndpointPathTau hd x y).1
    (xyDualD_d₁_pathTau hd x y) hI hres

theorem rootConstantD_pos (d : ℕ) {κ b C : ℝ} (hκ : 0 < κ) (hC : 0 < C) :
    0 < rootConstantD d κ b C := by
  unfold rootConstantD
  have hpoly := polyTail_nonneg (3 * d)
  have h2 : 0 ≤ (20 * (10 : ℝ) ^ d * (2 * Real.pi * (4 : ℝ) ^ d) ^ 2 * polyTail (3 * d) *
      Real.exp 1 * C + 5 * Real.pi ^ 2 * (4 : ℝ) ^ d) * Real.exp b / κ := by positivity
  linarith

/-- **The finite-volume root of FS82 Section 4 for every `d ≥ 3`, (4.40), from the interface.**
If the interface holds at the rate `κβ − b` for all `β` with `κβ − b ≥ d`, on every cube and for
all sites, then there are `β₀` and `C` with `exp(−C/β) ≤ ⟨cos(θ_x − θ_y)⟩` for all `β ≥ β₀`, every
cube and all sites `x, y` of it. -/
theorem fs82_xyD_spinCorrelation_root_of_interface (hd : 3 ≤ d) {κ b : ℝ} (hκ : 0 < κ)
    (hI : ∀ β : ℝ, 0 < β → (d : ℝ) ≤ κ * β - b → ∀ B : Box d, (∀ i j : Fin d, B i = B j) →
      ∀ x y : XYSites B, BranchJensenInterface hd β x y (xyDualDEndpointPathVector x y)
        (xyDualDEndpointPathTau hd x y).1 (κ * β - b)) :
    ∃ β₀ C : ℝ, 0 < β₀ ∧ 0 < C ∧ ∀ β : ℝ, β₀ ≤ β → ∀ B : Box d,
      (∀ i j : Fin d, B i = B j) → ∀ x y : XYSites B,
        Real.exp (-(C / β)) ≤ xyEndpointCosExpectation β x y := by
  have hd0 : (0 : ℝ) < (d : ℝ) := by
    have : 0 < d := by omega
    exact_mod_cast this
  refine ⟨max 1 (((d : ℝ) + b) / κ), rootConstantD d κ b (72 * (d : ℝ) ^ 2),
    lt_of_lt_of_le one_pos (le_max_left _ _), rootConstantD_pos d hκ (by positivity), ?_⟩
  intro β hβ B hCube x y
  have hβ0 : 0 < β := lt_of_lt_of_le one_pos ((le_max_left _ _).trans hβ)
  have hrate : (d : ℝ) ≤ κ * β - b := by
    have h := (le_max_right 1 (((d : ℝ) + b) / κ)).trans hβ
    rw [div_le_iff₀ hκ] at h
    linarith
  exact xyD_cube_spinCorrelation_lower hd hβ0 hκ hrate hCube x y (hI β hβ0 hrate B hCube x y)

end FroehlichSpencer.FS82.XY.DualD

end
