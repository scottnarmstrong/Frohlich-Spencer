/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.T12.Tower
public import FroehlichSpencer.T12.FiniteVolumeT21

/-!
# Unconditional simultaneous Green bounds on the tower event
-/

@[expose] public section

namespace FroehlichSpencer.T12

open Multiscale

private theorem pos_of_sc {K₀ : ℝ} (hK : ScaleConditions K₀) : 0 < K₀ := by
  have h := hK.1
  unfold scaleD at h
  by_contra hn
  push Not at hn
  have : Real.exp (K₀ * (5 / 4 : ℝ) ^ 0) ≤ 1 := by
    rw [Real.exp_le_one_iff]; simpa using hn
  linarith


theorem exists_norm_finiteGreen_towerRegion_le_of_regime (ν : ℕ) (hν : 1 ≤ ν) :
    ∃ K₁ L₀ : ℝ, ∀ (M : ℝ) (P : Params), K₁ ≤ P.K₀ →
      2 * ν * Real.exp (max 1 (2 * M)) ≤ P.Nthr →
      ∀ (Λ : Finset (Site ν)) (v : Configuration ν) (a : Site ν) (L : ℝ), L₀ ≤ L →
        scaleD P.K₀ 1 / 5 ≤ L ^ (3 / 4 : ℝ) → v ∈ towerEvent P Λ a L →
        ∀ (j : ℕ) (hfin : (towerRegion P Λ v a L j).Finite) (ε : ℝ) (hε : ε ≠ 0)
          (x y : {x // x ∈ hfin.toFinset ∩ Λ}), (4 ^ j * L) ^ (3 / 4 : ℝ) ≤ siteDist ν x y →
          ‖finiteGreen ν (hfin.toFinset ∩ Λ) v P.E ε hε x y‖ ≤
            Real.exp (-M * siteDist ν x y) := by
  obtain ⟨K_T, hKT⟩ := exists_finiteVolumeT21_rate ν hν
  obtain ⟨K_S, hKS⟩ := exists_scaleConditions
  obtain ⟨L₀, hL₀⟩ := exists_norm_finiteGreen_towerRegion_le ν
  refine ⟨max K_T K_S, max L₀ 1, fun M P hK hN Λ v a L hL h1 hv j hfin ε hε x y hxy => ?_⟩
  have hSC := hKS P.K₀ ((le_max_right _ _).trans hK)
  have hKp := pos_of_sc hSC
  have hL1 : 1 ≤ L := (le_max_right _ _).trans hL
  have hLl : L ^ (3 / 4 : ℝ) ≤ (4 ^ j * L) ^ (3 / 4 : ℝ) :=
    Real.rpow_le_rpow (by linarith) (le_mul_of_one_le_left (by linarith)
      (one_le_pow₀ (by norm_num))) (by norm_num)
  have hk1 := one_le_towerLevel hKp (h1.trans hLl)
  have hJ : JPred P Λ v (towerLevel P.K₀ (4 ^ j * L)) M := by
    have := hKT M P ((le_max_left _ _).trans hK) hN Λ v (towerLevel P.K₀ (4 ^ j * L) - 1)
    rwa [Nat.sub_add_cancel hk1] at this
  exact hL₀ P hSC Λ v a L ((le_max_left _ _).trans hL) h1 hv M j hJ hfin ε hε x y hxy

end FroehlichSpencer.T12

end
