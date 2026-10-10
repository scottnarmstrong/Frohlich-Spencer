/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.T12.InductionStep
public import FroehlichSpencer.T12.ScaleChoice
public import FroehlichSpencer.T12.Bridge

/-!
# The joint induction and the finite-volume T2.1

Iterating the step `(J_k, N_k) ⇒ (J_{k+1}, N_{k+1})` under the explicit
`LevelScale` conditions gives all levels; choosing `m_k = massSeq K₀ m_base (13 m_base)` and
`K₀` large gives `M = m_base / 2`.
-/

@[expose] public section

namespace FroehlichSpencer.T12

open Multiscale


theorem jPred_nPred_of_levelScale {ν : ℕ} (P : Params) (hK : ScaleConditions P.K₀)
    (Λ : Finset (Site ν)) (v : Site ν → ℝ) {m τ μ : ℕ → ℝ}
    (hJ0 : JPred P Λ v 0 (m 0)) (hN0 : NPred P Λ v 0 (normBound P.K₀ 0))
    (hs : ∀ k, LevelScale ν P.K₀ k (m k) (τ k) (μ k) (m (k + 1))) (k : ℕ) :
    JPred P Λ v k (m k) ∧ NPred P Λ v k (normBound P.K₀ k) := by
  induction k with
  | zero => exact ⟨hJ0, hN0⟩
  | succ k ih =>
    obtain ⟨hJ, hN⟩ := ih
    obtain ⟨hτ0, hμ0, hμm, hm'0, hd, hsmall, hloc, hτ, hθ, hfin, hcross⟩ := hs k
    have hJ' := jPred_succ P hK Λ v k hJ hN hτ0 hμ0 hμm hd hsmall hloc hτ hθ hfin
    exact ⟨hJ', nPred_succ P hK Λ v k hJ hN hτ0 (by linarith only [hμ0, hμm]) hd hsmall hloc hτ
      hcross hm'0 hJ'⟩


theorem finiteVolumeT21_of_levelScale {ν : ℕ} (P : Params) (hK : ScaleConditions P.K₀)
    (hN : 2 * (ν : ℝ) + 1 ≤ P.Nthr) {m τ μ : ℕ → ℝ} {M : ℝ}
    (hm0 : m 0 ≤ Real.log (P.Nthr / (2 * ν)))
    (hs : ∀ k, LevelScale ν P.K₀ k (m k) (τ k) (μ k) (m (k + 1))) (hM : ∀ k, M ≤ m (k + 1)) :
    FiniteVolumeT21 ν P M := by
  intro Λ v k
  have hJ0 : JPred P Λ v 0 (m 0) := by
    refine jPred_mono ?_ (jPred_zero P hN (le_refl 0) Λ v)
    simpa using hm0
  exact jPred_mono (hM k)
    (jPred_nPred_of_levelScale P hK Λ v hJ0 (nPred_zero P hN Λ v) hs (k + 1)).1


theorem exists_finiteVolumeT21 (ν : ℕ) (hν : 1 ≤ ν) : ∃ K₁ : ℝ, ∀ P : Params, K₁ ≤ P.K₀ →
    2 * ν * Real.exp 1 ≤ P.Nthr → FiniteVolumeT21 ν P (Real.log (P.Nthr / (2 * ν)) / 2) := by
  obtain ⟨Ks, hKs⟩ := exists_levelScale ν
  obtain ⟨K40, hK40⟩ := exists_scaleConditions
  refine ⟨max (max (max 40 K40) Ks) (8 * Real.log 52 + 32 * Real.log 2 + 1), fun P hK hN => ?_⟩
  have hK1 : 40 ≤ P.K₀ := by
    refine le_trans ?_ hK; exact (le_max_left _ _).trans ((le_max_left _ _).trans (le_max_left _ _))
  have hK2 : K40 ≤ P.K₀ := by
    refine le_trans ?_ hK
    exact (le_max_right _ _).trans ((le_max_left _ _).trans (le_max_left _ _))
  have hK3 : Ks ≤ P.K₀ := (le_max_right _ _).trans ((le_max_left _ _).trans hK)
  have hK4 : 8 * Real.log 52 + 32 * Real.log 2 + 1 ≤ P.K₀ := (le_max_right _ _).trans hK
  have hl52 : 0 ≤ Real.log 52 := Real.log_nonneg (by norm_num)
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hν1 : (1 : ℝ) ≤ ν := by exact_mod_cast hν
  have hν0 : (0 : ℝ) < 2 * ν := by linarith only [hν1]
  have he2 : (2 : ℝ) ≤ Real.exp 1 := by linarith only [Real.add_one_le_exp (1 : ℝ)]
  have hN1 : 2 * (ν : ℝ) + 1 ≤ P.Nthr := by nlinarith only [hN, hν1, he2]
  have hmb : 1 ≤ Real.log (P.Nthr / (2 * ν)) := by
    rw [Real.le_log_iff_exp_le (div_pos (by linarith only [hN1]) hν0), le_div_iff₀ hν0]
    linarith only [hN]
  set mb := Real.log (P.Nthr / (2 * ν)) with hmbdef
  have hSC := hK40 P.K₀ hK2
  have h0 : massSeq P.K₀ mb (13 * mb) 0 = mb := by simp [massSeq]
  have hd0 : scaleD P.K₀ 0 ^ (-(1 / 8 : ℝ)) ≤ 1 / 52 := by
    have : scaleD P.K₀ 0 ^ (-(1 / 8 : ℝ)) = Real.exp (-(P.K₀ / 8)) := by
      unfold scaleD
      rw [← Real.exp_mul]; congr 1; ring
    rw [this]
    calc Real.exp (-(P.K₀ / 8)) ≤ Real.exp (-Real.log 52) :=
          Real.exp_le_exp.2 (by linarith only [hK4, hl2])
      _ = 1 / 52 := by rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
  have hsmall : 2 * (13 * mb) * scaleD P.K₀ 0 ^ (-(1 / 8 : ℝ)) ≤ mb / 2 := by
    nlinarith only [hmb, hd0]
  refine finiteVolumeT21_of_levelScale P hSC hN1 (m := massSeq P.K₀ mb (13 * mb)) (M := mb / 2)
    (τ := locLoss P.K₀ mb)
    (μ := fun k => iterRate ν P.K₀ (massSeq P.K₀ mb (13 * mb) k) (locLoss P.K₀ mb k) k)
    (by rw [h0]) (fun k => hKs P.K₀ hK3 mb hmb k) fun k => ?_
  exact half_le_massSeq (by linarith only [hK4, hl52]) (by linarith only [hmb]) hsmall (k + 1)


theorem exists_finiteVolumeT21_rate (ν : ℕ) (hν : 1 ≤ ν) : ∃ K₁ : ℝ, ∀ (M : ℝ) (P : Params),
    K₁ ≤ P.K₀ → 2 * ν * Real.exp (max 1 (2 * M)) ≤ P.Nthr → FiniteVolumeT21 ν P M := by
  obtain ⟨K₁, hK₁⟩ := exists_finiteVolumeT21 ν hν
  refine ⟨K₁, fun M P hK hN => ?_⟩
  have hν1 : (1 : ℝ) ≤ ν := by exact_mod_cast hν
  have hν0 : (0 : ℝ) < 2 * ν := by linarith only [hν1]
  have h1 : 2 * (ν : ℝ) * Real.exp 1 ≤ P.Nthr :=
    le_trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (le_max_left _ _)) hν0.le) hN
  have h2 : 2 * M ≤ Real.log (P.Nthr / (2 * ν)) := by
    have hpos : 0 < P.Nthr / (2 * ν) := div_pos (by
      have := Real.exp_pos 1
      nlinarith only [hν0, h1, this]) hν0
    rw [Real.le_log_iff_exp_le hpos, le_div_iff₀ hν0]
    have h3 : 2 * ν * Real.exp (2 * M) ≤ P.Nthr :=
      le_trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (le_max_right _ _)) hν0.le) hN
    linarith only [h3, mul_comm (2 * (ν : ℝ)) (Real.exp (2 * M))]
  intro Λ v k
  exact jPred_mono (by linarith only [h2]) (hK₁ P hK h1 Λ v k)

end FroehlichSpencer.T12

end
