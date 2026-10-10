/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.T12.Bridge
public import FroehlichSpencer.T12.InductionDefs

/-!
# The scale conditions of the joint induction hold for large `K₀`

All conditions are reduced to
one-variable inequalities in `L = log d_k = K₀ (5/4)^k`, valid for all large `L`.
-/

@[expose] public section

namespace FroehlichSpencer.T12

open Multiscale Filter

/-! ### Elementary asymptotics -/

private theorem ev_lin {A B ε c : ℝ} (hA : 0 ≤ A) (hε : 0 < ε) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop, A + B * L ≤ ε * Real.exp (c * L) := by
  refine eventually_atTop.2 ⟨max 1 (2 * (A + B) / (ε * c ^ 2)), fun L hL => ?_⟩
  have h1 : 1 ≤ L := (le_max_left _ _).trans hL
  have h2 : 2 * (A + B) / (ε * c ^ 2) ≤ L := (le_max_right _ _).trans hL
  have h3 : 2 * (A + B) ≤ L * (ε * c ^ 2) := by
    rwa [div_le_iff₀ (by positivity)] at h2
  have h4 : (c * L) ^ 2 / 2 ≤ Real.exp (c * L) := by
    have := Real.quadratic_le_exp_of_nonneg (x := c * L) (by positivity)
    have h5 : 0 ≤ c * L := by positivity
    linarith only [this, h5]
  have h6 : A + B * L ≤ (A + B) * L := by nlinarith only [hA, h1]
  have h7 : (A + B) * L ≤ ε * ((c * L) ^ 2 / 2) := by
    have : 0 ≤ L := by linarith only [h1]
    calc (A + B) * L = (2 * (A + B)) * L / 2 := by ring
      _ ≤ (L * (ε * c ^ 2)) * L / 2 := by gcongr
      _ = ε * ((c * L) ^ 2 / 2) := by ring
  calc A + B * L ≤ ε * ((c * L) ^ 2 / 2) := h6.trans h7
    _ ≤ ε * Real.exp (c * L) := by gcongr

private theorem ev_exp {a c ε : ℝ} (hε : 0 < ε) (hac : a < c) :
    ∀ᶠ L : ℝ in atTop, Real.exp (a * L) ≤ ε * Real.exp (c * L) := by
  refine eventually_atTop.2 ⟨1 / (ε * (c - a)), fun L hL => ?_⟩
  have hpos : 0 < ε * (c - a) := mul_pos hε (by linarith only [hac])
  have h1 : 1 ≤ ε * (c - a) * L := by
    rw [div_le_iff₀ hpos] at hL
    linarith only [hL]
  have h2 : 1 + (c - a) * L ≤ Real.exp ((c - a) * L) := by
    have := Real.add_one_le_exp ((c - a) * L)
    linarith only [this]
  have hL0 : 0 ≤ L := by
    by_contra h
    have h' := not_le.1 h
    nlinarith only [hpos, h1, h']
  have h3 : 1 / ε ≤ Real.exp ((c - a) * L) := by
    rw [div_le_iff₀ hε]
    nlinarith only [hac, hpos, h1, h2]
  have h4 : Real.exp (c * L) = Real.exp (a * L) * Real.exp ((c - a) * L) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [h4]
  have h5 := Real.exp_pos (a * L)
  have h6 : 1 ≤ ε * Real.exp ((c - a) * L) := by
    rw [div_le_iff₀ hε] at h3
    linarith only [h3]
  nlinarith only [h5, h6]

/-! ### Rewriting the scales in terms of `L = log d_k` -/

private theorem scaleD_eq (K₀ : ℝ) (k : ℕ) : scaleD K₀ k = Real.exp (K₀ * (5 / 4 : ℝ) ^ k) := rfl

private theorem scaleD_succ_eq (K₀ : ℝ) (k : ℕ) :
    scaleD K₀ (k + 1) = Real.exp (5 / 4 * (K₀ * (5 / 4 : ℝ) ^ k)) := by
  rw [scaleD_eq]; congr 1; ring

private theorem sqrt_exp_eq (L : ℝ) : Real.sqrt (Real.exp L) = Real.exp (L / 2) := by
  rw [Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity), ← Real.exp_add]
  congr 1; ring

/-- The `N_k` bound is at least one and at most `exp (8 exp (2 L / 5))`. -/
private theorem normBound_bounds {K₀ : ℝ} (k : ℕ) {L : ℝ} (hL : K₀ * (5 / 4 : ℝ) ^ k = L) :
    1 ≤ normBound K₀ k ∧ normBound K₀ k ≤ Real.exp (8 * Real.exp (2 * L / 5)) := by
  unfold normBound
  split_ifs with h
  · exact ⟨le_rfl, Real.one_le_exp (by positivity)⟩
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [Nat.add_sub_cancel, scaleD_eq, sqrt_exp_eq]
    refine ⟨Real.one_le_exp (by positivity), Real.exp_le_exp.2 ?_⟩
    have : K₀ * (5 / 4 : ℝ) ^ j / 2 = 2 * L / 5 := by
      rw [← hL, pow_succ]; ring
    rw [this]

/-! ### Entropy and norm bookkeeping -/

private theorem entropy_bounds (ν : ℕ) {D : ℝ} (hD : 1 ≤ D) :
    0 ≤ Real.log (2 * (2 * ν * (8 * D) ^ ν)) ∧
    Real.log (2 * (2 * ν * (8 * D) ^ ν)) ≤ 4 * ν * 8 ^ ν + ν * Real.log D ∧
    2 * ν * (8 * D) ^ ν ≤ Real.exp (Real.log (2 * (2 * ν * (8 * D) ^ ν))) ∧
    2 * ν * (8 * D) ^ ν * Real.exp (-Real.log (2 * (2 * ν * (8 * D) ^ ν))) ≤ 1 / 2 := by
  rcases Nat.eq_zero_or_pos ν with rfl | hν
  · simp
  have hν1 : (1 : ℝ) ≤ ν := by exact_mod_cast hν
  have hD0 : 0 < D := by linarith only [hD]
  have h8 : (1 : ℝ) ≤ (8 * D) ^ ν := one_le_pow₀ (by linarith only [hD])
  set P : ℝ := 2 * ν * (8 * D) ^ ν with hP
  have hP2 : 2 ≤ P := by rw [hP]; nlinarith only [hν1, h8]
  have hP0 : 0 < P := by linarith only [hP2]
  have h2P : 2 * P = (4 * ν * 8 ^ ν) * D ^ ν := by rw [hP, mul_pow]; ring
  have hDν : 1 ≤ D ^ ν := one_le_pow₀ hD
  refine ⟨Real.log_nonneg (by linarith only [hP2]), ?_, ?_, ?_⟩
  · rw [h2P, Real.log_mul (by positivity) (by positivity), Real.log_pow]
    have := Real.log_le_sub_one_of_pos (show 0 < 4 * (ν : ℝ) * 8 ^ ν by positivity)
    linarith only [this]
  · rw [Real.exp_log (by linarith only [hP0])]; linarith only [hP0]
  · rw [Real.exp_neg, Real.exp_log (by linarith only [hP0])]
    field_simp
    linarith only []

private theorem norm_bounds (ν : ℕ) (L : ℝ) :
    0 ≤ 2 * ν * (25 * Real.exp L) ^ ν ∧
    2 * ν * (25 * Real.exp L) ^ ν ≤ Real.exp (2 * ν * 25 ^ ν + ν * L) := by
  have h1 : (25 * Real.exp L) ^ ν = 25 ^ ν * Real.exp (ν * L) := by
    rw [mul_pow, ← Real.exp_nat_mul]
  rw [h1, Real.exp_add]
  refine ⟨by positivity, ?_⟩
  have := Real.add_one_le_exp (2 * (ν : ℝ) * 25 ^ ν)
  calc 2 * (ν : ℝ) * (25 ^ ν * Real.exp (ν * L))
      = (2 * (ν : ℝ) * 25 ^ ν) * Real.exp (ν * L) := by ring
    _ ≤ Real.exp (2 * ν * 25 ^ ν) * Real.exp (ν * L) := by gcongr; linarith only [this]

/-! ### The one-variable inequalities -/

/-- The finitely many one-variable inequalities in `L = log d_k` used below. -/
private def ScaleBounds (ν : ℕ) (L : ℝ) : Prop :=
  7000 ≤ L ∧
  4 * ν * 8 ^ ν + 5 * ν / 4 * L ≤ 1 / 8 * Real.exp (5 / 4 * L) ∧
  2 * (2 * ν * 25 ^ ν) + 2 * ν * L + Real.exp (1 / 2 * L) + 1 ≤ Real.exp L / 2 ∧
  2 * (2 * ν * 25 ^ ν) + 2 * ν * L + 16 * Real.exp (2 * L / 5) + 2 ≤ 3 * Real.exp (1 / 2 * L) ∧
  2 * (2 * ν * 25 ^ ν) + 2 * ν * L + 16 * Real.exp (2 * L / 5) + Real.exp (1 / 2 * L) + 4 ≤
    3 / 5 * Real.exp L ∧
  3 / 2 + 4 * Real.exp (1 / 2 * L) + 2 / 5 * (4 * ν * 8 ^ ν + 5 * ν / 4 * L) ≤
    Real.exp (9 / 8 * L)

private theorem eventually_scaleBounds (ν : ℕ) : ∀ᶠ L : ℝ in atTop, ScaleBounds ν L := by
  have hν : (0 : ℝ) ≤ ν := Nat.cast_nonneg ν
  have hc : (0 : ℝ) ≤ 2 * ν * 25 ^ ν := by positivity
  have ha : (0 : ℝ) ≤ 4 * ν * 8 ^ ν := by positivity
  have e1 := ev_lin (A := 4 * ν * 8 ^ ν) (B := 5 * ν / 4) (ε := 1 / 8) (c := 5 / 4) ha
    (by norm_num) (by norm_num)
  have e2 := ev_lin (A := 2 * (2 * ν * 25 ^ ν) + 1) (B := 2 * ν) (ε := 1 / 4) (c := 1)
    (by positivity) (by norm_num) (by norm_num)
  have e2' := ev_exp (a := 1 / 2) (c := 1) (ε := 1 / 4) (by norm_num) (by norm_num)
  have e3 := ev_lin (A := 2 * (2 * ν * 25 ^ ν) + 2) (B := 2 * ν) (ε := 1) (c := 1 / 2)
    (by positivity) (by norm_num) (by norm_num)
  have e3' := ev_exp (a := 2 / 5) (c := 1 / 2) (ε := 1 / 16) (by norm_num) (by norm_num)
  have e4 := ev_lin (A := 2 * (2 * ν * 25 ^ ν) + 4) (B := 2 * ν) (ε := 1 / 5) (c := 1)
    (by positivity) (by norm_num) (by norm_num)
  have e4' := ev_exp (a := 2 / 5) (c := 1) (ε := 1 / 80) (by norm_num) (by norm_num)
  have e4'' := ev_exp (a := 1 / 2) (c := 1) (ε := 1 / 5) (by norm_num) (by norm_num)
  have e5 := ev_lin (A := 3 / 2 + 2 / 5 * (4 * ν * 8 ^ ν)) (B := 2 / 5 * (5 * ν / 4))
    (ε := 1 / 2) (c := 9 / 8) (by positivity) (by norm_num) (by norm_num)
  have e5' := ev_exp (a := 1 / 2) (c := 9 / 8) (ε := 1 / 8) (by norm_num) (by norm_num)
  have e0 : ∀ᶠ L : ℝ in atTop, (7000 : ℝ) ≤ L := eventually_ge_atTop _
  filter_upwards [e0, e1, e2, e2', e3, e3', e4, e4', e4'', e5, e5'] with L h0 h1 h2 h2' h3 h3'
    h4 h4' h4'' h5 h5'
  have hr : Real.exp (2 * L / 5) = Real.exp (2 / 5 * L) := by congr 1; ring
  simp only [one_mul] at h2 h2' h4 h4' h4''
  have hp := Real.exp_pos (1 / 2 * L)
  unfold ScaleBounds
  rw [hr]
  refine ⟨h0, h1, ?_, ?_, ?_, ?_⟩ <;> linarith only [h4, h4'', hp, h3, h3', h4', h5, h5']

private theorem exp_le_half {w : ℝ} (h : w ≤ -1) : Real.exp w ≤ 1 / 2 := by
  have h1 : Real.exp w ≤ Real.exp (-1) := Real.exp_le_exp.2 h
  have h2 := Real.add_one_le_exp (1 : ℝ)
  have h3 : Real.exp (-1) = (Real.exp 1)⁻¹ := Real.exp_neg 1
  have h4 : (Real.exp 1)⁻¹ ≤ 1 / 2 := by
    rw [inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
    norm_num
    linarith only [h2]
  linarith only [h1, h3, h4]

private theorem nx_bound {N X n u : ℝ} (hN0 : 0 ≤ N) (hN : N ≤ Real.exp n) (hX0 : 0 ≤ X)
    (hX : X ≤ Real.exp u) : N ^ 2 * X ^ 2 ≤ Real.exp (2 * n + 2 * u) := by
  have h1 : N ^ 2 ≤ Real.exp (2 * n) := by
    calc N ^ 2 ≤ (Real.exp n) ^ 2 := pow_le_pow_left₀ hN0 hN 2
      _ = Real.exp (2 * n) := by rw [← Real.exp_nat_mul]; norm_num
  have h2 : X ^ 2 ≤ Real.exp (2 * u) := by
    calc X ^ 2 ≤ (Real.exp u) ^ 2 := pow_le_pow_left₀ hX0 hX 2
      _ = Real.exp (2 * u) := by rw [← Real.exp_nat_mul]; norm_num
  rw [Real.exp_add]
  exact mul_le_mul h1 h2 (by positivity) (by positivity)

private theorem levelScale_core (ν : ℕ) {K₀ : ℝ} (k : ℕ) {L mb m m' : ℝ}
    (hL : K₀ * (5 / 4 : ℝ) ^ k = L) (hmb : 1 ≤ mb) (hm1 : mb / 2 ≤ m) (hm2 : m ≤ mb)
    (hm'0 : 0 ≤ m') (hm' : m' = m - 13 * mb * Real.exp (-(L / 8))) (hS : ScaleBounds ν L) :
    LevelScale ν K₀ k m (locLoss K₀ mb k) (iterRate ν K₀ m (locLoss K₀ mb k) k) m' := by
  obtain ⟨S0, S1, S2, S3, S4, S5⟩ := hS
  have hd : scaleD K₀ k = Real.exp L := by rw [← hL]; rfl
  have hD : scaleD K₀ (k + 1) = Real.exp (5 / 4 * L) := by rw [← hL, scaleD_succ_eq]
  have hT : Real.exp L ^ (9 / 8 : ℝ) = Real.exp (9 / 8 * L) := by
    rw [← Real.exp_mul]; congr 1; ring
  have hτ : locLoss K₀ mb k = 3 * mb * Real.exp (-(L / 8)) := by
    unfold locLoss; rw [hd, ← Real.exp_mul]; congr 2; ring
  obtain ⟨hX1, hX2⟩ := normBound_bounds k hL
  have hs12 : Real.exp (1 / 2 * L) = Real.exp (L / 2) := by congr 1; ring
  rw [hs12] at S2 S3 S4 S5
  have hL0 : 0 ≤ L := by linarith only [S0]
  have hET : Real.exp (-(L / 8)) * Real.exp (9 / 8 * L) = Real.exp L := by
    rw [← Real.exp_add]; congr 1; ring
  have hED : Real.exp (-(L / 8)) * Real.exp (5 / 4 * L) = Real.exp (9 / 8 * L) := by
    rw [← Real.exp_add]; congr 1; ring
  have hE12 : Real.exp (-(L / 8)) ≤ 1 / 12 := by
    have h := Real.add_one_le_exp (L / 8)
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
    norm_num
    linarith only [S0, h]
  have hE0 := Real.exp_pos (-(L / 8))
  have hdL : L + 1 ≤ Real.exp L := Real.add_one_le_exp L
  have hD1 : 1 ≤ Real.exp (5 / 4 * L) := Real.one_le_exp (by positivity)
  have hs0 := Real.exp_pos (L / 2)
  have hT0 := Real.exp_pos (9 / 8 * L)
  have hlogD : Real.log (Real.exp (5 / 4 * L)) = 5 / 4 * L := Real.log_exp _
  obtain ⟨hN0, hNb⟩ := norm_bounds ν L
  obtain ⟨Λ0, Λ1, Λ2, Λ3⟩ := entropy_bounds ν hD1
  have hu0 : 0 ≤ 8 * Real.exp (2 * L / 5) := by positivity
  have hcc : (0 : ℝ) ≤ 2 * ν * 25 ^ ν := by positivity
  have hνL : (0 : ℝ) ≤ ν * L := by positivity
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith only [this]
  have hexp1 : (2 : ℝ) ≤ Real.exp 1 := by linarith only [Real.add_one_le_exp (1 : ℝ)]
  rw [hlogD] at Λ1
  unfold LevelScale iterRate
  simp only [hτ, hd, hD, sqrt_exp_eq, hT]
  set E := Real.exp (-(L / 8)) with hE
  set D := Real.exp (5 / 4 * L) with hDdef
  set s := Real.exp (L / 2) with hs
  set T := Real.exp (9 / 8 * L) with hTdef
  set d := Real.exp L with hdd
  set X := normBound K₀ k with hXdef
  set N := 2 * (ν : ℝ) * (25 * d) ^ ν with hN
  set Λ := Real.log (2 * (2 * (ν : ℝ) * (8 * D) ^ ν)) with hΛ
  have hτ0 : 0 ≤ 3 * mb * E := by positivity
  have hτ1 : 3 * mb * E ≤ mb / 4 := by
    have := mul_le_mul_of_nonneg_left hE12 (show 0 ≤ 3 * mb by linarith only [hm2, hm'0, hm', hτ0])
    linarith only [this]
  set A := m - 3 * mb * E with hA
  have hAlo : mb / 4 ≤ A := by linarith only [hm1, hτ1]
  have hAhi : A ≤ mb := by linarith only [hm2, hτ0]
  have hΛD : Λ ≤ D / 8 := by linarith only [S1, Λ1]
  have hden : 0 < D / 2 + 1 := by positivity
  set μ := (A * (D / 2) - Λ) / (D / 2 + 1) with hμdef
  have hμ : μ * (D / 2 + 1) = A * (D / 2) - Λ := by
    rw [hμdef]; field_simp
  have hAD : D / 8 ≤ A * (D / 2) := by
    have := mul_le_mul_of_nonneg_right (show 1 / 4 ≤ A by linarith only [hmb, hAlo])
      (show 0 ≤ D / 2 by positivity)
    linarith only [this]
  have hμ0 : 0 ≤ μ := div_nonneg (by linarith only [hΛD, hAD]) hden.le
  have hμA : μ ≤ A := by
    rw [hμdef, div_le_iff₀ hden]; linarith only [Λ0, hAlo, hAhi]
  refine ⟨hτ0, hμ0, hμA, hm'0, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num; linarith only [S0, hdL]
  · have h1 : N ^ 2 ≤ Real.exp (2 * (2 * ν * 25 ^ ν + ν * L)) := by
      calc N ^ 2 ≤ (Real.exp (2 * ν * 25 ^ ν + ν * L)) ^ 2 := pow_le_pow_left₀ hN0 hNb 2
        _ = _ := by rw [← Real.exp_nat_mul]; norm_num
    have hmd : d / 2 ≤ m * d := by
      have := mul_le_mul_of_nonneg_right (show 1 / 2 ≤ m by linarith only [hmb, hm1])
        (Real.exp_pos L).le
      linarith only [this]
    calc N ^ 2 * Real.exp (s - m * d)
        ≤ Real.exp (2 * (2 * ν * 25 ^ ν + ν * L)) * Real.exp (s - m * d) := by gcongr
      _ = Real.exp (2 * (2 * ν * 25 ^ ν + ν * L) + (s - m * d)) := (Real.exp_add _ _).symm
      _ ≤ 1 / 2 := exp_le_half (by linarith only [S2, hmd])
  · have hnx := nx_bound hN0 hNb (by linarith only [hX1]) hX2
    have h2 : N ^ 2 * X ^ 2 * (2 * Real.exp s) ≤
        Real.exp (2 * (2 * ν * 25 ^ ν + ν * L) + 2 * (8 * Real.exp (2 * L / 5)) + (1 + s)) := by
      have h2' : 2 * Real.exp s ≤ Real.exp (1 + s) := by
        rw [Real.exp_add]; exact mul_le_mul_of_nonneg_right hexp1 (Real.exp_pos s).le
      exact (mul_le_mul hnx h2' (by positivity) (by positivity)).trans_eq
        (Real.exp_add _ _).symm
    have h3 : X ≤ Real.exp (2 * (2 * ν * 25 ^ ν + ν * L) + 2 * (8 * Real.exp (2 * L / 5)) +
        (1 + s)) := hX2.trans (Real.exp_le_exp.2 (by linarith only [hu0, hcc, hνL, hs0]))
    calc X + N ^ 2 * X ^ 2 * (2 * Real.exp s)
        ≤ 2 * Real.exp (2 * (2 * ν * 25 ^ ν + ν * L) + 2 * (8 * Real.exp (2 * L / 5)) +
            (1 + s)) := by linarith only [h2, h3]
      _ ≤ Real.exp 1 * Real.exp (2 * (2 * ν * 25 ^ ν + ν * L) + 2 * (8 * Real.exp (2 * L / 5)) +
            (1 + s)) := by gcongr
      _ = Real.exp (1 + (2 * (2 * ν * 25 ^ ν + ν * L) + 2 * (8 * Real.exp (2 * L / 5)) +
            (1 + s))) := (Real.exp_add _ _).symm
      _ ≤ Real.exp (4 * s) := Real.exp_le_exp.2 (by linarith only [S3])
  · have haa : (0 : ℝ) ≤ 4 * ν * 8 ^ ν := by positivity
    have hbb : (0 : ℝ) ≤ 5 * (ν : ℝ) / 4 * L := by positivity
    have hm0 : 0 ≤ m := by linarith only [hτ0, hμ0, hμA]
    have hnx := nx_bound hN0 hNb (by linarith only [hX1]) hX2
    have h2nx : 2 * (N ^ 2 * X ^ 2) ≤
        Real.exp (1 + (2 * (2 * ν * 25 ^ ν + ν * L) + 2 * (8 * Real.exp (2 * L / 5)))) := by
      rw [Real.exp_add]
      exact mul_le_mul hexp1 hnx (by positivity) (Real.exp_pos _).le
    have hP : 2 * N ^ 2 * X ^ 2 * Real.exp (s + m * (2 * d + 2 + 2 * d / 5)) ≤
        Real.exp (1 + (2 * (2 * ν * 25 ^ ν + ν * L) + 2 * (8 * Real.exp (2 * L / 5))) +
          (s + m * (2 * d + 2 + 2 * d / 5))) := by
      rw [Real.exp_add (1 + _) (s + _)]
      calc 2 * N ^ 2 * X ^ 2 * Real.exp (s + m * (2 * d + 2 + 2 * d / 5))
          = (2 * (N ^ 2 * X ^ 2)) * Real.exp (s + m * (2 * d + 2 + 2 * d / 5)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right h2nx (Real.exp_pos _).le
    have hmx : 0 ≤ m * (2 * d + 2 + 2 * d / 5) := mul_nonneg hm0 (by positivity)
    have hmx2 : m * (2 * d + 2 + 2 * d / 5) ≤ mb * (2 * d + 2 + 2 * d / 5) :=
      mul_le_mul_of_nonneg_right hm2 (by positivity)
    have hd3 : 0 ≤ 3 / 5 * d - 2 := by
      have := Real.exp_pos (2 * L / 5)
      linarith only [hcc, hs0, S4, hbb, this]
    have hprod : 0 ≤ (mb - 1) * (3 / 5 * d - 2) := mul_nonneg (by linarith only [hmb]) hd3
    have hZ : 1 + (2 * (2 * ν * 25 ^ ν + ν * L) + 2 * (8 * Real.exp (2 * L / 5))) +
        (s + m * (2 * d + 2 + 2 * d / 5)) + 1 ≤ 3 * mb * E * T := by
      have hV : 3 * mb * E * T = 3 * mb * d := by rw [mul_assoc (3 * mb), hET]
      rw [hV]
      have := Real.exp_pos (2 * L / 5)
      linarith only [S4, hmx2, hprod]
    have hZ0 : 0 ≤ 1 + (2 * (2 * ν * 25 ^ ν + ν * L) + 2 * (8 * Real.exp (2 * L / 5))) +
        (s + m * (2 * d + 2 + 2 * d / 5)) := by positivity
    rw [Real.log_le_iff_le_exp (by positivity)]
    have h1Z := Real.one_le_exp hZ0
    calc 1 + 2 * N ^ 2 * X ^ 2 * Real.exp (s + m * (2 * d + 2 + 2 * d / 5))
        ≤ 2 * Real.exp (1 + (2 * (2 * ν * 25 ^ ν + ν * L) + 2 * (8 * Real.exp (2 * L / 5))) +
          (s + m * (2 * d + 2 + 2 * d / 5))) := by linarith only [hP, h1Z]
      _ ≤ Real.exp 1 * Real.exp (1 + (2 * (2 * ν * 25 ^ ν + ν * L) +
          2 * (8 * Real.exp (2 * L / 5))) + (s + m * (2 * d + 2 + 2 * d / 5))) := by gcongr
      _ = Real.exp (1 + (1 + (2 * (2 * ν * 25 ^ ν + ν * L) + 2 * (8 * Real.exp (2 * L / 5))) +
          (s + m * (2 * d + 2 + 2 * d / 5)))) := (Real.exp_add _ _).symm
      _ ≤ Real.exp (3 * mb * E * T) := Real.exp_le_exp.2 (by linarith only [hZ])
  · have e : -(A - μ) * (D / 2) + μ = -Λ := by linear_combination hμ
    rw [e]; exact Λ3
  · have haa : (0 : ℝ) ≤ 4 * ν * 8 ^ ν := by positivity
    have hbb : (0 : ℝ) ≤ 5 * (ν : ℝ) / 4 * L := by positivity
    have hm'eq : m' = A - 10 * mb * E := by rw [hm', hA]; ring
    have hAμ : (A - μ) * (D / 2 + 1) = A + Λ := by linear_combination (-1 : ℝ) * hμ
    have hAμD : (A - μ) * D ≤ 2 * (A + Λ) := by linarith only [hμA, hAμ]
    have h2 : mb * E * D = mb * T := by rw [mul_assoc, hED]
    have hAT : A * T ≤ mb * T := mul_le_mul_of_nonneg_right hAhi hT0.le
    have hprod : 0 ≤ (mb - 1) * (T - 2 / 5) :=
      mul_nonneg (by linarith only [hmb]) (by linarith only [hs0, S5, haa, hbb])
    rw [hm'eq]
    linarith only [hlog2, S5, Λ1, hAhi, hAμD, h2, hAT, hprod]
  · calc 2 * ↑ν * (8 * D) ^ ν * Real.exp (-A * (D / 2))
        ≤ Real.exp Λ * Real.exp (-A * (D / 2)) := by gcongr
      _ = Real.exp (Λ + -A * (D / 2)) := (Real.exp_add _ _).symm
      _ ≤ 1 := by
        rw [← Real.exp_zero]; exact Real.exp_le_exp.2 (by linarith only [hΛD, hAD])


theorem exists_levelScale (ν : ℕ) : ∃ K₁ : ℝ, ∀ K₀ : ℝ, K₁ ≤ K₀ → ∀ mbase : ℝ, 1 ≤ mbase →
    ∀ k : ℕ, LevelScale ν K₀ k (massSeq K₀ mbase (13 * mbase) k) (locLoss K₀ mbase k)
      (iterRate ν K₀ (massSeq K₀ mbase (13 * mbase) k) (locLoss K₀ mbase k) k)
      (massSeq K₀ mbase (13 * mbase) (k + 1)) := by
  obtain ⟨L₁, hL₁⟩ := eventually_atTop.1 (eventually_scaleBounds ν)
  refine ⟨max L₁ 7000, fun K₀ hK mb hmb k => ?_⟩
  have hK1 : L₁ ≤ K₀ := (le_max_left _ _).trans hK
  have hK2 : 7000 ≤ K₀ := (le_max_right _ _).trans hK
  have hp : (1 : ℝ) ≤ (5 / 4 : ℝ) ^ k := one_le_pow₀ (by norm_num)
  have hLK : K₀ ≤ K₀ * (5 / 4 : ℝ) ^ k := by nlinarith only [hK2, hp]
  have hS := hL₁ _ (hK1.trans hLK)
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith only [this]
  have hK32 : 32 * Real.log 2 ≤ K₀ := by linarith only [hK2, hlog2]
  have hC : (0 : ℝ) ≤ 13 * mb := by linarith only [hmb]
  have h0 : scaleD K₀ 0 ^ (-(1 / 8 : ℝ)) ≤ 1 / 52 := by
    rw [scaleD_eq, ← Real.exp_mul]
    have e : K₀ * (5 / 4 : ℝ) ^ 0 * -(1 / 8 : ℝ) = -(K₀ / 8) := by ring
    rw [e, Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
    have h := Real.add_one_le_exp (K₀ / 8)
    norm_num
    linarith only [hK2, h]
  have hsmall : 2 * (13 * mb) * scaleD K₀ 0 ^ (-(1 / 8 : ℝ)) ≤ mb / 2 := by
    have := mul_le_mul_of_nonneg_left h0 (show 0 ≤ 2 * (13 * mb) by linarith only [hC])
    linarith only [this]
  have hlow := half_le_massSeq hK32 hC hsmall
  have hm1 := hlow k
  have hm2 : massSeq K₀ mb (13 * mb) k ≤ mb := by
    have := massSeq_antitone K₀ mb hC (Nat.zero_le k)
    have h00 : massSeq K₀ mb (13 * mb) 0 = mb := by simp [massSeq]
    linarith only [this, h00]
  have hm'0 : 0 ≤ massSeq K₀ mb (13 * mb) (k + 1) := by
    have := hlow (k + 1)
    linarith only [hm1, hm2, this]
  have hm' : massSeq K₀ mb (13 * mb) (k + 1) =
      massSeq K₀ mb (13 * mb) k - 13 * mb * Real.exp (-(K₀ * (5 / 4 : ℝ) ^ k / 8)) := by
    rw [massSeq_succ, scaleD_eq, ← Real.exp_mul]
    congr 3; ring
  exact levelScale_core ν k rfl hmb hm1 hm2 hm'0 hm' hS

end FroehlichSpencer.T12

end
