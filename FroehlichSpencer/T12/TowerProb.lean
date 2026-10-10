/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.T12.Tower
public import FroehlichSpencer.T12.Tails


@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace FroehlichSpencer.T12

open Multiscale

private theorem stage_real_bound {ν : ℕ} {K₀ : ℝ} (hK : 0 < K₀) {p Cb L : ℝ} (hp : 0 < p)
    (hCb : 0 ≤ Cb) (hL : 1 ≤ L) (h1 : scaleD K₀ 1 / 5 ≤ L ^ (3 / 4 : ℝ)) (j : ℕ) :
    Cb * (4 ^ j * L + 1) ^ ν * scaleD K₀ (towerLevel K₀ (4 ^ j * L)) ^ (-(5 * (p + ν) / 3)) ≤
      Cb * 2 ^ ν * ((4 : ℝ) ^ (-p)) ^ j * L ^ (-p) := by
  set l : ℝ := 4 ^ j * L with hl
  have hl1 : 1 ≤ l := hL.trans (le_mul_of_one_le_left (by linarith) (one_le_pow₀ (by norm_num)))
  have hl0 : 0 < l := by linarith
  have hLl : L ^ (3 / 4 : ℝ) ≤ l ^ (3 / 4 : ℝ) :=
    Real.rpow_le_rpow (by linarith) (le_mul_of_one_le_left (by linarith)
      (one_le_pow₀ (by norm_num))) (by norm_num)
  have hd01 : scaleD K₀ 0 ≤ scaleD K₀ 1 := scaleD_mono_of_nonneg hK.le (Nat.zero_le 1)
  have h0 : scaleD K₀ 0 / 5 ≤ l ^ (3 / 4 : ℝ) := by linarith
  have hlt := lt_scaleD_towerLevel hK h0
  have hd : l ^ (3 / 5 : ℝ) ≤ scaleD K₀ (towerLevel K₀ l) := by
    refine le_trans ?_ hlt.le
    rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hl0.le _), ← Real.rpow_mul hl0.le]
    have : (1 : ℝ) ≤ 5 ^ (4 / 5 : ℝ) := Real.one_le_rpow (by norm_num) (by norm_num)
    have h35 : (0 : ℝ) ≤ l ^ ((3 / 4 : ℝ) * (4 / 5)) := Real.rpow_nonneg hl0.le _
    have : (3 / 4 : ℝ) * (4 / 5) = 3 / 5 := by norm_num
    rw [this]
    nlinarith [Real.rpow_nonneg hl0.le (3 / 5 : ℝ)]
  have hq : (0 : ℝ) ≤ 5 * (p + ν) / 3 := by positivity
  have hdq : scaleD K₀ (towerLevel K₀ l) ^ (-(5 * (p + ν) / 3)) ≤ l ^ (-(p + ν : ℝ)) := by
    calc scaleD K₀ (towerLevel K₀ l) ^ (-(5 * (p + ν) / 3))
        ≤ (l ^ (3 / 5 : ℝ)) ^ (-(5 * (p + ν) / 3)) :=
          Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hl0 _) hd (by linarith)
      _ = l ^ (-(p + ν : ℝ)) := by
          rw [← Real.rpow_mul hl0.le]; congr 1; ring
  have hpow : (4 ^ j * L + 1) ^ ν ≤ 2 ^ ν * l ^ ν := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by linarith) (by linarith) ν
  have hlp : l ^ (ν : ℝ) * l ^ (-(p + ν : ℝ)) = ((4 : ℝ) ^ (-p)) ^ j * L ^ (-p) := by
    rw [← Real.rpow_add hl0]
    have : (ν : ℝ) + -(p + ν) = -p := by ring
    rw [this, hl, Real.mul_rpow (by positivity) (by linarith)]
    congr 1
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast,
      ← Real.rpow_mul (by norm_num)]
    congr 1; ring
  have hpos : 0 ≤ scaleD K₀ (towerLevel K₀ l) ^ (-(5 * (p + ν) / 3)) :=
    Real.rpow_nonneg (scaleD_pos _ _).le _
  calc Cb * (4 ^ j * L + 1) ^ ν * scaleD K₀ (towerLevel K₀ l) ^ (-(5 * (p + ν) / 3))
      ≤ Cb * (2 ^ ν * l ^ ν) * l ^ (-(p + ν : ℝ)) := by
        gcongr
    _ = Cb * 2 ^ ν * (l ^ (ν : ℝ) * l ^ (-(p + ν : ℝ))) := by
        rw [Real.rpow_natCast]; ring
    _ = _ := by rw [hlp]; ring

private theorem tower_compl_le {ν : ℕ} (μ : Measure (Configuration ν)) (P : Params)
    (hK : 0 < P.K₀) {p : ℝ} (hp : 0 < p) {Cb : ℝ} (hCb : 0 ≤ Cb)
    (Λ : Finset (Site ν)) (a : Site ν) {L : ℝ} (hL : 1 ≤ L)
    (h1 : scaleD P.K₀ 1 / 5 ≤ L ^ (3 / 4 : ℝ))
    (hs : ∀ (R : ℝ) (k : ℕ), 1 ≤ k → 1 ≤ R →
      μ {v | ∃ x, siteDist ν a x ≤ R ∧ x ∈ singularSetsIn P Λ v k} ≤
        ENNReal.ofReal (Cb * R ^ ν * scaleD P.K₀ k ^ (-(5 * (p + ν) / 3)))) :
    μ (towerEvent P Λ a L)ᶜ ≤
      ENNReal.ofReal (Cb * 2 ^ ν / (1 - (4 : ℝ) ^ (-p)) * L ^ (-p)) := by
  have hr : (4 : ℝ) ^ (-p) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hr0 : 0 ≤ (4 : ℝ) ^ (-p) := by positivity
  have hLp : 0 ≤ L ^ (-p) := Real.rpow_nonneg (by linarith) _
  have hsub : (towerEvent P Λ a L)ᶜ ⊆ ⋃ j : ℕ, {v | ∃ x, siteDist ν a x ≤ 4 ^ j * L + 1 ∧
      x ∈ singularSetsIn P Λ v (towerLevel P.K₀ (4 ^ j * L))} := by
    intro v hv
    simp only [towerEvent, Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall, not_not] at hv
    obtain ⟨j, x, hx, hxs⟩ := hv
    exact Set.mem_iUnion.2 ⟨j, x, hx, hxs⟩
  have hstage : ∀ j : ℕ, μ {v | ∃ x, siteDist ν a x ≤ 4 ^ j * L + 1 ∧
      x ∈ singularSetsIn P Λ v (towerLevel P.K₀ (4 ^ j * L))} ≤
      ENNReal.ofReal (Cb * 2 ^ ν * L ^ (-p) * ((4 : ℝ) ^ (-p)) ^ j) := fun j => by
    have hl1 : 1 ≤ 4 ^ j * L :=
      hL.trans (le_mul_of_one_le_left (by linarith) (one_le_pow₀ (by norm_num)))
    refine (hs _ _ (one_le_towerLevel hK ?_) (by linarith)).trans
      (ENNReal.ofReal_le_ofReal ?_)
    · exact h1.trans (Real.rpow_le_rpow (by linarith) (le_mul_of_one_le_left (by linarith)
        (one_le_pow₀ (by norm_num))) (by norm_num))
    · have := stage_real_bound (ν := ν) hK hp hCb hL h1 j
      linarith [mul_comm (L ^ (-p)) (((4 : ℝ) ^ (-p)) ^ j)]
  calc μ (towerEvent P Λ a L)ᶜ
      ≤ μ (⋃ j : ℕ, {v | ∃ x, siteDist ν a x ≤ 4 ^ j * L + 1 ∧
          x ∈ singularSetsIn P Λ v (towerLevel P.K₀ (4 ^ j * L))}) := measure_mono hsub
    _ ≤ ∑' j : ℕ, μ {v | ∃ x, siteDist ν a x ≤ 4 ^ j * L + 1 ∧
          x ∈ singularSetsIn P Λ v (towerLevel P.K₀ (4 ^ j * L))} := measure_iUnion_le _
    _ ≤ ∑' j : ℕ, ENNReal.ofReal (Cb * 2 ^ ν * L ^ (-p) * ((4 : ℝ) ^ (-p)) ^ j) :=
        ENNReal.tsum_le_tsum hstage
    _ = ENNReal.ofReal (∑' j : ℕ, Cb * 2 ^ ν * L ^ (-p) * ((4 : ℝ) ^ (-p)) ^ j) := by
        rw [ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity)]
        exact (summable_geometric_of_lt_one hr0 hr).mul_left _
    _ = _ := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr]
        congr 1; field_simp

private theorem two_center_le {ν : ℕ} (μ : Measure (Configuration ν)) (T U : Set (Configuration ν))
    {c : ℝ} (hc : 0 ≤ c) (hT : μ Tᶜ ≤ ENNReal.ofReal c) (hU : μ Uᶜ ≤ ENNReal.ofReal c) :
    μ (T ∩ U)ᶜ ≤ ENNReal.ofReal (2 * c) := by
  rw [Set.compl_inter]
  calc μ (Tᶜ ∪ Uᶜ) ≤ μ Tᶜ + μ Uᶜ := measure_union_le _ _
    _ ≤ ENNReal.ofReal c + ENNReal.ofReal c := add_le_add hT hU
    _ = ENNReal.ofReal (2 * c) := by
        rw [← ENNReal.ofReal_add hc hc]; congr 1; ring

private theorem towerConst_nonneg {ν : ℕ} {p Cb : ℝ} (hp : 0 < p) (hCb : 0 ≤ Cb) :
    0 ≤ Cb * 2 ^ ν / (1 - (4 : ℝ) ^ (-p)) := by
  have hr : (4 : ℝ) ^ (-p) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  exact div_nonneg (by positivity) (by linarith)


theorem exists_towerEvent_compl_le_boundedDensity (ν : ℕ) {K₀ : ℝ} (hK : 0 < K₀) {p : ℝ}
    (hp : 0 < p) :
    ∃ δ₀ C : ℝ, ∀ (law : Measure ℝ) [IsProbabilityMeasure law] (δ : ℝ), HasBoundedDensity law δ →
      δ₀ ≤ δ → ∀ (P : Params), P.K₀ = K₀ → P.Nthr = Real.sqrt δ →
        ∀ (Λ : Finset (Site ν)) (a b : Site ν) (L : ℝ), 1 ≤ L →
          scaleD K₀ 1 / 5 ≤ L ^ (3 / 4 : ℝ) →
          MeasurableSet (towerEvent P Λ a L) ∧
          configurationMeasure ν law (towerEvent P Λ a L)ᶜ ≤ ENNReal.ofReal (C * L ^ (-p)) ∧
          MeasurableSet (towerEvent P Λ a L ∩ towerEvent P Λ b L) ∧
          configurationMeasure ν law (towerEvent P Λ a L ∩ towerEvent P Λ b L)ᶜ ≤
            ENNReal.ofReal (2 * C * L ^ (-p)) := by
  have hq : 0 < 5 * (p + ν) / 3 := by positivity
  obtain ⟨δ₀, Cb, h⟩ := exists_ballEvent_le_boundedDensity ν hK hq
  refine ⟨δ₀, max Cb 0 * 2 ^ ν / (1 - (4 : ℝ) ^ (-p)),
    fun law _ δ hlaw hδ P hP hN Λ a b L hL h1 => ?_⟩
  have hCb : 0 ≤ max Cb 0 := le_max_right _ _
  have hs : ∀ (x : Site ν), ∀ (R : ℝ) (k : ℕ), 1 ≤ k → 1 ≤ R →
      configurationMeasure ν law
        {v | ∃ y, siteDist ν x y ≤ R ∧ y ∈ singularSetsIn P Λ v k} ≤
        ENNReal.ofReal (max Cb 0 * R ^ ν * scaleD P.K₀ k ^ (-(5 * (p + ν) / 3))) :=
    fun x R k hk hR => by
      refine (h law δ hlaw hδ P hP hN Λ x R k hk hR).2.trans (ENNReal.ofReal_le_ofReal ?_)
      rw [hP]
      have := Real.rpow_nonneg (scaleD_pos K₀ k).le (-(5 * (p + ν) / 3))
      have hR' : 0 ≤ R ^ ν := by positivity
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hR') this
  have hK' : 0 < P.K₀ := hP ▸ hK
  have h1' : scaleD P.K₀ 1 / 5 ≤ L ^ (3 / 4 : ℝ) := hP ▸ h1
  have hTa := tower_compl_le (configurationMeasure ν law) P hK' hp hCb Λ a hL h1' (hs a)
  have hTb := tower_compl_le (configurationMeasure ν law) P hK' hp hCb Λ b hL h1' (hs b)
  have hc := mul_nonneg (towerConst_nonneg (ν := ν) hp hCb)
    (Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ L) (-p))
  refine ⟨measurableSet_towerEvent P Λ a L, hTa,
    (measurableSet_towerEvent P Λ a L).inter (measurableSet_towerEvent P Λ b L), ?_⟩
  have := two_center_le _ _ _ hc hTa hTb
  convert this using 2; ring


theorem exists_towerEvent_compl_le_gaussian (ν : ℕ) {K₀ : ℝ} (hK : 0 < K₀) {γ : ℝ} (hγ : 0 < γ)
    {p : ℝ} (hp : 0 < p) :
    ∃ E₀ C : ℝ, ∀ (P : Params), P.K₀ = K₀ → E₀ ≤ |P.E - 2 * ν| → P.Nthr = |P.E| / 2 →
      ∀ (Λ : Finset (Site ν)) (a b : Site ν) (L : ℝ), 1 ≤ L →
        scaleD K₀ 1 / 5 ≤ L ^ (3 / 4 : ℝ) →
        MeasurableSet (towerEvent P Λ a L) ∧
          configurationMeasure ν (gaussianLaw γ hγ) (towerEvent P Λ a L)ᶜ ≤
            ENNReal.ofReal (C * L ^ (-p)) ∧
          MeasurableSet (towerEvent P Λ a L ∩ towerEvent P Λ b L) ∧
          configurationMeasure ν (gaussianLaw γ hγ) (towerEvent P Λ a L ∩ towerEvent P Λ b L)ᶜ ≤
            ENNReal.ofReal (2 * C * L ^ (-p)) := by
  have hq : 0 < 5 * (p + ν) / 3 := by positivity
  obtain ⟨E₀, Cb, h⟩ := exists_ballEvent_le_gaussian ν hK hγ hq
  refine ⟨E₀, max Cb 0 * 2 ^ ν / (1 - (4 : ℝ) ^ (-p)),
    fun P hP hE hN Λ a b L hL h1 => ?_⟩
  have hCb : 0 ≤ max Cb 0 := le_max_right _ _
  have hs : ∀ (x : Site ν), ∀ (R : ℝ) (k : ℕ), 1 ≤ k → 1 ≤ R →
      configurationMeasure ν (gaussianLaw γ hγ)
        {v | ∃ y, siteDist ν x y ≤ R ∧ y ∈ singularSetsIn P Λ v k} ≤
        ENNReal.ofReal (max Cb 0 * R ^ ν * scaleD P.K₀ k ^ (-(5 * (p + ν) / 3))) :=
    fun x R k hk hR => by
      refine (h P hP hE hN Λ x R k hk hR).2.trans (ENNReal.ofReal_le_ofReal ?_)
      rw [hP]
      have := Real.rpow_nonneg (scaleD_pos K₀ k).le (-(5 * (p + ν) / 3))
      have hR' : 0 ≤ R ^ ν := by positivity
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hR') this
  have hK' : 0 < P.K₀ := hP ▸ hK
  have h1' : scaleD P.K₀ 1 / 5 ≤ L ^ (3 / 4 : ℝ) := hP ▸ h1
  have hTa := tower_compl_le (configurationMeasure ν (gaussianLaw γ hγ)) P hK' hp hCb Λ a hL h1'
    (hs a)
  have hTb := tower_compl_le (configurationMeasure ν (gaussianLaw γ hγ)) P hK' hp hCb Λ b hL h1'
    (hs b)
  have hc := mul_nonneg (towerConst_nonneg (ν := ν) hp hCb)
    (Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ L) (-p))
  refine ⟨measurableSet_towerEvent P Λ a L, hTa,
    (measurableSet_towerEvent P Λ a L).inter (measurableSet_towerEvent P Λ b L), ?_⟩
  have := two_center_le _ _ _ hc hTa hTb
  convert this using 2; ring

end FroehlichSpencer.T12

end
