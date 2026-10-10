/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.Reduction.DyadicGeometry
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Summing the exceptional probabilities over dyadic shells -/

public section

namespace FroehlichSpencer.Reduction

@[expose] noncomputable def badRealTerm (ν : ℕ) (R K : ℝ) (x : Site ν) : ℝ :=
  (latticeLength ν x) ^ 2 *
    (K / Real.rpow (dyadicGreenScale ν R x) ((ν + 5 : ℕ) : ℝ))

@[expose] def badShellConstant (ν : ℕ) (K : ℝ) : ℝ :=
  72 ^ ν * 24 ^ 2 * 512 * K

private theorem badShell_pointwise (ν : ℕ) {R K : ℝ} (hR : 1 ≤ R)
    (hK : 0 ≤ K) (j : ℕ) (x : Site ν)
    (hx : dyadicShellIndex ν R x = j) :
    badRealTerm ν R K x ≤
      (24 : ℝ) ^ 2 * K /
        (R * (2 : ℝ) ^ j / 8) ^ (ν + 3 : ℕ) := by
  let N : ℝ := R * (2 : ℝ) ^ j / 8
  have hNpos : 0 < N := by
    dsimp [N]
    positivity
  have hL : latticeLength ν x ≤ 3 * R * (2 : ℝ) ^ j := by
    have h := dyadicShellIndex_radius_upper (lt_of_lt_of_le zero_lt_one hR) x
    rw [hx] at h
    exact h.le
  have hNscale : dyadicGreenScale ν R x = N := by
    simp [dyadicGreenScale, hx, N]
  have hradScale : 3 * R * (2 : ℝ) ^ j = 24 * N := by
    dsimp [N]
    ring
  have hcancel :
      (24 * N) ^ 2 * (K / N ^ (ν + 5 : ℕ)) =
        (24 : ℝ) ^ 2 * K / N ^ (ν + 3 : ℕ) := by
    have hsum : ν + 5 = (ν + 3) + 2 := by omega
    rw [mul_pow, hsum, pow_add]
    field_simp [hNpos.ne']
  have hbad :
      (latticeLength ν x) ^ 2 *
          (K / Real.rpow (dyadicGreenScale ν R x) ((ν + 5 : ℕ) : ℝ)) ≤
        (24 : ℝ) ^ 2 * K / N ^ (ν + 3 : ℕ) := by
    rw [hNscale]
    have hrpow : Real.rpow N ((ν + 5 : ℕ) : ℝ) = N ^ (ν + 5 : ℕ) := by
      exact Real.rpow_natCast N (ν + 5)
    rw [hrpow]
    calc
      (latticeLength ν x) ^ 2 * (K / N ^ (ν + 5 : ℕ)) ≤
          (3 * R * (2 : ℝ) ^ j) ^ 2 * (K / N ^ (ν + 5 : ℕ)) := by
            exact mul_le_mul_of_nonneg_right
              ((sq_le_sq₀ (latticeLength_nonneg ν x) (by positivity)).2 hL)
              (div_nonneg hK (by positivity))
      _ = (24 * N) ^ 2 * (K / N ^ (ν + 5 : ℕ)) := by rw [hradScale]
      _ = (24 : ℝ) ^ 2 * K / N ^ (ν + 3 : ℕ) := hcancel
  simpa [badRealTerm, N, hNscale] using hbad

set_option linter.style.haveILetI false in
private theorem badShell_sum_bound (ν : ℕ) {R K : ℝ} (hR : 1 ≤ R)
    (hK : 0 ≤ K) (j : ℕ) :
    ∑' x : {x : Site ν // dyadicShellIndex ν R x = j},
      ENNReal.ofReal (badRealTerm ν R K x.1) ≤
        ENNReal.ofReal (badShellConstant ν K / R ^ 3 * (1 / 8 : ℝ) ^ j) := by
  classical
  let S : Set (Site ν) := {x | dyadicShellIndex ν R x = j}
  have hSfin : S.Finite := by
    exact finite_dyadicShell ν (lt_of_lt_of_le zero_lt_one hR) j
  letI : Fintype S := hSfin.fintype
  obtain ⟨B, hB, hBcard⟩ := exists_dyadicShell_ball_finset ν hR j
  let hinj : S → (↑B : Set (Site ν)) := fun x => ⟨x.1, hB x.1 x.2⟩
  have hinj_inj : Function.Injective hinj := by
    intro a b hab
    apply Subtype.ext
    simpa [hinj] using congrArg (fun y : (↑B : Set (Site ν)) => y.1) hab
  have hcardNat : Fintype.card S ≤ Fintype.card (↑B : Set (Site ν)) :=
    Fintype.card_le_of_injective hinj hinj_inj
  have hcardReal : (Fintype.card S : ℝ) ≤ (B.card : ℝ) := by
    have hcast : (Fintype.card S : ℝ) ≤ (Fintype.card (↑B : Set (Site ν)) : ℝ) :=
      Nat.cast_le.mpr hcardNat
    simpa using hcast
  let N : ℝ := R * (2 : ℝ) ^ j / 8
  have hNpos : 0 < N := by dsimp [N]; positivity
  have hcountScale : 9 * R * (2 : ℝ) ^ j = 72 * N := by
    dsimp [N]
    ring
  have hradScale : 3 * R * (2 : ℝ) ^ j = 24 * N := by
    dsimp [N]
    ring
  have hcardBound : (Fintype.card S : ℝ) ≤ (72 * N) ^ ν := by
    calc
      (Fintype.card S : ℝ) ≤ (B.card : ℝ) := hcardReal
      _ ≤ (9 * R * (2 : ℝ) ^ j) ^ ν := hBcard
      _ = (72 * N) ^ ν := by rw [hcountScale]
  have hper : 0 ≤ (24 : ℝ) ^ 2 * K / N ^ (ν + 3 : ℕ) := by positivity
  have hsumReal :
      (Fintype.card S : ℝ) * ((24 : ℝ) ^ 2 * K / N ^ (ν + 3 : ℕ)) ≤
        badShellConstant ν K / R ^ 3 * (1 / 8 : ℝ) ^ j := by
    calc
      (Fintype.card S : ℝ) * ((24 : ℝ) ^ 2 * K / N ^ (ν + 3 : ℕ)) ≤
          (72 * N) ^ ν * ((24 : ℝ) ^ 2 * K / N ^ (ν + 3 : ℕ)) :=
            mul_le_mul_of_nonneg_right hcardBound hper
      _ = 72 ^ ν * 24 ^ 2 * K / N ^ 3 := by
        rw [mul_pow]
        have hsum : ν + 3 = ν + 3 := rfl
        rw [hsum, pow_add]
        field_simp [hNpos.ne']
      _ = badShellConstant ν K / R ^ 3 * (1 / 8 : ℝ) ^ j := by
        dsimp [badShellConstant, N]
        have h8 : (8 : ℝ) ^ j ≠ 0 := pow_ne_zero _ (by norm_num)
        have hpow : ((2 : ℝ) ^ j) ^ 3 = (8 : ℝ) ^ j := by
          rw [← pow_mul, Nat.mul_comm j 3, pow_mul]
          norm_num
        have hNinv3 :
            1 / (R * (2 : ℝ) ^ j / 8) ^ 3 =
              512 / (R ^ 3 * (8 : ℝ) ^ j) := by
          rw [div_pow, mul_pow, hpow]
          norm_num
        have hrecip : (1 / 8 : ℝ) ^ j * (8 : ℝ) ^ j = 1 := by
          rw [← mul_pow]
          norm_num
        have hrecip' : (8 : ℝ) ^ j * (1 / 8 : ℝ) ^ j = 1 := by
          rw [mul_comm]
          exact hrecip
        calc
          72 ^ ν * 24 ^ 2 * K / (R * (2 : ℝ) ^ j / 8) ^ 3 =
              72 ^ ν * 24 ^ 2 * K *
                (1 / (R * (2 : ℝ) ^ j / 8) ^ 3) := by ring
          _ = 72 ^ ν * 24 ^ 2 * K *
                (512 / (R ^ 3 * (8 : ℝ) ^ j) : ℝ) := by rw [hNinv3]
          _ = 72 ^ ν * 24 ^ 2 * 512 * K / R ^ 3 * (1 / 8 : ℝ) ^ j := by
                field_simp [h8]
                calc
                  _ = K * 1 := by ring
                  _ = K * ((8 : ℝ) ^ j * (1 / 8 : ℝ) ^ j) := by rw [hrecip']
                  _ = K * (8 : ℝ) ^ j * (1 / 8 : ℝ) ^ j := by ring
  have hperSite : ∀ x : S,
      badRealTerm ν R K x.1 ≤ (24 : ℝ) ^ 2 * K / N ^ (ν + 3 : ℕ) := by
    intro x
    have h := badShell_pointwise ν hR hK j x.1 x.2
    simpa [N] using h
  calc
    ∑' x : S, ENNReal.ofReal (badRealTerm ν R K x.1) ≤
        ∑' x : S, ENNReal.ofReal ((24 : ℝ) ^ 2 * K / N ^ (ν + 3 : ℕ)) :=
      ENNReal.tsum_le_tsum (fun x => ENNReal.ofReal_le_ofReal (hperSite x))
    _ = ENNReal.ofReal ((Fintype.card S : ℝ) *
        ((24 : ℝ) ^ 2 * K / N ^ (ν + 3 : ℕ))) := by
      rw [tsum_fintype]
      simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ENNReal.ofReal (badShellConstant ν K / R ^ 3 * (1 / 8 : ℝ) ^ j) :=
      ENNReal.ofReal_le_ofReal hsumReal

theorem bad_global_sum_bound (ν : ℕ) {R K : ℝ} (hR : 1 ≤ R)
    (hK : 0 ≤ K) :
    ∑' x : Site ν, ENNReal.ofReal (badRealTerm ν R K x) ≤
      ENNReal.ofReal (badShellConstant ν K / R ^ 3 * (8 / 7 : ℝ)) := by
  classical
  let idx : Site ν → ℕ := dyadicShellIndex ν R
  have hC : 0 ≤ badShellConstant ν K / R ^ 3 := by
    unfold badShellConstant
    positivity
  calc
    ∑' x : Site ν, ENNReal.ofReal (badRealTerm ν R K x) =
        ∑' j : ℕ, ∑' x : {x : Site ν // idx x = j},
          ENNReal.ofReal (badRealTerm ν R K x.1) := by
      symm
      exact ENNReal.tsum_fiberwise
        (fun x => ENNReal.ofReal (badRealTerm ν R K x)) idx
    _ ≤ ∑' j : ℕ,
        ENNReal.ofReal (badShellConstant ν K / R ^ 3 * (1 / 8 : ℝ) ^ j) :=
      ENNReal.tsum_le_tsum (fun j => by
        simpa [idx] using badShell_sum_bound ν hR hK j)
    _ = ENNReal.ofReal (badShellConstant ν K / R ^ 3 * (8 / 7 : ℝ)) := by
      rw [← ENNReal.ofReal_tsum_of_nonneg]
      · rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
        norm_num
      · intro j
        exact mul_nonneg hC (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 8) _)
      · exact (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _

end FroehlichSpencer.Reduction

end
