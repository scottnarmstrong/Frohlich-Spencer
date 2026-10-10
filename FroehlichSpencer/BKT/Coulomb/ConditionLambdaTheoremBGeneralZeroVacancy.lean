/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Coulomb.ConditionLambdaTheoremBObstruction
public import FroehlichSpencer.BKT.Coulomb.ConditionLambdaTheoremBGeneral
import Mathlib.Tactic

/-!
# The zero-vacancy case `λ(0) = 0` is outside FS81's argument

The density-one law is `λ(±1) = 1` and `λ(n) = 0` otherwise. It is even and nonnegative, and it
satisfies Condition λ as printed with `C = 1`, `α = ε = 0` (`densityOneLaw_conditionLambda`). But
`λ(0) = 0`, so every site carries a unit charge.

* `densityOne_partition_eq_zero`, `densityOne_regionPartition_eq_zero`: a region with an odd
  number of sites has no neutral configuration. So `Z_Λ = 0` and the Gibbs measure (1.7) is
  undefined.
* `densityOneCorr_pair_eq`: on a two-site region `{x, y}` the only configurations are the forced
  dipoles `±(δ_x − δ_y)`. Hence `G_ξ(x, y) = e^{−κξ²p/2} cosh(ξκp)` with `p = 2E(δ_x − δ_y)`.
* **`densityOneCorr_pair_ge`**: `G_ξ(x, y) ≥ 1/2` for every pair, every `κ ≥ 0` and every
  `0 ≤ ξ ≤ 1`. There is no decay in the distance.
* `densityOne_exceeds_powerLaw`, **`not_coulombB_conditionLambda_free_fullRange_zeroVacancy`**:
  the region-uniform full-range Theorem B without the vacancy bound is false, at every `κ`.

The reason in FS81:
- (5.38) writes `λ̂(φ) = 1 + Σ_{q ≥ 1} 2λ(q) cos(qφ)`, i.e. it takes `λ(0) = 1`.
- It then decomposes `λ̂ = Σ_q ζ_q (1 + z(q) cos(qφ))` with `Σ ζ_q = 1`.
- The mean of `λ̂` over `φ` is `λ(0)`. So this decomposition, and with it the ensemble expansions
  of Theorems 2.1 and 5.2 about the vacuum, needs `λ(0) > 0` after normalisation.
- With `λ(0) = 0` there is no vacuum to expand about. FS81's remark after Condition λ (J p. 531)
  points to crystalline phases at high density.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Coulomb

open Filter Topology FroehlichSpencer.BKT.Generic.Marked

/-! ### The density-one law -/

/-- The density-one law `λ(±1) = 1`, `λ(n) = 0` otherwise; in particular `λ(0) = 0`. Every site
carries a unit charge. -/
def densityOneLawInternal : ℤ → ℝ := fun n => if n.natAbs = 1 then 1 else 0

theorem densityOneLaw_zero : densityOneLawInternal 0 = 0 := by simp [densityOneLawInternal]

theorem densityOneLaw_nonneg (n : ℤ) : 0 ≤ densityOneLawInternal n := by
  unfold densityOneLawInternal
  split_ifs <;> norm_num

/-- The density-one law satisfies Condition λ as printed, with `C = 1`, `α = ε = 0`. -/
theorem densityOneLaw_conditionLambda (κ : ℝ) :
    ConditionLambdaInternal 1 0 0 κ densityOneLawInternal := by
  refine ⟨fun n => by simp [densityOneLawInternal], fun n => ?_⟩
  simp only [zero_mul, add_zero, Real.exp_zero, mul_one]
  unfold densityOneLawInternal
  split_ifs <;> norm_num

theorem densityOneLaw_eq_zero {n : ℤ} (hn : n ∉ ({-1, 0, 1} : Finset ℤ)) :
    densityOneLawInternal n = 0 := by
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
  unfold densityOneLawInternal
  have h1 : n.natAbs ≠ 1 := by omega
  simp only [h1, ↓reduceIte]

/-! ### Odd regions: the partition function vanishes -/

theorem intCast_zmodTwo_of_natAbs_eq_one {n : ℤ} (h : n.natAbs = 1) : (n : ZMod 2) = 1 := by
  rcases Int.natAbs_eq n with h1 | h1 <;> rw [h1, h] <;> simp

/-- **No neutral density-one configuration on an odd number of sites**: for the density-one law
the free-boundary partition function `Z_Λ` (FS81 (1.8), neutral configurations) is `0` whenever
the number of sites is odd, so the Gibbs measure (1.7) is undefined there. -/
theorem densityOne_partition_eq_zero {V : Type*} [Fintype V] [DecidableEq V]
    (hodd : Odd (Fintype.card V)) (T : (V → ℝ) →ₗ[ℝ] V → ℝ) (κ : ℝ) :
    fullGasPartitionInternal T κ (fun _ => densityOneLawInternal) = 0 := by
  unfold fullGasPartitionInternal
  have hzero : ∀ q : V → ℤ, gasWeightInternal T κ (fun _ => densityOneLawInternal) q = 0 := by
    intro q
    unfold gasWeightInternal
    split_ifs with hq
    · obtain ⟨j, hj⟩ : ∃ j, densityOneLawInternal (q j) = 0 := by
        by_contra hne
        push Not at hne
        have h1 : ∀ j, (q j).natAbs = 1 := fun j => by
          have := hne j
          unfold densityOneLawInternal at this
          by_contra h
          exact this (by simp only [h, ↓reduceIte])
        have hcast : ((∑ j, q j : ℤ) : ZMod 2) = (Fintype.card V : ZMod 2) := by
          push_cast
          rw [Finset.sum_congr rfl fun j _ => intCast_zmodTwo_of_natAbs_eq_one (h1 j)]
          simp
        rw [hq, Int.cast_zero, eq_comm, ZMod.natCast_eq_zero_iff_even] at hcast
        exact Nat.not_even_iff_odd.2 hodd hcast
      rw [Finset.prod_eq_zero (Finset.mem_univ j) hj, zero_mul]
    · rfl
  simp [hzero]

/-- The free-boundary partition function of the density-one law vanishes on every region with an
odd number of sites. -/
theorem densityOne_regionPartition_eq_zero (Λ : Finset (ℤ × ℤ)) (hodd : Odd Λ.card) (κ : ℝ) :
    fullGasPartitionInternal (freePotentialOpInternal (fun v : Λ => (v : ℤ × ℤ))) κ
      (fun _ => densityOneLawInternal) = 0 :=
  densityOne_partition_eq_zero (by rwa [Fintype.card_coe]) _ κ

/-! ### Two-site regions: no decay -/

/-- The two-site region `{x, y}`. -/
abbrev pairRegionInternal (x y : ℤ × ℤ) : Finset (ℤ × ℤ) := {x, y}

/-- The site `x` of `pairRegionInternal x y`. -/
abbrev pairLeftInternal (x y : ℤ × ℤ) : pairRegionInternal x y := ⟨x, by simp⟩

/-- The site `y` of `pairRegionInternal x y`. -/
abbrev pairRightInternal (x y : ℤ × ℤ) : pairRegionInternal x y := ⟨y, by simp⟩

theorem pairLeft_ne_right {x y : ℤ × ℤ} (hxy : x ≠ y) :
    pairLeftInternal x y ≠ pairRightInternal x y :=
  fun h => hxy (congrArg Subtype.val h)

theorem pair_cases (x y : ℤ × ℤ) (v : pairRegionInternal x y) :
    v = pairLeftInternal x y ∨ v = pairRightInternal x y := by
  obtain ⟨v, hv⟩ := v
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- `p(x, y) = ⟨δ_x − δ_y, C(δ_x − δ_y)⟩ = 2E(δ_x − δ_y)`, the free energy of the dipole. -/
def pairDipoleQuadInternal (x y : ℤ × ℤ) : ℝ :=
  freeQuadInternal (fun v : pairRegionInternal x y => (v : ℤ × ℤ))
    (dipoleRealInternal (pairLeftInternal x y) (pairRightInternal x y))

theorem pairDipoleQuad_nonneg (x y : ℤ × ℤ) : 0 ≤ pairDipoleQuadInternal x y := by
  have h := free_chargeEnergy_ge (fun v : pairRegionInternal x y => (v : ℤ × ℤ))
    Subtype.val_injective (dipoleMark (pairLeftInternal x y) (pairRightInternal x y))
    (sum_univ_dipoleMark _ _)
  rw [chargeEnergy_dipoleMark_eq] at h
  have h0 : 0 ≤ (∑ j, ((dipoleMark (pairLeftInternal x y) (pairRightInternal x y) j : ℤ) : ℝ) ^ 2) /
      16 := by positivity
  unfold pairDipoleQuadInternal
  linarith

/-- **The forced dipole.** For the density-one law on `{x, y}` the only neutral configurations are
`±(δ_x − δ_y)`, and `G_ξ(x, y) = e^{−κξ²p/2} cosh(ξκp)`, `p = pairDipoleQuadInternal x y`. -/
theorem densityOneCorr_pair_eq {x y : ℤ × ℤ} (hxy : x ≠ y) (κ ξ : ℝ) :
    regionConditionLambdaFracCorrInternal (pairRegionInternal x y) κ densityOneLawInternal ξ x y =
      Real.exp (-(κ * ξ ^ 2 * pairDipoleQuadInternal x y / 2)) *
        Real.cosh (ξ * (κ * pairDipoleQuadInternal x y)) := by
  set p := pairDipoleQuadInternal x y with hp
  have hmem : x ∈ pairRegionInternal x y ∧ y ∈ pairRegionInternal x y := ⟨by simp, by simp⟩
  unfold regionConditionLambdaFracCorrInternal
  simp only [hmem, and_self, ↓reduceDIte]
  unfold freeConditionLambdaFracCorrInternal fullGasExpectationInternal fullGasPartitionInternal
  set T := freePotentialOpInternal (fun v : pairRegionInternal x y => (v : ℤ × ℤ)) with hT
  have hlam : ∀ n ∉ ({-1, 0, 1} : Finset ℤ), densityOneLawInternal n = 0 :=
    fun n hn => densityOneLaw_eq_zero hn
  have hZ := tsum_gasWeight_twoSites T (pairLeft_ne_right hxy) (pair_cases x y) κ
    densityOneLawInternal hlam (fun _ => 1)
  have hN := tsum_gasWeight_twoSites T (pairLeft_ne_right hxy) (pair_cases x y) κ
    densityOneLawInternal hlam (fun q => Real.cosh (ξ * (κ * freeChargePairingInternal
      (fun v : pairRegionInternal x y => (v : ℤ × ℤ))
      (dipoleRealInternal (pairLeftInternal x y) (pairRightInternal x y)) q)))
  simp only [mul_one] at hZ
  rw [hZ, hN]
  have hE : chargeEnergyInternal T (dipoleMark (pairLeftInternal x y) (pairRightInternal x y)) =
      p / 2 := by
    rw [hT, chargeEnergy_dipoleMark_eq]
    rfl
  simp only [freeChargePairing_dipoleMultiple, hE]
  have h1 : densityOneLawInternal 1 = 1 := by simp [densityOneLawInternal]
  have hm1 : densityOneLawInternal (-1) = 1 := by simp [densityOneLawInternal]
  have e1 : freeQuadInternal (fun v : pairRegionInternal x y => (v : ℤ × ℤ))
      (dipoleRealInternal (pairLeftInternal x y) (pairRightInternal x y)) = p := rfl
  have hDen : ∑ n ∈ ({-1, 0, 1} : Finset ℤ), densityOneLawInternal n *
      densityOneLawInternal (-n) * Real.exp (-κ * ((n : ℝ) ^ 2 * (p / 2))) =
      2 * Real.exp (-(κ * (p / 2))) := by
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
    simp only [neg_neg, neg_zero, h1, hm1, densityOneLaw_zero, Int.cast_neg, Int.cast_one,
      neg_one_sq, one_pow, one_mul, zero_mul, neg_mul]
    ring
  have hNum : ∑ n ∈ ({-1, 0, 1} : Finset ℤ), densityOneLawInternal n *
      densityOneLawInternal (-n) * Real.exp (-κ * ((n : ℝ) ^ 2 * (p / 2))) *
        Real.cosh (ξ * (κ * ((n : ℝ) * p))) =
      Real.cosh (ξ * (κ * p)) * (2 * Real.exp (-(κ * (p / 2)))) := by
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
    simp only [neg_neg, neg_zero, h1, hm1, densityOneLaw_zero, Int.cast_neg, Int.cast_one,
      neg_one_sq, one_pow, one_mul, zero_mul, neg_mul, mul_neg, Real.cosh_neg]
    ring
  rw [e1, hNum, hDen, mul_div_cancel_right₀ _ (by positivity)]

/-- **No decay for the density-one law**: on every two-site region, at every `κ ≥ 0` and every
`0 ≤ ξ ≤ 1`, `G_ξ(x, y) ≥ 1/2`, however far apart `x` and `y` are. -/
theorem densityOneCorr_pair_ge {x y : ℤ × ℤ} (hxy : x ≠ y) {κ ξ : ℝ} (hκ : 0 ≤ κ) (hξ0 : 0 ≤ ξ)
    (hξ1 : ξ ≤ 1) :
    1 / 2 ≤ regionConditionLambdaFracCorrInternal (pairRegionInternal x y) κ
      densityOneLawInternal ξ x y := by
  rw [densityOneCorr_pair_eq hxy]
  set p := pairDipoleQuadInternal x y
  have hp : 0 ≤ p := pairDipoleQuad_nonneg x y
  have hcosh : Real.exp (ξ * (κ * p)) / 2 ≤ Real.cosh (ξ * (κ * p)) := by
    rw [Real.cosh_eq]
    linarith [Real.exp_pos (-(ξ * (κ * p)))]
  have hexp : 1 ≤ Real.exp (-(κ * ξ ^ 2 * p / 2)) * Real.exp (ξ * (κ * p)) := by
    rw [← Real.exp_add]
    apply Real.one_le_exp
    have e : -(κ * ξ ^ 2 * p / 2) + ξ * (κ * p) = κ * p * (ξ * (1 - ξ / 2)) := by ring
    rw [e]
    exact mul_nonneg (mul_nonneg hκ hp) (mul_nonneg hξ0 (by linarith))
  calc (1 : ℝ) / 2 ≤ Real.exp (-(κ * ξ ^ 2 * p / 2)) * Real.exp (ξ * (κ * p)) / 2 := by linarith
    _ = Real.exp (-(κ * ξ ^ 2 * p / 2)) * (Real.exp (ξ * (κ * p)) / 2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hcosh (Real.exp_pos _).le

/-- For every `A` and `b > 0` there is a two-site region along the first axis on which the
density-one correlation exceeds `A (|x − y|₁ + 1)^{−b}`. -/
theorem densityOne_exceeds_powerLaw {κ ξ A b : ℝ} (hκ : 0 ≤ κ) (hξ0 : 0 ≤ ξ) (hξ1 : ξ ≤ 1)
    (hb : 0 < b) :
    ∃ r : ℕ, 1 ≤ r ∧ A * ((r : ℝ) + 1) ^ (-b) <
      regionConditionLambdaFracCorrInternal (pairRegionInternal (0, 0) ((r : ℤ), 0)) κ
        densityOneLawInternal ξ (0, 0) ((r : ℤ), 0) := by
  have hT : Tendsto (fun r : ℕ => A * ((r : ℝ) + 1) ^ (-b)) atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop hb).comp
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
    simpa using h.const_mul A
  obtain ⟨r, hr, hr1⟩ :=
    ((hT.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))).and
      (eventually_ge_atTop 1)).exists
  refine ⟨r, hr1, lt_of_lt_of_le hr (densityOneCorr_pair_ge ?_ hκ hξ0 hξ1)⟩
  intro h
  have := congrArg Prod.fst h
  simp only at this
  omega

/-- **Positive vacancy weight is necessary**: the general full-range Theorem B
(`coulombB_conditionLambda_free_fullRange_general`) with the vacancy bound `ν ≤ λ(0)`, `ν > 0`,
removed (laws only nonnegative and even, with the printed growth bound) is false. The density-one
law, with `C = 1`, `α = ε = 0`, violates it at every `κ`. -/
theorem not_coulombB_conditionLambda_free_fullRange_zeroVacancy :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ C α ε : ℝ, 0 ≤ C → 0 ≤ α → ε < 1 / 16 →
      ∀ η : ℝ, 0 < η →
        ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, κ₀ < κ → ∀ lam : ℤ → ℝ,
          ConditionLambdaInternal C α ε κ lam → (∀ n, 0 ≤ lam n) →
          ∀ (Λ : Finset (ℤ × ℤ)) (ξ : ℝ) (x y : ℤ × ℤ),
            x ∈ Λ → y ∈ Λ → x ≠ y → 0 < ξ → ξ < 1 → η ≤ dipoleGap ξ →
            0 ≤ regionConditionLambdaFracCorrInternal Λ κ lam ξ x y ∧
              regionConditionLambdaFracCorrInternal Λ κ lam ξ x y ≤
                2 * Real.exp (1 / (64 * (1 / 16 - max ε 0)) * κ) *
                  ((((y.1 - x.1).natAbs + (y.2 - x.2).natAbs : ℕ) + 1 : ℝ) ^
                    (-(c * (1 / 16 - max ε 0) * η ^ 2 * κ))) := by
  rintro ⟨c, hc, h⟩
  obtain ⟨κ₀, hκ₀, hF⟩ := h 1 0 0 zero_le_one le_rfl (by norm_num) (1 / 2) (by norm_num)
  have hκ : 0 ≤ κ₀ + 1 := by linarith
  have hb : 0 < c * (1 / 16 - max 0 0) * (1 / 2) ^ 2 * (κ₀ + 1) := by
    norm_num
    positivity
  obtain ⟨r, hr1, hr⟩ := densityOne_exceeds_powerLaw (ξ := 1 / 2)
    (A := 2 * Real.exp (1 / (64 * (1 / 16 - max 0 0)) * (κ₀ + 1))) hκ (by norm_num)
    (by norm_num) hb
  have hxy : ((0 : ℤ), (0 : ℤ)) ≠ ((r : ℤ), 0) := by
    intro h
    have := congrArg Prod.fst h
    simp only at this
    omega
  have hgap : (1 / 2 : ℝ) ≤ dipoleGap (1 / 2) := by
    unfold dipoleGap
    norm_num
  have hB := (hF (κ₀ + 1) (by linarith) densityOneLawInternal
    (densityOneLaw_conditionLambda (κ₀ + 1)) densityOneLaw_nonneg
    (pairRegionInternal (0, 0) ((r : ℤ), 0)) (1 / 2) (0, 0) ((r : ℤ), 0) (by simp) (by simp) hxy
    (by norm_num) (by norm_num) hgap).2
  have hd : (((((r : ℤ), (0 : ℤ)).1 - ((0 : ℤ), (0 : ℤ)).1).natAbs +
      ((((r : ℤ), (0 : ℤ)).2 - ((0 : ℤ), (0 : ℤ)).2)).natAbs : ℕ) : ℝ) = r := by
    simp
  rw [hd] at hB
  linarith

end FroehlichSpencer.BKT.Coulomb

end
