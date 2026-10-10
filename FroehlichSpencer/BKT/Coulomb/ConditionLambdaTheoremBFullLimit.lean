/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Coulomb.ConditionLambdaTheoremBFull
public import FroehlichSpencer.BKT.Coulomb.ConditionLambdaTheoremBLimit
import Mathlib.Tactic

/-!
# FS81 Theorem B for Condition-λ gases in the whole range `ε < 1/16`

FS81 Theorem B (J p. 532, (1.25)) for general Condition-λ gases (§5.2), free boundary condition,
in the printed range `ε < 1/16` of Condition λ b). Write `δ = 1/16 − max(ε, 0)`.

* **`coulombB_conditionLambda_free_fullRange`**: there is `c > 0` such that for all growth data
  `(C, α, ε)` with `ε < 1/16` and every gap `η > 0` there is `κ₀`. For `κ > κ₀`, every physical
  law satisfying Condition λ, every finite region and every site pair:
  `0 ≤ G_ξ(x, y) ≤ 2 e^{κ/(64δ)} (|x − y|₁ + 1)^{−c δ η² κ}`.
  - The constant `2 e^{κ/(64δ)}` depends on `κ` (FS81's `const`).
  - It cannot be made uniform in `κ` when `ε` is large compared with `η²`
    (`ConditionLambdaTheoremBObstruction`).
* `coulombB_conditionLambda_thermodynamicLimit_fullRange`: the same bound for every thermodynamic
  limit point.
* `coulombB_conditionLambda_free_fullRange_far`: beyond a distance `R(C, α, ε, η)` independent of
  `κ`, the bound holds with prefactor `2` and exponent `c δ η² κ/2`.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Coulomb

open MeasureTheory Filter Topology FroehlichSpencer.BKT.Generic.Marked

section TheoremB

/-- **FS81 Theorem B for Condition-λ gases in the whole range `ε < 1/16`, free boundary
condition.** With `δ = 1/16 − max(ε, 0)`, for fixed growth data `(C, α, ε)` and gap `η` there is a
threshold `κ₀` such that for every physical law satisfying them, finite region and site pair,
`0 ≤ G_ξ(x, y) ≤ 2 e^{κ/(64δ)} (|x − y|₁ + 1)^{−c δ η² κ}`. The constant `2 e^{κ/(64δ)}` depends
on `κ`, as FS81's `const` in (1.25) may; it cannot be taken uniform in `κ` when `ε` is large
compared with `η²` (`ConditionLambdaTheoremBObstruction`). -/
theorem coulombB_conditionLambda_free_fullRange :
    ∃ c : ℝ, 0 < c ∧ ∀ C α ε : ℝ, 0 ≤ C → 0 ≤ α → ε < 1 / 16 →
      ∀ η : ℝ, 0 < η →
        ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, κ₀ < κ → ∀ lam : ℤ → ℝ,
          ConditionLambdaInternal C α ε κ lam → PhysicalWeightInternal lam →
          ∀ (Λ : Finset (ℤ × ℤ)) (ξ : ℝ) (x y : ℤ × ℤ),
            x ∈ Λ → y ∈ Λ → x ≠ y → 0 < ξ → ξ < 1 → η ≤ dipoleGap ξ →
            0 ≤ regionConditionLambdaFracCorrInternal Λ κ lam ξ x y ∧
              regionConditionLambdaFracCorrInternal Λ κ lam ξ x y ≤
                2 * Real.exp (1 / (64 * (1 / 16 - max ε 0)) * κ) *
                  ((((y.1 - x.1).natAbs + (y.2 - x.2).natAbs : ℕ) + 1 : ℝ) ^
                    (-(c * (1 / 16 - max ε 0) * η ^ 2 * κ))) := by
  obtain ⟨cB, hcB, hSquare⟩ := markedConditionLambdaSquareBound_split_exists
  let c := 8 * cB / Real.log 2
  have hc : 0 < c := div_pos (by positivity) (Real.log_pos (by norm_num))
  refine ⟨c, hc, fun C α ε hC hα hε η hη => ?_⟩
  obtain ⟨κB, hκB, hSquare⟩ := hSquare C α ε hC hα hε η hη
  obtain ⟨κA, hκA, hFree⟩ := free_conditionLambda_bound (1 / 2) (by norm_num) C α ε hε
  let κ₀ := max κB κA
  have hκ₀ : 0 < κ₀ := by dsimp [κ₀]; exact lt_of_lt_of_le hκA (le_max_right _ _)
  refine ⟨κ₀, hκ₀, fun κ hκκ₀ lam hlam hphys Λ ξ x y hx hy hxy hξ0 hξ1 hηξ => ?_⟩
  have hκB' : κB < κ := lt_of_le_of_lt (le_max_left _ _) hκκ₀
  have hκA' : κA < κ := lt_of_le_of_lt (le_max_right _ _) hκκ₀
  have hκ : 0 < κ := (hκ₀.trans hκκ₀)
  have hfree := hFree Λ κ hκA' lam hlam hphys.1
  have hgate : GateInternal
      (freePotentialOpInternal (Subtype.val : Λ → ℤ × ℤ)) κ (fun _ => lam) := hfree.2.1
  let pos : Λ → ℤ × ℤ := Subtype.val
  let ox : Λ := ⟨x, hx⟩
  let oy : Λ := ⟨y, hy⟩
  have hpos : Function.Injective pos := Subtype.val_injective
  have hox : ox ≠ oy := fun he => hxy (congrArg Subtype.val he)
  let B := 2 * Real.exp (1 / (64 * (1 / 16 - max ε 0)) * κ) *
    (((y.1 - x.1).natAbs + (y.2 - x.2).natAbs : ℕ) + 1 : ℝ) ^
      (-(c * (1 / 16 - max ε 0) * η ^ 2 * κ))
  have hCutBound : ∀ N, 0 ≤ freeConditionLambdaFracCorrCutoffInternal pos N κ lam ξ ox oy ∧
      freeConditionLambdaFracCorrCutoffInternal pos N κ lam ξ ox oy ≤ B := by
    intro N
    have hT := tendsto_torus_conditionLambdaFracCorrCutoff pos hpos κ hκ N lam hlam.1 hphys ξ
      ox oy (fun n => torusSiteMapInternal pos n ox)
    have hev : ∀ᶠ n in atTop,
        0 ≤ weightedGFFExpectation (squarePeriodic (torusSideInternal n))
            (squarePeriodic_connected _ (one_lt_torusSide n)) κ⁻¹ (inv_pos.2 hκ)
            (torusSiteMapInternal pos n ox)
            (torusCutoffWeightsInternal pos n N lam)
            (fun φ => Real.cos (ξ * (φ (torusSiteMapInternal pos n ox) -
              φ (torusSiteMapInternal pos n oy)))) ∧
          weightedGFFExpectation (squarePeriodic (torusSideInternal n))
            (squarePeriodic_connected _ (one_lt_torusSide n)) κ⁻¹ (inv_pos.2 hκ)
            (torusSiteMapInternal pos n ox)
            (torusCutoffWeightsInternal pos n N lam)
            (fun φ => Real.cos (ξ * (φ (torusSiteMapInternal pos n ox) -
              φ (torusSiteMapInternal pos n oy)))) ≤ B := by
      filter_upwards [eventually_injective_latticeToSquare pos hpos,
        eventually_latticeDistance_torus (pos ox) (pos oy)] with n hinj hdist
      let site := torusSiteMapInternal pos n
      let A := Finset.univ.image site
      have hne : site ox ≠ site oy := fun h => hox (hinj h)
      obtain ⟨hZ, hI⟩ := ((hSquare (torusSideInternal n) (one_lt_torusSide n)).2
        (even_torusSide n)) κ hκB' hκ lam hlam hphys.1 N A (site ox) (site ox) (site oy)
        hne ξ hξ0 hξ1 hηξ
      let G := squarePeriodic (torusSideInternal n)
      let hG := squarePeriodic_connected _ (one_lt_torusSide n)
      let root := site ox
      let weights : (Fin (torusSideInternal n) × Fin (torusSideInternal n)) → ℝ → ℝ :=
        fun j => sineGordonWeightInternal N (regionWeightInternal A lam j)
      let obs : ((Fin (torusSideInternal n) × Fin (torusSideInternal n)) → ℝ) → ℝ :=
        fun φ => Real.cos (ξ * (φ (site ox) - φ (site oy)))
      have hnorm := weightedGFFNormalizer_eq G hG κ⁻¹ (inv_pos.2 hκ) root weights
      have hcorrEq : weightedGFFExpectation G hG κ⁻¹ (inv_pos.2 hκ) root weights obs =
          (∫ φ, obs φ * ∏ j, weights j (φ j) ∂gffLaw G hG κ⁻¹ (inv_pos.2 hκ) root) /
            weightedGFFNormalizer G hG κ⁻¹ (inv_pos.2 hκ) root weights := by
        rw [weightedGFFExpectation_eq, ← hnorm]
      let f := dipoleRealInternal (site ox) (site oy)
      have hsum : ∀ φ : (Fin (torusSideInternal n) × Fin (torusSideInternal n) → ℝ),
          ∑ j, φ j * f j = φ (site ox) - φ (site oy) := by
        intro φ
        calc ∑ j, φ j * f j = ∑ j, f j * φ j := by
              exact Finset.sum_congr rfl fun j _ => mul_comm _ _
          _ = _ := sum_dipoleRealInternal_mul _ _ φ
      have hnum : 0 ≤ ∫ φ, obs φ * ∏ j, weights j (φ j)
          ∂gffLaw G hG κ⁻¹ (inv_pos.2 hκ) root := by
        have hbase := integral_cos_mul_prod_sineGordonWeight_nonneg G hG κ⁻¹
          (inv_pos.2 hκ) root N (fun j => regionWeightInternal A lam j)
          (fun j q => regionWeight_neg A hlam.1 j q)
          (fun j q => regionWeight_nonneg A hphys.2 j q) f (sum_dipoleRealInternal _ _) ξ
        simpa [obs, weights, hsum] using hbase
      have hdist' : latticeDistance .periodic (torusSideInternal n) (site ox) (site oy) =
          (y.1 - x.1).natAbs + (y.2 - x.2).natAbs := hdist
      have hdpos : (0 : ℝ) <
          ((y.1 - x.1).natAbs + (y.2 - x.2).natAbs : ℕ) + 1 := by positivity
      have hexp : Real.exp (-(cB * (8 * (1 / 16 - max ε 0)) * η ^ 2 * κ) * Real.logb 2
          (((y.1 - x.1).natAbs + (y.2 - x.2).natAbs : ℕ) + 1)) =
          (((y.1 - x.1).natAbs + (y.2 - x.2).natAbs : ℕ) + 1 : ℝ) ^
            (-(c * (1 / 16 - max ε 0) * η ^ 2 * κ)) := by
        rw [Real.rpow_def_of_pos hdpos, Real.logb]
        congr 1
        dsimp [c]
        ring
      have hI' := hI
      rw [hdist'] at hI'
      have hnumle : (∫ φ, obs φ * ∏ j, weights j (φ j)
          ∂gffLaw G hG κ⁻¹ (inv_pos.2 hκ) root) ≤
          B * weightedGFFNormalizer G hG κ⁻¹ (inv_pos.2 hκ) root weights := by
        calc _ ≤ |∫ φ, obs φ * ∏ j, weights j (φ j)
              ∂gffLaw G hG κ⁻¹ (inv_pos.2 hκ) root| := le_abs_self _
          _ ≤ 2 * Real.exp (1 / (64 * (1 / 16 - max ε 0)) * κ) *
                Real.exp (-(cB * (8 * (1 / 16 - max ε 0)) * η ^ 2 * κ) * Real.logb 2
                (((y.1 - x.1).natAbs + (y.2 - x.2).natAbs : ℕ) + 1)) *
                weightedGFFNormalizer G hG κ⁻¹ (inv_pos.2 hκ) root weights := by
                  simpa [obs, weights, A, site] using hI'
          _ = B * weightedGFFNormalizer G hG κ⁻¹ (inv_pos.2 hκ) root weights := by
                rw [hexp]
      have hcorr0 : 0 ≤ weightedGFFExpectation G hG κ⁻¹ (inv_pos.2 hκ) root weights obs := by
        rw [hcorrEq]
        exact div_nonneg hnum hZ.le
      have hcorrle : weightedGFFExpectation G hG κ⁻¹ (inv_pos.2 hκ) root weights obs ≤ B := by
        rw [hcorrEq]
        exact (div_le_iff₀ hZ).2 hnumle
      simpa [G, hG, root, weights, obs] using ⟨hcorr0, hcorrle⟩
    exact ⟨ge_of_tendsto hT (hev.mono fun n h => h.1),
      le_of_tendsto hT (hev.mono fun n h => h.2)⟩
  have hTfull := tendsto_freeConditionLambdaFracCorrCutoff pos κ lam hphys hgate ξ ox oy
  have hbound : 0 ≤ freeConditionLambdaFracCorrInternal pos κ lam ξ ox oy ∧
      freeConditionLambdaFracCorrInternal pos κ lam ξ ox oy ≤ B :=
    ⟨ge_of_tendsto hTfull (Eventually.of_forall fun N => (hCutBound N).1),
      le_of_tendsto hTfull (Eventually.of_forall fun N => (hCutBound N).2)⟩
  unfold regionConditionLambdaFracCorrInternal
  simpa [regionConditionLambdaFracCorrInternal, pos, ox, oy, hx, hy, B] using hbound

/-- **Every thermodynamic limit point** of free-boundary Condition-λ correlations in the whole range
`ε < 1/16` satisfies the same bound. The bound is uniform in the finite regions. -/
theorem coulombB_conditionLambda_thermodynamicLimit_fullRange :
    ∃ c : ℝ, 0 < c ∧ ∀ C α ε : ℝ, 0 ≤ C → 0 ≤ α → ε < 1 / 16 →
      ∀ η : ℝ, 0 < η →
        ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, κ₀ < κ → ∀ lam : ℤ → ℝ,
        ConditionLambdaInternal C α ε κ lam → PhysicalWeightInternal lam →
        ∀ ξ : ℝ, 0 < ξ → ξ < 1 → η ≤ dipoleGap ξ →
        ∀ x y : ℤ × ℤ, x ≠ y → ∀ Λs : ℕ → Finset (ℤ × ℤ),
          (∀ k, x ∈ Λs k ∧ y ∈ Λs k) →
          (∀ k, 0 ≤ regionConditionLambdaFracCorrInternal (Λs k) κ lam ξ x y ∧
            regionConditionLambdaFracCorrInternal (Λs k) κ lam ξ x y ≤
              2 * Real.exp (1 / (64 * (1 / 16 - max ε 0)) * κ) *
                (((y.1 - x.1).natAbs + (y.2 - x.2).natAbs : ℕ) + 1 : ℝ) ^
                  (-(c * (1 / 16 - max ε 0) * η ^ 2 * κ))) ∧
          (∃ ℓ : ℝ, ∃ φ : ℕ → ℕ, StrictMono φ ∧
            Tendsto (fun k => regionConditionLambdaFracCorrInternal (Λs (φ k)) κ lam ξ x y)
              atTop (𝓝 ℓ)) ∧
          ∀ ℓ : ℝ, MapClusterPt ℓ atTop
              (fun k => regionConditionLambdaFracCorrInternal (Λs k) κ lam ξ x y) →
            0 ≤ ℓ ∧ ℓ ≤
              2 * Real.exp (1 / (64 * (1 / 16 - max ε 0)) * κ) *
                (((y.1 - x.1).natAbs + (y.2 - x.2).natAbs : ℕ) + 1 : ℝ) ^
                  (-(c * (1 / 16 - max ε 0) * η ^ 2 * κ)) := by
  obtain ⟨c, hc, hfree⟩ := coulombB_conditionLambda_free_fullRange
  refine ⟨c, hc, fun C α ε hC hα hε η hη => ?_⟩
  obtain ⟨κ₀, hκ₀, hF⟩ := hfree C α ε hC hα hε η hη
  refine ⟨κ₀, hκ₀, fun κ hκκ₀ lam hlam hphys ξ hξ0 hξ1 hηξ x y hxy Λs hΛs => ?_⟩
  let B : ℝ := 2 * Real.exp (1 / (64 * (1 / 16 - max ε 0)) * κ) *
    (((y.1 - x.1).natAbs + (y.2 - x.2).natAbs : ℕ) + 1 : ℝ) ^
      (-(c * (1 / 16 - max ε 0) * η ^ 2 * κ))
  have hk : ∀ k, 0 ≤ regionConditionLambdaFracCorrInternal (Λs k) κ lam ξ x y ∧
      regionConditionLambdaFracCorrInternal (Λs k) κ lam ξ x y ≤ B := by
    intro k
    exact hF κ hκκ₀ lam hlam hphys (Λs k) ξ x y (hΛs k).1 (hΛs k).2 hxy hξ0 hξ1 hηξ
  have hmem : ∀ k, regionConditionLambdaFracCorrInternal (Λs k) κ lam ξ x y ∈ Set.Icc 0 B :=
    fun k => hk k
  refine ⟨hk, ?_, fun ℓ hℓ =>
    isClosed_Icc.mem_of_mapClusterPt hℓ (Eventually.of_forall hmem)⟩
  obtain ⟨ℓ, -, φ, hφ, hT⟩ := tendsto_subseq_of_bounded (Metric.isBounded_Icc 0 B) hmem
  exact ⟨ℓ, φ, hφ, hT⟩

/-- The prefactor `e^{Pκ}` is absorbed at distances `log(r + 1) ≥ 2P/p`, independently of `κ > 0`:
`e^{Pκ} (r + 1)^{−pκ} ≤ (r + 1)^{−pκ/2}`. -/
theorem exp_mul_rpow_le_rpow_half {P p κ r : ℝ} (hp : 0 < p) (hκ : 0 < κ) (hr : 0 ≤ r)
    (hR : Real.exp (2 * P / p) ≤ r + 1) :
    Real.exp (P * κ) * (r + 1) ^ (-(p * κ)) ≤ (r + 1) ^ (-(p / 2 * κ)) := by
  have hr1 : 0 < r + 1 := by linarith
  have hlog : 2 * P / p ≤ Real.log (r + 1) := by
    rw [← Real.exp_le_exp, Real.exp_log hr1]; exact hR
  have hlog' : 2 * P ≤ p * Real.log (r + 1) := by
    rw [div_le_iff₀ hp] at hlog; linarith
  rw [Real.rpow_def_of_pos hr1, Real.rpow_def_of_pos hr1, ← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  nlinarith [mul_le_mul_of_nonneg_left hlog' hκ.le]

/-- **The κ-uniform prefactor away from the diagonal**: in the whole range `ε < 1/16`, beyond a
distance `R(C, α, ε, η)` independent of `κ`, the Condition-λ correlation obeys
`G_ξ(x, y) ≤ 2 (|x − y|₁ + 1)^{−(c δ η²/2) κ}`, `δ = 1/16 − max(ε, 0)`. -/
theorem coulombB_conditionLambda_free_fullRange_far :
    ∃ c : ℝ, 0 < c ∧ ∀ C α ε : ℝ, 0 ≤ C → 0 ≤ α → ε < 1 / 16 →
      ∀ η : ℝ, 0 < η →
        ∃ κ₀ R : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, κ₀ < κ → ∀ lam : ℤ → ℝ,
          ConditionLambdaInternal C α ε κ lam → PhysicalWeightInternal lam →
          ∀ (Λ : Finset (ℤ × ℤ)) (ξ : ℝ) (x y : ℤ × ℤ),
            x ∈ Λ → y ∈ Λ → x ≠ y → 0 < ξ → ξ < 1 → η ≤ dipoleGap ξ →
            R ≤ (((y.1 - x.1).natAbs + (y.2 - x.2).natAbs : ℕ) : ℝ) →
            0 ≤ regionConditionLambdaFracCorrInternal Λ κ lam ξ x y ∧
              regionConditionLambdaFracCorrInternal Λ κ lam ξ x y ≤
                2 * ((((y.1 - x.1).natAbs + (y.2 - x.2).natAbs : ℕ) + 1 : ℝ) ^
                  (-(c * (1 / 16 - max ε 0) * η ^ 2 / 2 * κ))) := by
  obtain ⟨c, hc, hfree⟩ := coulombB_conditionLambda_free_fullRange
  refine ⟨c, hc, fun C α ε hC hα hε η hη => ?_⟩
  obtain ⟨κ₀, hκ₀, hF⟩ := hfree C α ε hC hα hε η hη
  have hδ : 0 < 1 / 16 - max ε 0 := by
    have := max_lt hε (by norm_num : (0 : ℝ) < 1 / 16)
    linarith
  have hp : 0 < c * (1 / 16 - max ε 0) * η ^ 2 := by positivity
  refine ⟨κ₀, Real.exp (2 * (1 / (64 * (1 / 16 - max ε 0))) /
    (c * (1 / 16 - max ε 0) * η ^ 2)), hκ₀, fun κ hκκ₀ lam hlam hphys Λ ξ x y hx hy hxy hξ0 hξ1
      hηξ hR => ?_⟩
  have hκ : 0 < κ := hκ₀.trans hκκ₀
  obtain ⟨h0, hle⟩ := hF κ hκκ₀ lam hlam hphys Λ ξ x y hx hy hxy hξ0 hξ1 hηξ
  refine ⟨h0, hle.trans ?_⟩
  set r : ℝ := (((y.1 - x.1).natAbs + (y.2 - x.2).natAbs : ℕ) : ℝ) with hr
  have hr0 : 0 ≤ r := Nat.cast_nonneg _
  have hR' : Real.exp (2 * (1 / (64 * (1 / 16 - max ε 0))) /
      (c * (1 / 16 - max ε 0) * η ^ 2)) ≤ r + 1 := by linarith
  have key := exp_mul_rpow_le_rpow_half hp hκ hr0 hR'
  have e1 : -(c * (1 / 16 - max ε 0) * η ^ 2 * κ) = -((c * (1 / 16 - max ε 0) * η ^ 2) * κ) := by
    ring
  have e2 : -(c * (1 / 16 - max ε 0) * η ^ 2 / 2 * κ) =
      -((c * (1 / 16 - max ε 0) * η ^ 2) / 2 * κ) := by ring
  rw [e1, e2, mul_assoc]
  exact mul_le_mul_of_nonneg_left key (by norm_num)

end TheoremB

end FroehlichSpencer.BKT.Coulomb

end
