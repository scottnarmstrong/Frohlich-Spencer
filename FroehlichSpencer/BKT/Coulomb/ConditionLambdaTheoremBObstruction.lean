/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Coulomb.ConditionLambdaTheoremBLimit
import Mathlib.Tactic

/-!
# Theorem B cannot have a `κ`-uniform constant in the whole range `ε < 1/16`

The unit-charge law `λ(0) = 1`, `λ(±1) = e^{εκ}` satisfies Condition λ with `(C, α) = (1, 0)`.
It is the hard-core gas with activity `z = e^{εκ}`.

At the two adjacent sites `{(0,0), (1,0)}` the charge formula has the closed form
`G_ξ = e^{−κξ²p/2} (1 + 2u cosh(ξκp)) / (1 + 2u)`, where:
* `u = e^{2εκ − κp/2}`;
* `p = 2E(δ_o − δ_x) ∈ [1/4, 1]` (`regionCorr_adjacent_eq`, `adjacentDipoleQuad_ge`,
  `adjacentDipoleQuad_le`).

The configuration with a unit charge screening the fractional one has energy `η²p/2` and activity
`e^{2εκ}`, so:
* `regionCorr_adjacent_ge`: `G_ξ ≥ e^{κ r}/3` with `r = min(2ε − (1 − ξ)²/2, ξ(1 − ξ/2)/4)`;
* **`regionCorr_adjacent_tendsto_atTop`**: if `(1 − ξ)² < 4ε`, then `G_ξ → ∞` as `κ → ∞`;
* `conditionLambda_no_uniform_bound`: for `0 < η ≤ 1/2` with `η² < 4ε`, no bound `G_ξ ≤ M` holds
  for all large `κ`;
* **`not_coulombB_conditionLambda_free_uniform`**: the marked-cluster estimate's statement `coulombB_conditionLambda_free`
  with its restriction `ε < η²/128` removed is false.

So a `κ`-uniform prefactor needs `ε ≲ η²`. Between `η²/128` (the marked-cluster estimate) and `η²/4` (here) the sharp
constant is open. In the whole range the constant must grow with `κ`, as in
`coulombB_conditionLambda_free_fullRange`. FS81's Theorem B (1.25) allows this, since its `const`
may depend on `β`.

The printed intermediate bound (5.33), `z(β, ξϱ₀ + ϱ^𝒩) ≤ e^{−(cη²β − b) ln d}`, with `b` independent
of `β`, would give `G_ξ(0, x) < 2` at `|x| = 1` via (5.35). That bound is false in this regime, already
for the hard-core gas with `z = e^{εβ}`, `ε < 1/16` (the proviso of (5.27), §5.1).
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Coulomb

open Filter Topology FroehlichSpencer.BKT.Generic.Marked

/-! ### The unit-charge law -/

/-- The unit-charge law `λ(0) = 1`, `λ(±1) = e^{εκ}`, `λ(n) = 0` for `|n| ≥ 2`. -/
def unitChargeLawInternal (ε κ : ℝ) : ℤ → ℝ :=
  fun n => if n = 0 then 1 else if n.natAbs = 1 then Real.exp (ε * κ) else 0

theorem unitChargeLaw_conditionLambda (ε κ : ℝ) :
    ConditionLambdaInternal 1 0 ε κ (unitChargeLawInternal ε κ) := by
  refine ⟨fun n => by simp [unitChargeLawInternal], fun n => ?_⟩
  unfold unitChargeLawInternal
  split_ifs with h0 h1
  · subst h0; simp
  · have hn : (n : ℝ) ^ 2 = 1 := by
      rcases Int.natAbs_eq n with h | h <;> rw [h, h1] <;> norm_num
    rw [hn, abs_of_pos (Real.exp_pos _)]
    simp
  · simp only [abs_zero, one_mul]
    positivity

theorem unitChargeLaw_physical (ε κ : ℝ) : PhysicalWeightInternal (unitChargeLawInternal ε κ) := by
  refine ⟨by simp [unitChargeLawInternal], fun n => ?_⟩
  unfold unitChargeLawInternal
  split_ifs <;> positivity

theorem unitChargeLaw_eq_zero {ε κ : ℝ} {n : ℤ} (hn : n ∉ ({-1, 0, 1} : Finset ℤ)) :
    unitChargeLawInternal ε κ n = 0 := by
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
  unfold unitChargeLawInternal
  have h1 : n.natAbs ≠ 1 := by omega
  simp only [hn.2.1, h1, ↓reduceIte]

/-! ### Two-site gases -/

section TwoSites

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The multiples `n (δ_o − δ_x)` of the dipole. -/
def dipoleMultipleInternal (o x : V) (n : ℤ) : V → ℤ := fun v => n * dipoleMark o x v

omit [Fintype V] in
theorem dipoleMark_left {o x : V} (hox : o ≠ x) : dipoleMark o x o = 1 := by
  simp [dipoleMark, hox]

omit [Fintype V] in
theorem dipoleMark_right {o x : V} (hox : o ≠ x) : dipoleMark o x x = -1 := by
  simp [dipoleMark, hox.symm]

theorem univ_eq_pair {o x : V} (hV : ∀ v, v = o ∨ v = x) : (Finset.univ : Finset V) = {o, x} := by
  ext v
  simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
  exact hV v

omit [Fintype V] in
theorem dipoleMultiple_injective {o x : V} (hox : o ≠ x) :
    Function.Injective (dipoleMultipleInternal o x) := by
  intro n m h
  have := congrFun h o
  simpa [dipoleMultipleInternal, dipoleMark_left hox] using this

/-- On two sites every neutral configuration is a multiple of the dipole. -/
theorem eq_dipoleMultiple {o x : V} (hox : o ≠ x) (hV : ∀ v, v = o ∨ v = x) {q : V → ℤ}
    (hq : ∑ j, q j = 0) : q = dipoleMultipleInternal o x (q o) := by
  rw [univ_eq_pair hV, Finset.sum_pair hox] at hq
  funext v
  rcases hV v with rfl | rfl
  · simp [dipoleMultipleInternal, dipoleMark_left hox]
  · simp only [dipoleMultipleInternal, dipoleMark_right hox]
    omega

theorem chargeEnergy_dipoleMultiple (T : (V → ℝ) →ₗ[ℝ] V → ℝ) (o x : V) (n : ℤ) :
    chargeEnergyInternal T (dipoleMultipleInternal o x n) =
      (n : ℝ) ^ 2 * chargeEnergyInternal T (dipoleMark o x) := by
  unfold chargeEnergyInternal dipoleMultipleInternal
  have hf : (fun i => (((n * dipoleMark o x i : ℤ)) : ℝ)) =
      (n : ℝ) • fun i => ((dipoleMark o x i : ℤ) : ℝ) := by
    funext i
    simp
  rw [hf, map_smul]
  simp only [Pi.smul_apply, smul_eq_mul, Int.cast_mul]
  rw [mul_div_assoc', Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- The gas weight of `n (δ_o − δ_x)`: `λ(n) λ(−n) e^{−κ n² E(δ_o − δ_x)}`. -/
theorem gasWeight_dipoleMultiple (T : (V → ℝ) →ₗ[ℝ] V → ℝ) {o x : V} (hox : o ≠ x)
    (hV : ∀ v, v = o ∨ v = x) (κ : ℝ) (lam : ℤ → ℝ) (n : ℤ) :
    gasWeightInternal T κ (fun _ => lam) (dipoleMultipleInternal o x n) =
      lam n * lam (-n) *
        Real.exp (-κ * ((n : ℝ) ^ 2 * chargeEnergyInternal T (dipoleMark o x))) := by
  unfold gasWeightInternal
  have hneutral : ∑ j, dipoleMultipleInternal o x n j = 0 := by
    unfold dipoleMultipleInternal
    rw [← Finset.mul_sum, sum_univ_dipoleMark, mul_zero]
  simp only [hneutral, ↓reduceIte]
  rw [chargeEnergy_dipoleMultiple, univ_eq_pair hV, Finset.prod_pair hox]
  simp [dipoleMultipleInternal, dipoleMark_left hox, dipoleMark_right hox]

/-- **The two-site gas sum.** For a law vanishing on `|n| ≥ 2`, the full gas sum of `w · F` over
neutral configurations of two sites is the sum over the dipole multiples `n ∈ {−1, 0, 1}`. -/
theorem tsum_gasWeight_twoSites (T : (V → ℝ) →ₗ[ℝ] V → ℝ) {o x : V} (hox : o ≠ x)
    (hV : ∀ v, v = o ∨ v = x) (κ : ℝ) (lam : ℤ → ℝ)
    (hlam : ∀ n ∉ ({-1, 0, 1} : Finset ℤ), lam n = 0) (F : (V → ℤ) → ℝ) :
    ∑' q : V → ℤ, gasWeightInternal T κ (fun _ => lam) q * F q =
      ∑ n ∈ ({-1, 0, 1} : Finset ℤ), lam n * lam (-n) *
        Real.exp (-κ * ((n : ℝ) ^ 2 * chargeEnergyInternal T (dipoleMark o x))) *
          F (dipoleMultipleInternal o x n) := by
  rw [← (dipoleMultiple_injective hox).tsum_eq]
  · rw [tsum_eq_sum (s := ({-1, 0, 1} : Finset ℤ))]
    · exact Finset.sum_congr rfl fun n _ => by rw [gasWeight_dipoleMultiple T hox hV]
    · intro n hn
      rw [gasWeight_dipoleMultiple T hox hV, hlam n hn]
      ring
  · intro q hq
    have hw : gasWeightInternal T κ (fun _ => lam) q ≠ 0 := by
      intro h0
      exact hq (by simp [h0])
    have hneutral : ∑ j, q j = 0 := by
      by_contra hne
      exact hw (by simp [gasWeightInternal, hne])
    exact ⟨q o, (eq_dipoleMultiple hox hV hneutral).symm⟩

end TwoSites

/-! ### The closed form at two adjacent sites -/

section Adjacent

/-- A lower bound for the closed form: with `u = e^{2εκ − κp/2}` and `κ ≥ 0`,
`e^{−κξ²p/2} (1 + 2u cosh(ξκp)) / (1 + 2u) ≥ e^{κ r}/3`, where
`r = min(2ε − p(1 − ξ)²/2, pξ(1 − ξ/2))`. -/
theorem twoSite_closedForm_ge {κ ξ p ε : ℝ} (hκ : 0 ≤ κ) :
    Real.exp (κ * min (2 * ε - p * (1 - ξ) ^ 2 / 2) (p * ξ * (1 - ξ / 2))) / 3 ≤
      Real.exp (-(κ * ξ ^ 2 * p / 2)) *
        ((1 + 2 * Real.exp (2 * ε * κ - κ * p / 2) * Real.cosh (ξ * (κ * p))) /
          (1 + 2 * Real.exp (2 * ε * κ - κ * p / 2))) := by
  set u := Real.exp (2 * ε * κ - κ * p / 2) with hu
  have hu0 : 0 < u := Real.exp_pos _
  have hcosh : Real.exp (ξ * (κ * p)) / 2 ≤ Real.cosh (ξ * (κ * p)) := by
    rw [Real.cosh_eq]
    have := Real.exp_pos (-(ξ * (κ * p)))
    linarith
  have hnum : u * Real.exp (ξ * (κ * p)) ≤ 1 + 2 * u * Real.cosh (ξ * (κ * p)) := by
    have := mul_le_mul_of_nonneg_left hcosh (by positivity : (0 : ℝ) ≤ 2 * u)
    linarith
  have hden : 0 < 1 + 2 * u := by positivity
  have hfrac : u * Real.exp (ξ * (κ * p)) / (1 + 2 * u) ≤
      (1 + 2 * u * Real.cosh (ξ * (κ * p))) / (1 + 2 * u) :=
    div_le_div_of_nonneg_right hnum hden.le
  refine le_trans ?_ (mul_le_mul_of_nonneg_left hfrac (Real.exp_pos _).le)
  rcases le_total u 1 with hu1 | hu1
  · -- dilute: `1 + 2u ≤ 3`
    have h1 : Real.exp (-(κ * ξ ^ 2 * p / 2)) * (u * Real.exp (ξ * (κ * p))) / 3 ≤
        Real.exp (-(κ * ξ ^ 2 * p / 2)) * (u * Real.exp (ξ * (κ * p)) / (1 + 2 * u)) := by
      rw [mul_div_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
      exact div_le_div_of_nonneg_left (by positivity) hden (by linarith)
    refine le_trans ?_ h1
    rw [hu, ← Real.exp_add, ← Real.exp_add]
    refine div_le_div_of_nonneg_right (Real.exp_le_exp.2 ?_) (by norm_num)
    have := mul_le_mul_of_nonneg_left (min_le_left (2 * ε - p * (1 - ξ) ^ 2 / 2)
      (p * ξ * (1 - ξ / 2))) hκ
    nlinarith
  · -- dense: `1 + 2u ≤ 3u`
    have h1 : Real.exp (-(κ * ξ ^ 2 * p / 2)) * Real.exp (ξ * (κ * p)) / 3 ≤
        Real.exp (-(κ * ξ ^ 2 * p / 2)) * (u * Real.exp (ξ * (κ * p)) / (1 + 2 * u)) := by
      rw [mul_div_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
      rw [div_le_div_iff₀ (by norm_num) hden]
      have := Real.exp_pos (ξ * (κ * p))
      nlinarith
    refine le_trans ?_ h1
    rw [← Real.exp_add]
    refine div_le_div_of_nonneg_right (Real.exp_le_exp.2 ?_) (by norm_num)
    have := mul_le_mul_of_nonneg_left (min_le_right (2 * ε - p * (1 - ξ) ^ 2 / 2)
      (p * ξ * (1 - ξ / 2))) hκ
    nlinarith

/-- The free energy and the pairing of the dipole on any finite set of sites. -/
theorem chargeEnergy_dipoleMark_eq {V : Type*} [Fintype V] [DecidableEq V] (pos : V → ℤ × ℤ)
    (o x : V) :
    chargeEnergyInternal (freePotentialOpInternal pos) (dipoleMark o x) =
      freeQuadInternal pos (dipoleRealInternal o x) / 2 := rfl

theorem freeChargePairing_dipoleMultiple {V : Type*} [Fintype V] [DecidableEq V]
    (pos : V → ℤ × ℤ) (o x : V) (n : ℤ) :
    freeChargePairingInternal pos (dipoleRealInternal o x) (dipoleMultipleInternal o x n) =
      n * freeQuadInternal pos (dipoleRealInternal o x) := by
  unfold freeChargePairingInternal dipoleMultipleInternal freeQuadInternal
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp only [dipoleRealInternal, Int.cast_mul]
  ring

/-- The two adjacent sites `{(0,0), (1,0)}`. -/
abbrev adjacentPairInternal : Finset (ℤ × ℤ) := {(0, 0), (1, 0)}

/-- The left site of `adjacentPairInternal`. -/
abbrev adjacentLeftInternal : adjacentPairInternal := ⟨(0, 0), by simp⟩

/-- The right site of `adjacentPairInternal`. -/
abbrev adjacentRightInternal : adjacentPairInternal := ⟨(1, 0), by simp⟩

theorem adjacentLeft_ne_right : adjacentLeftInternal ≠ adjacentRightInternal := by
  intro h
  have := congrArg Subtype.val h
  simp at this

theorem adjacentPair_cases (v : adjacentPairInternal) :
    v = adjacentLeftInternal ∨ v = adjacentRightInternal := by
  obtain ⟨v, hv⟩ := v
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- `p = ⟨δ_o − δ_x, C(δ_o − δ_x)⟩` for the adjacent dipole, `p = 2 E(δ_o − δ_x)`. -/
def adjacentDipoleQuadInternal : ℝ :=
  freeQuadInternal (fun v : adjacentPairInternal => (v : ℤ × ℤ))
    (dipoleRealInternal adjacentLeftInternal adjacentRightInternal)

theorem adjacentDipoleQuad_ge : 1 / 4 ≤ adjacentDipoleQuadInternal := by
  have h := free_chargeEnergy_ge (fun v : adjacentPairInternal => (v : ℤ × ℤ))
    Subtype.val_injective (dipoleMark adjacentLeftInternal adjacentRightInternal)
    (sum_univ_dipoleMark _ _)
  rw [chargeEnergy_dipoleMark_eq, univ_eq_pair adjacentPair_cases,
    Finset.sum_pair adjacentLeft_ne_right, dipoleMark_left adjacentLeft_ne_right,
    dipoleMark_right adjacentLeft_ne_right] at h
  unfold adjacentDipoleQuadInternal
  norm_num at h
  linarith

theorem adjacentDipoleQuad_le : adjacentDipoleQuadInternal ≤ 1 := by
  have hlap := potentialKernel_laplacian 0
  have h01 := potentialKernel_nonneg (0, 1)
  have h01' := potentialKernel_nonneg (0, -1)
  have h0 := potentialKernel_zero
  have hq : adjacentDipoleQuadInternal =
      potentialKernelInternal (-1, 0) + potentialKernelInternal (1, 0) -
        2 * potentialKernelInternal 0 := by
    unfold adjacentDipoleQuadInternal freeQuadInternal freePotentialOpInternal
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    rw [univ_eq_pair adjacentPair_cases, Finset.sum_pair adjacentLeft_ne_right]
    simp only [Finset.sum_pair adjacentLeft_ne_right, dipoleRealInternal,
      dipoleMark_left adjacentLeft_ne_right, dipoleMark_right adjacentLeft_ne_right]
    norm_num
    ring
  rw [hq]
  simp only [zero_add, zero_sub, ↓reduceIte] at hlap
  norm_num at hlap
  linarith

/-- **The closed form at two adjacent sites.** With `p = adjacentDipoleQuadInternal` and
`u = e^{2εκ − κp/2}`, the unit-charge correlation is
`G = e^{−κξ²p/2} (1 + 2u cosh(ξκp)) / (1 + 2u)`. -/
theorem regionCorr_adjacent_eq (κ ε ξ : ℝ) :
    regionConditionLambdaFracCorrInternal adjacentPairInternal κ (unitChargeLawInternal ε κ) ξ
        (0, 0) (1, 0) =
      Real.exp (-(κ * ξ ^ 2 * adjacentDipoleQuadInternal / 2)) *
        ((1 + 2 * Real.exp (2 * ε * κ - κ * adjacentDipoleQuadInternal / 2) *
            Real.cosh (ξ * (κ * adjacentDipoleQuadInternal))) /
          (1 + 2 * Real.exp (2 * ε * κ - κ * adjacentDipoleQuadInternal / 2))) := by
  set p := adjacentDipoleQuadInternal with hp
  have hmem : ((0, 0) : ℤ × ℤ) ∈ adjacentPairInternal ∧ ((1, 0) : ℤ × ℤ) ∈ adjacentPairInternal :=
    ⟨by simp, by simp⟩
  unfold regionConditionLambdaFracCorrInternal
  simp only [hmem, and_self, ↓reduceDIte]
  unfold freeConditionLambdaFracCorrInternal fullGasExpectationInternal fullGasPartitionInternal
  set T := freePotentialOpInternal (fun v : adjacentPairInternal => (v : ℤ × ℤ)) with hT
  have hlam : ∀ n ∉ ({-1, 0, 1} : Finset ℤ), unitChargeLawInternal ε κ n = 0 :=
    fun n hn => unitChargeLaw_eq_zero hn
  have hZ := tsum_gasWeight_twoSites T adjacentLeft_ne_right adjacentPair_cases κ
    (unitChargeLawInternal ε κ) hlam (fun _ => 1)
  have hN := tsum_gasWeight_twoSites T adjacentLeft_ne_right adjacentPair_cases κ
    (unitChargeLawInternal ε κ) hlam (fun q => Real.cosh (ξ * (κ * freeChargePairingInternal
      (fun v : adjacentPairInternal => (v : ℤ × ℤ))
      (dipoleRealInternal adjacentLeftInternal adjacentRightInternal) q)))
  simp only [mul_one] at hZ
  rw [hZ, hN]
  have hE : chargeEnergyInternal T (dipoleMark adjacentLeftInternal adjacentRightInternal) =
      p / 2 := by
    rw [hT, chargeEnergy_dipoleMark_eq]
    rfl
  simp only [freeChargePairing_dipoleMultiple, hE]
  have hl0 : unitChargeLawInternal ε κ 0 = 1 := by simp [unitChargeLawInternal]
  have hl1 : unitChargeLawInternal ε κ 1 = Real.exp (ε * κ) := by simp [unitChargeLawInternal]
  have hlm1 : unitChargeLawInternal ε κ (-1) = Real.exp (ε * κ) := by
    simp [unitChargeLawInternal]
  have hw : Real.exp (ε * κ) * Real.exp (ε * κ) * Real.exp (-κ * (1 * (p / 2))) =
      Real.exp (2 * ε * κ - κ * p / 2) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have e1 : freeQuadInternal (fun v : adjacentPairInternal => (v : ℤ × ℤ))
      (dipoleRealInternal adjacentLeftInternal adjacentRightInternal) = p := rfl
  have hDen : ∑ n ∈ ({-1, 0, 1} : Finset ℤ), unitChargeLawInternal ε κ n *
      unitChargeLawInternal ε κ (-n) * Real.exp (-κ * ((n : ℝ) ^ 2 * (p / 2))) =
      1 + 2 * Real.exp (2 * ε * κ - κ * p / 2) := by
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
    simp only [neg_neg, neg_zero, hl0, hl1, hlm1, Int.cast_neg, Int.cast_one, Int.cast_zero,
      neg_one_sq, one_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul,
      mul_zero, Real.exp_zero, mul_one]
    rw [hw]
    ring
  have hNum : ∑ n ∈ ({-1, 0, 1} : Finset ℤ), unitChargeLawInternal ε κ n *
      unitChargeLawInternal ε κ (-n) * Real.exp (-κ * ((n : ℝ) ^ 2 * (p / 2))) *
        Real.cosh (ξ * (κ * ((n : ℝ) * p))) =
      1 + 2 * Real.exp (2 * ε * κ - κ * p / 2) * Real.cosh (ξ * (κ * p)) := by
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
    simp only [neg_neg, neg_zero, hl0, hl1, hlm1, Int.cast_neg, Int.cast_one, Int.cast_zero,
      neg_one_sq, one_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul,
      mul_zero, Real.exp_zero, mul_one, Real.cosh_zero, neg_mul, one_mul, mul_neg,
      Real.cosh_neg]
    have hw' : Real.exp (ε * κ) * Real.exp (ε * κ) * Real.exp (-(κ * (p / 2))) =
        Real.exp (2 * ε * κ - κ * p / 2) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    rw [hw']
    ring
  rw [e1, hNum, hDen]

/-- **The adjacent unit-charge correlation grows exponentially in `κ`**: for `0 < ξ < 1` and
`κ ≥ 0`, `G ≥ e^{κ r}/3` with `r = min(2ε − (1 − ξ)²/2, ξ(1 − ξ/2)/4)`. -/
theorem regionCorr_adjacent_ge {κ ε ξ : ℝ} (hκ : 0 ≤ κ) (hξ0 : 0 < ξ) (hξ1 : ξ < 1) :
    Real.exp (κ * min (2 * ε - (1 - ξ) ^ 2 / 2) (ξ * (1 - ξ / 2) / 4)) / 3 ≤
      regionConditionLambdaFracCorrInternal adjacentPairInternal κ (unitChargeLawInternal ε κ) ξ
        (0, 0) (1, 0) := by
  rw [regionCorr_adjacent_eq]
  refine le_trans ?_ (twoSite_closedForm_ge hκ)
  refine div_le_div_of_nonneg_right (Real.exp_le_exp.2 ?_) (by norm_num)
  refine mul_le_mul_of_nonneg_left ?_ hκ
  have hp1 := adjacentDipoleQuad_le
  have hp0 := adjacentDipoleQuad_ge
  have hsq : 0 ≤ (1 - ξ) ^ 2 := sq_nonneg _
  have hpos : 0 < ξ * (1 - ξ / 2) := by nlinarith
  refine le_min ((min_le_left _ _).trans ?_) ((min_le_right _ _).trans ?_)
  · nlinarith
  · have : ξ * (1 - ξ / 2) / 4 ≤ adjacentDipoleQuadInternal * (ξ * (1 - ξ / 2)) := by
      nlinarith
    linarith

/-- **The obstruction**: if `(1 − ξ)² < 4ε`, the unit-charge Condition-λ correlation at two
adjacent sites tends to `+∞` as `κ → ∞`. -/
theorem regionCorr_adjacent_tendsto_atTop {ε ξ : ℝ} (hξ0 : 0 < ξ) (hξ1 : ξ < 1)
    (hξε : (1 - ξ) ^ 2 < 4 * ε) :
    Tendsto (fun κ => regionConditionLambdaFracCorrInternal adjacentPairInternal κ
      (unitChargeLawInternal ε κ) ξ (0, 0) (1, 0)) atTop atTop := by
  set r := min (2 * ε - (1 - ξ) ^ 2 / 2) (ξ * (1 - ξ / 2) / 4) with hr
  have hr0 : 0 < r := lt_min (by linarith) (by nlinarith)
  have hT : Tendsto (fun κ : ℝ => Real.exp (κ * r) / 3) atTop atTop := by
    refine Tendsto.atTop_div_const (by norm_num) ?_
    exact Real.tendsto_exp_atTop.comp (tendsto_id.atTop_mul_const hr0)
  refine tendsto_atTop_mono' atTop ?_ hT
  filter_upwards [eventually_ge_atTop 0] with κ hκ
  exact regionCorr_adjacent_ge hκ hξ0 hξ1

/-- **No `κ`-uniform bound in the full FS81 range.** For `0 < η ≤ 1/2` with `η² < 4ε` (possible
for every `ε ∈ (0, 1/16)`), no bound `G_ξ ≤ M` holds for all large `κ`, even on two adjacent sites,
for the unit-charge laws satisfying Condition λ with `(C, α) = (1, 0)`. -/
theorem conditionLambda_no_uniform_bound {ε η : ℝ} (hη : 0 < η) (hη2 : η ≤ 1 / 2)
    (hηε : η ^ 2 < 4 * ε) :
    ¬ ∃ κ₀ M : ℝ, ∀ κ : ℝ, κ₀ < κ → ∀ lam : ℤ → ℝ,
      ConditionLambdaInternal 1 0 ε κ lam → PhysicalWeightInternal lam →
      ∀ ξ : ℝ, 0 < ξ → ξ < 1 → η ≤ dipoleGap ξ →
        regionConditionLambdaFracCorrInternal adjacentPairInternal κ lam ξ (0, 0) (1, 0) ≤ M := by
  rintro ⟨κ₀, M, hM⟩
  have hξ0 : 0 < 1 - η := by linarith
  have hξ1 : 1 - η < 1 := by linarith
  have hgap : η ≤ dipoleGap (1 - η) := by
    unfold dipoleGap
    exact le_min (by linarith) (by linarith)
  have hT := regionCorr_adjacent_tendsto_atTop (ε := ε) hξ0 hξ1 (by rw [sub_sub_cancel]; exact hηε)
  obtain ⟨κ, hκ⟩ := ((hT.eventually_gt_atTop M).and (eventually_gt_atTop κ₀)).exists
  exact absurd (hM κ hκ.2 _ (unitChargeLaw_conditionLambda ε κ) (unitChargeLaw_physical ε κ)
    (1 - η) hξ0 hξ1 hgap) (not_le.2 hκ.1)

/-- **The κ-uniform form of Theorem B fails in FS81's full range**: the marked-cluster estimate statement
(`coulombB_conditionLambda_free`) without its restriction `ε < η²/128` is false. -/
theorem not_coulombB_conditionLambda_free_uniform :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ C α ε : ℝ, 0 ≤ C → 0 ≤ α → ε < 1 / 16 →
      ∀ η : ℝ, 0 < η →
        ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, κ₀ < κ → ∀ lam : ℤ → ℝ,
          ConditionLambdaInternal C α ε κ lam → PhysicalWeightInternal lam →
          ∀ (Λ : Finset (ℤ × ℤ)) (ξ : ℝ) (x y : ℤ × ℤ),
            x ∈ Λ → y ∈ Λ → x ≠ y → 0 < ξ → ξ < 1 → η ≤ dipoleGap ξ →
            0 ≤ regionConditionLambdaFracCorrInternal Λ κ lam ξ x y ∧
              regionConditionLambdaFracCorrInternal Λ κ lam ξ x y ≤
                2 * ((((y.1 - x.1).natAbs + (y.2 - x.2).natAbs : ℕ) + 1 : ℝ) ^
                  (-(c * η ^ 2 * κ))) := by
  rintro ⟨c, hc, h⟩
  obtain ⟨κ₀, hκ₀pos, hκ₀⟩ := h 1 0 (1 / 32) zero_le_one le_rfl (by norm_num) (1 / 8)
    (by norm_num)
  refine conditionLambda_no_uniform_bound (ε := 1 / 32) (η := 1 / 8) (by norm_num) (by norm_num)
    (by norm_num) ⟨κ₀, 2, fun κ hκ lam hlam hphys ξ hξ0 hξ1 hηξ => ?_⟩
  have hκ0 : 0 < κ := hκ₀pos.trans hκ
  have hb := (hκ₀ κ hκ lam hlam hphys adjacentPairInternal ξ (0, 0) (1, 0) (by simp) (by simp)
    (by simp) hξ0 hξ1 hηξ).2
  refine hb.trans ?_
  have hpow : ∀ t : ℝ, 1 ≤ t → t ^ (-(c * (1 / 8) ^ 2 * κ)) ≤ 1 := fun t ht =>
    Real.rpow_le_one_of_one_le_of_nonpos ht (by nlinarith)
  have h1 := hpow _ (le_add_of_nonneg_left (Nat.cast_nonneg
    ((((1, 0) : ℤ × ℤ).1 - ((0, 0) : ℤ × ℤ).1).natAbs +
      (((1, 0) : ℤ × ℤ).2 - ((0, 0) : ℤ × ℤ).2).natAbs)))
  linarith

end Adjacent

end FroehlichSpencer.BKT.Coulomb

end
