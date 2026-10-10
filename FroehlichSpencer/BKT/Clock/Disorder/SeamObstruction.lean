/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Clock.Disorder.SeamTwistedWeight
public import FroehlichSpencer.BKT.Clock.Disorder.FiniteCarrier
public import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

/-!
# (7.5) fails for twists with `Nξ ∉ ℤ`

`⟨D^ξ⟩_Λ ≤ λ^r`, for some `λ = λ(β, N, ξ) < 1`, uniformly in the box   (`clockDisorderExpectation_le_pow`).

So no power-law lower bound `const·(1 + r)^{−ξ²β'''/(2π)}` can hold at such `ξ`
(`not_clockDisorder_powerLaw`).

Summing over the spins leaves the
   currents with zero divergence mod `N`, each with a nonnegative multiplicity.

So
   `|Z(f)| ≤ (∏_e λ_e) Z(g)` whenever `‖f̂_e‖ ≤ λ_e ĝ_e` with `ĝ_e ≥ 0`
   (`norm_clockEdgeSum_le`).
3. **One seam bond.** `ŵ_δ(μ) = ∑_{a − b ≡ μ (N)} T(a, b) e^{i(a − b)δ}` with `T > 0`.

The frequencies
   `μ` and `μ + N` carry phases differing by `e^{iNδ} ≠ 1`, so `‖ŵ_δ‖ ≤ λ ŵ₀` with `λ < 1`
   (`exists_twistedClockWeight_contraction`).

Physically, each seam bond carries a current defined only modulo `N`.

Adding `N` units of current
across the seam costs the phase `e^{2πiNξ}`, which is trivial exactly when `Nξ ∈ ℤ`.

For the
`ℤ_N` disorder operators (`ξ ∈ (1/N)ℤ`), `λ = 1` and this argument gives no decay.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Clock.Disorder

open Filter Topology
open FroehlichSpencer.BKT.Rotator
open FroehlichSpencer.BKT.Clock.Compact

/-! ### The seam bonds of the free square -/

/-- The internal bond of the free square crossing the seam at index `i`: the vertical bond from
`seamLowerSite i` to `seamUpperSite i`. -/
def seamBond {r L : ℕ} (hL : 0 < L) (hr : r ≤ L) (i : Fin r) : RotatorInternalBond (2 * L) :=
  Sum.inr (⟨L + i.val + 1, by have := i.isLt; omega⟩, ⟨⟨L, by omega⟩, by simp; omega⟩)

theorem seamBond_src {r L : ℕ} (hL : 0 < L) (hr : r ≤ L) (i : Fin r) :
    (rotatorFreeGraph (2 * L)).src (seamBond hL hr i) = seamLowerSite hL hr i := rfl

theorem seamBond_tgt {r L : ℕ} (hL : 0 < L) (hr : r ≤ L) (i : Fin r) :
    (rotatorFreeGraph (2 * L)).tgt (seamBond hL hr i) = seamUpperSite hL hr i := rfl

theorem seamBond_injective {r L : ℕ} (hL : 0 < L) (hr : r ≤ L) :
    Function.Injective (seamBond hL hr) := by
  intro i j h
  unfold seamBond at h
  have h1 := congrArg Fin.val (congrArg Prod.fst (Sum.inr_injective h))
  simp only at h1
  exact Fin.ext (by omega)

/-- The seam bonds as a finite set. -/
def seamBondSet {r L : ℕ} (hL : 0 < L) (hr : r ≤ L) : Finset (RotatorInternalBond (2 * L)) :=
  Finset.univ.image (seamBond hL hr)

theorem card_seamBondSet {r L : ℕ} (hL : 0 < L) (hr : r ≤ L) : (seamBondSet hL hr).card = r := by
  unfold seamBondSet
  rw [Finset.card_image_of_injective _ (seamBond_injective hL hr), Finset.card_univ,
    Fintype.card_fin]

/-- The bond twists: `−2πξ` on the seam bonds and `0` elsewhere. -/
def seamTwist {r L : ℕ} (hL : 0 < L) (hr : r ≤ L) (ξ : ℝ) (e : RotatorInternalBond (2 * L)) : ℝ :=
  if e ∈ seamBondSet hL hr then -(2 * Real.pi * ξ) else 0

/-! ### Step 1: the disorder insertion as a twisted product -/

theorem clockBoxWeight_eq_prod (N L : ℕ) (β : ℝ) (k : RotatorSpinSite (2 * L) → Fin N) :
    clockBoxWeight N (2 * L) β k =
      ∏ e, twistedClockWeight β 0
        (clockEdgeAngle N (rotatorFreeGraph (2 * L)).src (rotatorFreeGraph (2 * L)).tgt k e) := by
  unfold clockBoxWeight twistedClockWeight clockEdgeAngle clockAngles
  rw [Real.exp_sum]
  refine Finset.prod_congr rfl fun e _ => ?_
  rw [add_zero]

/-- One seam factor: the bond weight times the disorder ratio is the twisted weight. -/
theorem seam_factor_eq (β ξ d a : ℝ) (had : a = -d) :
    Real.exp (β * Real.cos (d + 2 * Real.pi * ξ)) / Real.exp (β * Real.cos d) *
      twistedClockWeight β 0 a = twistedClockWeight β (-(2 * Real.pi * ξ)) a := by
  unfold twistedClockWeight
  rw [had, add_zero, Real.cos_neg, div_mul_cancel₀ _ (Real.exp_pos _).ne',
    show -d + -(2 * Real.pi * ξ) = -(d + 2 * Real.pi * ξ) by ring, Real.cos_neg]

/-- **The disorder insertion times the clock weight is the twisted bond product.** -/
theorem clockDisorder_mul_weight_eq {r L : ℕ} (N : ℕ) (β ξ : ℝ) (hN : 0 < N)
    (hL : 0 < L) (hr : r ≤ L) (k : RotatorSpinSite (2 * L) → Fin N) :
    clockDisorder N β ξ hN k hL hr * clockBoxWeight N (2 * L) β k =
      ∏ e, twistedClockWeight β (seamTwist hL hr ξ e)
        (clockEdgeAngle N (rotatorFreeGraph (2 * L)).src (rotatorFreeGraph (2 * L)).tgt k e) := by
  classical
  set a := clockEdgeAngle N (rotatorFreeGraph (2 * L)).src (rotatorFreeGraph (2 * L)).tgt k
    with ha
  set S := seamBondSet hL hr with hS
  have hsplit : ∀ F : RotatorInternalBond (2 * L) → ℝ,
      ∏ e, F e = (∏ i : Fin r, F (seamBond hL hr i)) * ∏ e ∈ Finset.univ.filter (· ∉ S), F e := by
    intro F
    rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (· ∈ S)]
    congr 1
    rw [Finset.filter_mem_eq_inter, Finset.univ_inter, hS, seamBondSet,
      Finset.prod_image fun i _ j _ h => seamBond_injective hL hr h]
  rw [clockBoxWeight_eq_prod, hsplit, hsplit]
  have hrest : ∏ e ∈ Finset.univ.filter (· ∉ S), twistedClockWeight β 0 (a e) =
      ∏ e ∈ Finset.univ.filter (· ∉ S), twistedClockWeight β (seamTwist hL hr ξ e) (a e) := by
    refine Finset.prod_congr rfl fun e he => ?_
    have he' : e ∉ S := (Finset.mem_filter.mp he).2
    unfold seamTwist
    simp only [← hS, he', ↓reduceIte]
  rw [← hrest, ← mul_assoc]
  congr 1
  unfold clockDisorder
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hmem : seamBond hL hr i ∈ S := Finset.mem_image_of_mem _ (Finset.mem_univ i)
  have hai : a (seamBond hL hr i) =
      -(clockAngles N k (seamUpperSite hL hr i) - clockAngles N k (seamLowerSite hL hr i)) := by
    rw [ha]
    unfold clockEdgeAngle clockAngles
    rw [seamBond_src, seamBond_tgt]
    ring
  unfold clockDisorderFactor seamTwist
  simp only [← hS, hmem, ↓reduceIte]
  exact seam_factor_eq β ξ _ _ hai

/-! ### Step 2–3: the exponential bound -/

theorem seamTwist_contraction {N : ℕ} (hN : 0 < N) {β ξ : ℝ} (hβ : 0 < β)
    (hξ : ∀ j : ℤ, (N : ℝ) * ξ ≠ j) :
    ∃ lam : ℝ, 0 ≤ lam ∧ lam < 1 ∧
      ∀ μ : Fin N, ‖clockAngleFourier N (twistedClockWeight β (-(2 * Real.pi * ξ))) μ‖ ≤
        lam * clockWeightCoeff N β μ := by
  refine exists_twistedClockWeight_contraction hN hβ fun j h => hξ (-j) ?_
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  push_cast
  have : (N : ℝ) * ξ * (2 * Real.pi) = -(j * (2 * Real.pi)) := by linear_combination -h
  have h2 : (N : ℝ) * ξ = -j := by
    have := mul_right_cancel₀ hpi (this.trans (by ring : -(j * (2 * Real.pi)) = -j * (2 * Real.pi)))
    exact this
  exact h2

/-- **Exponential decay of the seam disorder expectation** for `β > 0` and `Nξ ∉ ℤ`, uniformly in
the box: `⟨D^ξ⟩_Λ ≤ λ^r` with `λ = λ(β, N, ξ) < 1`. -/
theorem clockDisorderExpectation_le_pow {N : ℕ} (hN : 0 < N) {β ξ : ℝ} (hβ : 0 < β)
    (hξ : ∀ j : ℤ, (N : ℝ) * ξ ≠ j) :
    ∃ lam : ℝ, 0 ≤ lam ∧ lam < 1 ∧ ∀ (r L : ℕ) (hL : 0 < L) (hr : r ≤ L),
      clockDisorderExpectation N β ξ hN hL hr ≤ lam ^ r := by
  classical
  obtain ⟨lam, hlam0, hlam1, hcontr⟩ := seamTwist_contraction hN hβ hξ
  refine ⟨lam, hlam0, hlam1, fun r L hL hr => ?_⟩
  set src := (rotatorFreeGraph (2 * L)).src
  set tgt := (rotatorFreeGraph (2 * L)).tgt
  have hnum : (∑ k : RotatorSpinSite (2 * L) → Fin N,
      clockDisorder N β ξ hN k hL hr * clockBoxWeight N (2 * L) β k) =
      clockEdgeSum N src tgt fun e => twistedClockWeight β (seamTwist hL hr ξ e) := by
    unfold clockEdgeSum
    exact Finset.sum_congr rfl fun k _ => clockDisorder_mul_weight_eq N β ξ hN hL hr k
  have hden : clockDisorderPartition N L β hN =
      clockEdgeSum N src tgt fun _ => twistedClockWeight β 0 := by
    unfold clockDisorderPartition clockEdgeSum
    exact Finset.sum_congr rfl fun k _ => clockBoxWeight_eq_prod N L β k
  have hbound := norm_clockEdgeSum_le hN src tgt
    (fun e => twistedClockWeight β (seamTwist hL hr ξ e)) (fun _ => twistedClockWeight β 0)
    (fun e => twistedClockWeight_periodic β _) (fun _ => twistedClockWeight_periodic β 0)
    (fun _ μ => clockWeightCoeff N β μ)
    (fun _ μ => clockAngleFourier_twistedClockWeight_zero hN β μ)
    (fun e => if e ∈ seamBondSet hL hr then lam else 1) (fun e μ => ?_)
  · have hprod : ∏ e, (if e ∈ seamBondSet hL hr then lam else 1) = lam ^ r := by
      rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const,
        Finset.filter_mem_eq_inter, Finset.univ_inter, card_seamBondSet]
    rw [hprod] at hbound
    have hZ := clockDisorderPartition_pos N L β hN
    unfold clockDisorderExpectation
    rw [div_le_iff₀ hZ, hnum, hden]
    exact (le_abs_self _).trans hbound
  · by_cases he : e ∈ seamBondSet hL hr
    · simp only [he, ↓reduceIte, seamTwist]
      exact hcontr μ
    · simp only [he, ↓reduceIte, seamTwist, one_mul]
      rw [clockAngleFourier_twistedClockWeight_zero hN β μ, Complex.norm_real,
        Real.norm_of_nonneg (clockWeightCoeff_pos hβ μ).le]

/-- Every limit point of the exhaustion obeys the same exponential bound. -/
theorem clockDisorderLimitPoint_le_pow {N : ℕ} (hN : 0 < N) {β ξ : ℝ} (hβ : 0 < β)
    (hξ : ∀ j : ℤ, (N : ℝ) * ξ ≠ j) :
    ∃ lam : ℝ, 0 ≤ lam ∧ lam < 1 ∧ ∀ (r : ℕ) (hr : 0 < r) (c : ℝ),
      IsClockDisorderLimitPoint N r β ξ c hN hr → c ≤ lam ^ r := by
  obtain ⟨lam, hlam0, hlam1, hle⟩ := clockDisorderExpectation_le_pow hN hβ hξ
  refine ⟨lam, hlam0, hlam1, fun r hr c hc => ?_⟩
  obtain ⟨s, -, hlim⟩ := hc
  exact le_of_tendsto' hlim fun t => hle r (r + s t) (by omega) (by omega)

/-! ### (7.5) fails -/

/-- Exponential decay beats every power: `λ^r < const (1 + r)^{−B}` for some `r ≥ 1`. -/
theorem exists_pow_lt_rpow {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam < 1) {C : ℝ} (hC : 0 < C)
    (B : ℝ) : ∃ r : ℕ, 0 < r ∧ lam ^ r < C * (1 + (r : ℝ)) ^ (-B) := by
  set k : ℕ := ⌈B⌉₊
  have hlim : Tendsto (fun n : ℕ => (2 : ℝ) ^ k * ((n : ℝ) ^ k * lam ^ n)) atTop (𝓝 0) := by
    have := tendsto_pow_const_mul_const_pow_of_abs_lt_one k (abs_lt.mpr ⟨by linarith, hlam1⟩)
    simpa using this.const_mul ((2 : ℝ) ^ k)
  obtain ⟨n, hn, hn1⟩ := ((hlim.eventually (gt_mem_nhds hC)).and
    (eventually_ge_atTop 1)).exists
  refine ⟨n, hn1, ?_⟩
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have h1 : (1 : ℝ) ≤ 1 + n := by linarith
  have hpos : 0 < (1 + (n : ℝ)) ^ B := Real.rpow_pos_of_pos (by linarith) B
  have hB : (1 + (n : ℝ)) ^ B ≤ (2 : ℝ) ^ k * (n : ℝ) ^ k := by
    calc (1 + (n : ℝ)) ^ B ≤ (1 + (n : ℝ)) ^ (k : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le h1 (Nat.le_ceil B)
      _ = (1 + (n : ℝ)) ^ k := Real.rpow_natCast _ _
      _ ≤ (2 * n) ^ k := pow_le_pow_left₀ (by linarith) (by linarith) k
      _ = (2 : ℝ) ^ k * (n : ℝ) ^ k := mul_pow _ _ _
  have hprod : lam ^ n * (1 + (n : ℝ)) ^ B < C := by
    calc lam ^ n * (1 + (n : ℝ)) ^ B ≤ lam ^ n * ((2 : ℝ) ^ k * (n : ℝ) ^ k) :=
          mul_le_mul_of_nonneg_left hB (pow_nonneg hlam0 n)
      _ = (2 : ℝ) ^ k * ((n : ℝ) ^ k * lam ^ n) := by ring
      _ < C := hn
  rw [Real.rpow_neg (by linarith), ← div_eq_mul_inv, lt_div_iff₀ hpos]
  exact hprod

/-- **No power-law lower bound** at a twist with `Nξ ∉ ℤ`: for every `const > 0` and every exponent
`B`, some seam length `r ≥ 1` has a limit point below `const (1 + r)^{−B}`. -/
theorem not_clockDisorder_powerLaw {N : ℕ} (hN : 0 < N) {β ξ : ℝ} (hβ : 0 < β)
    (hξ : ∀ j : ℤ, (N : ℝ) * ξ ≠ j) {C : ℝ} (hC : 0 < C) (B : ℝ) :
    ∃ (r : ℕ) (hr : 0 < r) (c : ℝ), IsClockDisorderLimitPoint N r β ξ c hN hr ∧
      c < C * (1 + (r : ℝ)) ^ (-B) := by
  obtain ⟨lam, hlam0, hlam1, hle⟩ := clockDisorderLimitPoint_le_pow hN hβ hξ
  obtain ⟨r, hr, hlt⟩ := exists_pow_lt_rpow hlam0 hlam1 hC B
  obtain ⟨c, hc⟩ := exists_clockDisorderLimitPoint N r hr β ξ hN
  exact ⟨r, hr, c, hc, (hle r hr c hc).trans_lt hlt⟩

/--
It already fails at `ξ = 1/(2N)`.
-/
theorem not_clockDisorder_lowerBound {N : ℕ} (hN : 0 < N) {β : ℝ} (hβ : 0 < β) :
    ¬ ∃ β''' : ℝ, ∀ ξ : ℝ, 0 < ξ → ξ < 1 → ∃ C : ℝ, 0 < C ∧
      ∀ (r : ℕ) (hr : 0 < r) (c : ℝ), IsClockDisorderLimitPoint N r β ξ c hN hr →
        C * (1 + (r : ℝ)) ^ (-(ξ ^ 2 * β''' / (2 * Real.pi))) ≤ c := by
  rintro ⟨β''', h⟩
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  set ξ : ℝ := 1 / (2 * N)
  have hξ0 : 0 < ξ := by positivity
  have hξ1 : ξ < 1 := by
    rw [div_lt_one (by positivity)]
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hξZ : ∀ j : ℤ, (N : ℝ) * ξ ≠ j := by
    intro j hj
    have h2 : (N : ℝ) * ξ = 1 / 2 := by
      simp only [ξ]
      field_simp
    rw [h2] at hj
    have h3 : (2 : ℝ) * j = 1 := by linarith
    have h4 : (2 : ℤ) * j = 1 := by exact_mod_cast h3
    omega
  obtain ⟨C, hC, hlow⟩ := h ξ hξ0 hξ1
  obtain ⟨r, hr, c, hc, hlt⟩ := not_clockDisorder_powerLaw hN hβ hξZ hC
    (ξ ^ 2 * β''' / (2 * Real.pi))
  exact absurd (hlow r hr c hc) (not_le.mpr hlt)

/-- **The root shape of (7.5) is false**: there is no threshold function `n₁` such that for every
`β > 0` and every `N ≥ n₁(β)` some `β'''(β, N)` gives the (7.5) bound for all `ξ ∈ (0, 1)` at every
limit point (whatever the behaviour of `n₁` as `β → ∞`). -/
theorem not_clockDisorder_lowerBound_root :
    ¬ ∃ n₁ : ℝ → ℕ, ∀ β : ℝ, 0 < β → ∀ (N : ℕ) (hN : 0 < N), n₁ β ≤ N →
      ∃ β''' : ℝ, ∀ ξ : ℝ, 0 < ξ → ξ < 1 → ∃ C : ℝ, 0 < C ∧
        ∀ (r : ℕ) (hr : 0 < r) (c : ℝ), IsClockDisorderLimitPoint N r β ξ c hN hr →
          C * (1 + (r : ℝ)) ^ (-(ξ ^ 2 * β''' / (2 * Real.pi))) ≤ c := by
  rintro ⟨n₁, h⟩
  have hN : 0 < n₁ 1 + 1 := Nat.succ_pos _
  exact not_clockDisorder_lowerBound hN one_pos (h 1 one_pos (n₁ 1 + 1) hN (Nat.le_succ _))

end FroehlichSpencer.BKT.Clock.Disorder

end
