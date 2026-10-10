/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Clock.Compact.TwoPoint
public import FroehlichSpencer.BKT.Clock.Compact.MarkedDomain
public import FroehlichSpencer.BKT.Coulomb.TheoremB
public import FroehlichSpencer.BKT.SpinWaves.ShellPacking
import Mathlib.Tactic

/-!
# FS81 Theorem 7.1(2): decay of the high clock harmonics

**The route.** For each Fejér cutoff `M`, the clock comb is replaced by the shifted Fejér weights
`F_M(φ − δ_n)`.

These are a positive site mixture with leaves `≤ e^{2q}` (`mixtureLeaf_fejer_le`;
the geometric mixture `geomMixture`).

1.

`clock_markedDomain_bound` bounds each Fejér ratio on the KP square, uniformly in `M`.
2.

`tendsto_clockFejerRatio` identifies the limit `M → ∞` with the Ginibre clock two-point
   function.

The comb is never expanded as a distribution.

Each cutoff carries the **exact** finite mixture
identity of KP T2.2 (`t22MixStep_holds`), and the marked expansion is exact.

**Constants.**
* `clockDecay = 10⁷ M²/(32 log 2)`, `M = chargeCoverScale`: an absolute exponent.
* `n₀(β, η)` collects the following conditions:
  - the unmarked envelope conditions;
  - the composite strip `28 λ_c ≤ n` and cost `8192 β λ_c ≤ η n²`, with `λ_c = 10⁷ D₁ M²/η`.

* `clock_twoPoint_squareBox_le`: on the squares `{0, …, L}²`.
* `clock_twoPoint_freeBox_le`: on the centred boxes `[−L, L]²`.
* **`clock_twoPointLimit_le`**: for the free thermodynamic limit `twoPointLimit` of `BKT/Ginibre`.

**Reading of the source.**
- The observable is the Ginibre two-point function `⟨cos(ξ(θ_u − θ_v))⟩`, the real part of FS81's
  `⟨e^{iξ(θ_0 − θ_x)}⟩`.

The imaginary part vanishes by the symmetry `θ ↦ −θ`, which is not
  restated here.
- The quantifiers are those of FS81: `n₀` depends on `β` and `q = η`.

The bound is stated with
  `η ≤ min(ξ/n, 1 − ξ/n)` for every `0 < ξ < n`, and is stronger in two respects:
  - the exponent `c` is absolute (FS81: `ξ²/(2πβ'')` with `β'' = β''(β, n, q) < ∞`; take
    `β'' = ξ²/(2πc)`);
  - the prefactor is `2`.
- The thermodynamic limit is the free limit of `BKT/Ginibre` along the centred boxes.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Clock.Compact

open MeasureTheory Filter Topology
open SpinWaves Reduction
open FroehlichSpencer.BKT.Clock.Periodic
open FroehlichSpencer.BKT.Generic
open FroehlichSpencer.BKT.Generic.Marked

/-! ### The Fejér weights of the clock comb as a site mixture -/

section FejerMixture

/-- The geometric normalization `∑_{q = 1}^M 2^{-q}`. -/
def geomNorm (M : ℕ) : ℝ := ∑ q : SiteMode M, (1 / 2 : ℝ) ^ (q : ℕ)

theorem geomNorm_pos {M : ℕ} (hM : 0 < M) : 0 < geomNorm M :=
  Finset.sum_pos (fun q _ => by positivity) ⟨⟨1, Finset.mem_Icc.2 ⟨le_rfl, hM⟩⟩, Finset.mem_univ _⟩

theorem geomNorm_le_one (M : ℕ) : geomNorm M ≤ 1 := by
  unfold geomNorm
  calc ∑ q : SiteMode M, (1 / 2 : ℝ) ^ (q : ℕ) = ∑ q ∈ Finset.Icc 1 M, (1 / 2 : ℝ) ^ q :=
        Finset.sum_coe_sort (Finset.Icc 1 M) (fun q => (1 / 2 : ℝ) ^ q)
    _ ≤ ∑ q ∈ Finset.range (M + 1), (1 / 2 : ℝ) ^ q - 1 := by
        have h : Finset.range (M + 1) = insert 0 (Finset.Icc 1 M) := by
          ext q; simp [Finset.mem_Icc]; omega
        rw [h, Finset.sum_insert (by simp)]
        simp
    _ ≤ 2 - 1 := by
        have := sum_geometric_two_le (M + 1)
        linarith
    _ = 1 := by norm_num

/-- The geometric mixture `ζ(q) = 2^{-q}/∑_{q'=1}^M 2^{-q'}` on the frequencies `1, …, M`. -/
def geomMixture (M : ℕ) (q : SiteMode M) : ℝ := (1 / 2 : ℝ) ^ (q : ℕ) / geomNorm M

/-- The Fourier coefficient of the shifted Fejér weight `F_M(φ − δ)`, `δ ∈ {0, π}`. -/
def fejerShiftCoeff (M : ℕ) (δ : ℝ) (q : ℕ) : ℝ :=
  fejerFourierCoefficient M (q : ℤ) * Real.cos (q * δ)

theorem sin_mul_clockOffset (n q : ℕ) : Real.sin (q * clockOffset n) = 0 := by
  unfold clockOffset
  split_ifs
  · exact Real.sin_nat_mul_pi q
  · simp

theorem fejerPolynomial_sub_clockOffset (M n : ℕ) (φ : ℝ) :
    fejerPolynomial M (φ - clockOffset n) =
      1 + 2 * ∑ q ∈ Finset.Icc 1 M, fejerShiftCoeff M (clockOffset n) q * Real.cos (q * φ) := by
  rw [fejerPolynomial_eq_fourierCosineExpansion]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  unfold fejerShiftCoeff
  rw [mul_sub, Real.cos_sub, sin_mul_clockOffset]
  ring

theorem abs_fejerShiftCoeff_le (M : ℕ) (δ : ℝ) (q : ℕ) : |fejerShiftCoeff M δ q| ≤ 1 := by
  unfold fejerShiftCoeff
  have hcoeff := fejerFourierCoefficient_mem_unitInterval M (q : ℤ)
  rw [abs_mul]
  have h1 : |fejerFourierCoefficient M (q : ℤ)| ≤ 1 := by
    rw [abs_le]; exact ⟨le_trans (by norm_num) hcoeff.1, hcoeff.2⟩
  calc |fejerFourierCoefficient M (q : ℤ)| * |Real.cos (q * δ)| ≤ 1 * 1 :=
        mul_le_mul h1 (Real.abs_cos_le_one _) (abs_nonneg _) zero_le_one
    _ = 1 := one_mul 1

/-- The clock mixture leaves are at most `e^{2q}`. -/
theorem mixtureLeaf_fejer_le {L M : ℕ} (hM : 0 < M) (n : ℕ) (j : Fin L × Fin L) (q : ℕ) :
    mixtureLeaf (fun _ => M) (fun _ => fejerShiftCoeff M (clockOffset n))
      (fun _ => geomMixture M) j q ≤ Real.exp (2 * q) := by
  unfold mixtureLeaf
  split_ifs with h
  · have hq1 : 1 ≤ q := (Finset.mem_Icc.1 h).1
    have hZ := geomNorm_pos hM
    have hZ1 := geomNorm_le_one M
    unfold geomMixture
    rw [div_div_eq_mul_div]
    have hp : (0 : ℝ) < (1 / 2) ^ q := by positivity
    rw [div_le_iff₀ hp]
    have hc := abs_fejerShiftCoeff_le M (clockOffset n) q
    have h2 : 2 * |fejerShiftCoeff M (clockOffset n) q| * geomNorm M ≤ 2 := by nlinarith
    have h4 : (2 : ℝ) ≤ Real.exp (2 * q) * (1 / 2) ^ q := by
      have he : Real.exp (2 * (q : ℝ)) = (Real.exp 2) ^ q := by
        rw [← Real.exp_nat_mul]; ring_nf
      rw [he, ← mul_pow]
      have h7 : (2 : ℝ) ≤ Real.exp 2 * (1 / 2) := by
        have := Real.quadratic_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)
        linarith
      calc (2 : ℝ) ≤ Real.exp 2 * (1 / 2) := h7
        _ ≤ (Real.exp 2 * (1 / 2)) ^ q :=
            le_self_pow₀ (by linarith) (by omega)
    linarith
  · exact (Real.exp_pos _).le

end FejerMixture

/-! ### Constants -/

section Constants

theorem isCostEnvelope_mono {c : ℝ → ℝ} {κ κ' W κ₂ κ₂' : ℝ} (h : IsCostEnvelope c κ κ' W)
    (hκ : κ ≤ κ₂) (hκ' : κ' ≤ κ₂') : IsCostEnvelope c κ₂ κ₂' W where
  even := h.even
  zero := h.zero
  nonneg_κ := h.nonneg_κ.trans hκ
  nonneg_κ' := h.nonneg_κ'.trans hκ'
  quad u hu := (h.quad u hu).trans (mul_le_mul_of_nonneg_right hκ (sq_nonneg u))
  expo u hu hW := (h.expo u hu hW).trans
    (mul_le_mul_of_nonneg_right hκ' (Real.exp_pos _).le)

theorem rpow_gradExponent_seven (m : ℕ) :
    (2 : ℝ) ^ (gradExponent (7 / 4) * ((7 * m : ℕ) : ℝ)) = 8 ^ m := by
  have h : gradExponent (7 / 4) * ((7 * m : ℕ) : ℝ) = ((3 * m : ℕ) : ℝ) := by
    unfold gradExponent
    push_cast
    ring
  rw [h, Real.rpow_natCast, pow_mul]
  norm_num

end Constants

/-! ### FS81 Theorem 7.1(2) on the free squares -/

section Square

open FroehlichSpencer.BKT.Ginibre FroehlichSpencer.BKT.Rotator FroehlichSpencer.BKT.Rotator.Ginibre

/-- The decay rate of Theorem 7.1(2): `c = 10⁷ M²/(32 log 2)`, `M = chargeCoverScale`. -/
def clockDecay : ℝ := 10 ^ 7 * (chargeCoverScale : ℝ) ^ 2 / 32 / Real.log 2

theorem clockDecay_pos : 0 < clockDecay := by
  unfold clockDecay
  have : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hM : (0 : ℝ) < (chargeCoverScale : ℝ) := by norm_num [chargeCoverScale]
  positivity

/-- The composite conditions (C1)–(C3) for `λ_c η = 10⁷ D₁ M²`. -/
theorem clock_composite_conditions {D₁ Mc lamc η : ℝ} (hD₁ : 1 ≤ D₁) (hMc : 1 ≤ Mc)
    (hlη : lamc * η = 10 ^ 7 * D₁ * Mc ^ 2) :
    (2 : ℝ) + 4 + 1 ≤ lamc * η / 8 ∧
      4 * (288 * Mc ^ 2 * Real.exp (-4)) ≤ lamc * η / 16 ∧
      289 * 200 + 289 * (4 : ℝ) ≤ lamc * η / (32 * D₁) := by
  have hD₁pos : 0 < D₁ := by linarith
  have hM2 : 1 ≤ Mc ^ 2 := one_le_pow₀ hMc
  have he : Real.exp (-4) ≤ 1 := by rw [Real.exp_le_one_iff]; norm_num
  rw [hlη]
  refine ⟨?_, ?_, ?_⟩
  · have : (1 : ℝ) ≤ D₁ * Mc ^ 2 := one_le_mul_of_one_le_of_one_le hD₁ hM2
    nlinarith
  · have : Mc ^ 2 ≤ D₁ * Mc ^ 2 := le_mul_of_one_le_left (by positivity) hD₁
    nlinarith [Real.exp_pos (-4)]
  · rw [show 10 ^ 7 * D₁ * Mc ^ 2 / (32 * D₁) = 10 ^ 7 * Mc ^ 2 / 32 by field_simp]
    nlinarith

/-- The unmarked smallness conditions on the threshold. -/
theorem clock_unmarked_conditions {β amp W N : ℝ} {k₀ : ℕ} (hβ : 0 ≤ β) (hamp : 0 < amp)
    (hN : 0 < N)
    (hXe : 200 * 4 ^ k₀ * (β + 1) * W ^ 2 * (1 + Real.exp (2 * Real.pi * W)) / amp ≤ N ^ 2)
    (hX8 : 8192 * (β + 1) * amp ≤ N ^ 2) (hW : W = amp * 28) :
    100 * 4 ^ k₀ * costMajorant ((β + 1) / N ^ 2) ((β + 1) * W ^ 2 / N ^ 2) (amp * 28) ≤ amp / 2 ∧
      amp ≤ 1 / (2 * ((β + 1) / N ^ 2) * 4096) := by
  have hN2 : 0 < N ^ 2 := by positivity
  refine ⟨?_, ?_⟩
  · unfold costMajorant
    rw [← hW]
    rw [div_le_iff₀ hamp] at hXe
    have key : 100 * 4 ^ k₀ * ((β + 1) / N ^ 2 * W ^ 2 +
        (β + 1) * W ^ 2 / N ^ 2 * Real.exp (2 * Real.pi * W)) =
        (200 * 4 ^ k₀ * (β + 1) * W ^ 2 * (1 + Real.exp (2 * Real.pi * W))) / N ^ 2 / 2 := by
      field_simp
      ring
    rw [key, div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2), div_le_iff₀ hN2]
    nlinarith
  · rw [show 1 / (2 * ((β + 1) / N ^ 2) * 4096) = N ^ 2 / (8192 * (β + 1)) by
      field_simp; ring, le_div_iff₀ (by positivity)]
    nlinarith

/-- **The Fejér-ratio bound on one free square**, uniform in the Fejér cutoff `M`. -/
theorem clock_fejerRatio_le {L : ℕ} (hL : 1 < L + 1) {D₁ D₀ : ℝ} (hD₁ : 1 ≤ D₁)
    (hmono : P21Step .free (L + 1) D₀ → P21Step .free (L + 1) D₁)
    (h21 : P21Step .free (L + 1) D₀) {N : ℕ} (hN : 0 < N) {β : ℝ} (hβ : 0 ≤ β)
    {κ κ' W amp lamc η : ℝ} {k₀ : ℕ} (hc : IsCostEnvelope (clockShiftCost β N) κ κ' W)
    (hκ : 0 < κ) (hamp : 0 < amp) (hampW : amp * 28 ≤ W) (hk₀ : 1 ≤ k₀)
    (hexp : 100 * 4 ^ k₀ * costMajorant κ κ' (amp * 28) ≤ amp / 2)
    (hquad₁ : amp ≤ 1 / (2 * κ * 4096))
    (hquad₂ : amp ≤ (2 : ℝ) ^ (gradExponent (7 / 4) * k₀) / 28)
    (hamp1 : (2 : ℝ) + 4 ≤ amp / 8) (hamp2 : 200 + (4 : ℝ) ≤ amp / (8 * D₁))
    {a b : Fin (L + 1) × Fin (L + 1)} (hab : a ≠ b) {ξ : ℕ} (hξ0 : 0 < ξ) (hξN : ξ < N)
    (hη : 0 < η) (hηξ : η ≤ dipoleGap ((ξ : ℝ) / N)) (hlamc0 : 0 ≤ lamc)
    (hlamcn : 28 * lamc ≤ N) (hcost : 8192 * β * lamc ≤ η * (N : ℝ) ^ 2)
    (C1 : (2 : ℝ) + 4 + 1 ≤ lamc * η / 8)
    (C2 : 4 * (288 * (chargeCoverScale : ℝ) ^ 2 * Real.exp (-4)) ≤ lamc * η / 16)
    (C3 : 289 * 200 + 289 * (4 : ℝ) ≤ lamc * η / (32 * D₁)) (M : ℕ) (hM : 1 ≤ M) :
    (∫ φ, Real.cos ((ξ : ℝ) / N * (φ a - φ b)) * ∏ v, fejerPolynomial M (φ v - clockOffset N)
        ∂clockLaw β N (squareFree (L + 1))) /
      (∫ φ, ∏ v, fejerPolynomial M (φ v - clockOffset N) ∂clockLaw β N (squareFree (L + 1)))
      ≤ 2 * Real.exp (-(lamc * η / (32 * D₁)) *
          Real.logb 2 (latticeDistance .free (L + 1) a b + 1)) := by
  have hMpos : 0 < M := hM
  obtain ⟨hZ, hI⟩ := clock_markedDomain_bound (boundary := .free) hL (Or.inl rfl)
    (squareFree (L + 1)) (squareFree_connected (L + 1) hL) (fun _ _ => rfl)
    (SpinWaves.squareFreeBipartiteDegreeFour (L + 1) hL)
    (SpinWaves.BoundaryShellPacking.l46Statement_holds (L + 1) hL).1 hD₁ (hmono h21)
    (fun _ φ => fejerPolynomial M (φ - clockOffset N)) (fun _ => M)
    (fun _ => fejerShiftCoeff M (clockOffset N)) (fun _ => geomMixture M) (fun _ => hMpos)
    (fun _ q hq => by
      unfold fejerShiftCoeff fejerFourierCoefficient
      rw [ite_eq_right (by intro h; omega), zero_mul])
    (fun _ φ => fejerPolynomial_sub_clockOffset M N φ)
    (fun _ q => by unfold geomMixture; exact div_pos (by positivity) (geomNorm_pos hMpos))
    (fun _ => by
      unfold geomMixture
      rw [← Finset.sum_div]
      exact div_self (geomNorm_pos hMpos).ne')
    (h := 2) (fun j q => mixtureLeaf_fejer_le hMpos N j q) hN hβ hc hκ hamp.le hampW
    hk₀ hexp hquad₁ hquad₂ (s := 4) (by norm_num) Coulomb.exp_neg_four_le hamp1 hamp2 hab
    hξ0 hξN hη hηξ hlamc0 hlamcn hcost C1 C2 C3
  rw [div_le_iff₀ hZ]
  exact (le_abs_self _).trans hI

/-- **FS81 Theorem 7.1(2) on the free squares** (the `ℤ_N` clock, high harmonics). There is an
absolute `c > 0` such that for every `η > 0` and `β ≥ 0` there is `n₀` with: for every `N ≥ n₀`,
every integer harmonic `0 < ξ < N` with `min(ξ/N, 1 − ξ/N) ≥ η`, every square `{0, …, L}²` and
sites `a, b` of it, the free-boundary clock two-point function satisfies
`⟨cos(ξ(θ_a − θ_b))⟩ ≤ 2 (|a − b|₁ + 1)^{−c}`. -/
theorem clock_twoPoint_squareBox_le :
    ∃ c : ℝ, 0 < c ∧ ∀ η : ℝ, 0 < η → ∀ β : ℝ, 0 ≤ β → ∃ n₀ : ℕ, 0 < n₀ ∧
      ∀ N : ℕ, n₀ ≤ N → ∀ (hN : 0 < N) (hβ : 0 ≤ β) (ξ : ℕ), 0 < ξ → ξ < N →
        η ≤ dipoleGap ((ξ : ℝ) / N) → ∀ (L : ℕ) (a b : RotatorSpinSite L),
          (clockModel N hN β hβ).twoPoint (ξ : ℤ) (squareBoxZ L) (siteToZ a) (siteToZ b) ≤
            2 * ((Lattice2D.freeRadius a b : ℝ) + 1) ^ (-c) := by
  classical
  obtain ⟨D₀, -, h21⟩ := kp_p21Statement
  obtain ⟨D₁, hD₁⟩ : ∃ D₁ : ℝ, D₁ = max D₀ 1 := ⟨_, rfl⟩
  have hD₁1 : 1 ≤ D₁ := hD₁ ▸ le_max_right _ _
  have hD₁pos : 0 < D₁ := by linarith
  have hmono : ∀ {L : ℕ}, P21Step .free L D₀ → P21Step .free L D₁ := by
    intro L h cover ϱ hϱ
    obtain ⟨h1, h2⟩ := h cover ϱ hϱ
    refine ⟨h1, h2.trans (mul_le_mul_of_nonneg_right (hD₁ ▸ le_max_left _ _) ?_)⟩
    positivity
  obtain ⟨Mc, hMc⟩ : ∃ Mc : ℝ, Mc = (chargeCoverScale : ℝ) := ⟨_, rfl⟩
  have hMc1 : 1 ≤ Mc := by rw [hMc]; norm_num [chargeCoverScale]
  obtain ⟨Cc, hCc⟩ : ∃ Cc : ℝ, Cc = 10 ^ 7 * D₁ * Mc ^ 2 := ⟨_, rfl⟩
  have hCcpos : 0 < Cc := by rw [hCc]; positivity
  refine ⟨clockDecay, clockDecay_pos, fun η hη β hβ0 => ?_⟩
  obtain ⟨amp, hamp⟩ : ∃ amp : ℝ, amp = 2000 * D₁ := ⟨_, rfl⟩
  have hampp : 0 < amp := by rw [hamp]; positivity
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (28 * amp) (by norm_num : (1 : ℝ) < 8)
  have hm8 : 28 * amp ≤ (8 : ℝ) ^ (m + 1) := by
    have : (8 : ℝ) ^ m ≤ 8 ^ (m + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  obtain ⟨W, hW⟩ : ∃ W : ℝ, W = amp * 28 := ⟨_, rfl⟩
  have hW1 : 1 ≤ W := by rw [hW, hamp]; nlinarith
  obtain ⟨lamc, hlamc⟩ : ∃ lamc : ℝ, lamc = Cc / η := ⟨_, rfl⟩
  have hlη : lamc * η = 10 ^ 7 * D₁ * Mc ^ 2 := by rw [hlamc, ← hCc]; field_simp
  obtain ⟨C1, C2, C3⟩ := clock_composite_conditions hD₁1 hMc1 hlη
  rw [hMc] at C2
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = max (max (max W (28 * lamc)) (max (8192 * (β + 1) * amp)
      (8192 * β * lamc / η + 1)))
      (200 * 4 ^ (7 * (m + 1)) * (β + 1) * W ^ 2 * (1 + Real.exp (2 * Real.pi * W)) / amp) :=
    ⟨_, rfl⟩
  obtain ⟨n₀, hn₀⟩ := exists_nat_ge X
  refine ⟨n₀ + 1, Nat.succ_pos _, fun N hNn₀ hN hβ ξ hξ0 hξN hηξ L a b => ?_⟩
  by_cases hab : a = b
  · subst hab
    have h1 := (clockModel N hN β hβ).twoPoint_le_one (ξ : ℤ) (squareBoxZ L) (siteToZ a)
      (siteToZ a)
    have : Lattice2D.freeRadius a a = 0 := by simp [Lattice2D.freeRadius]
    rw [this]
    simp only [Nat.cast_zero, zero_add, Real.one_rpow, mul_one]
    linarith
  have hL : 1 < L + 1 := by
    by_contra h
    have hL0 : L = 0 := by omega
    subst hL0
    apply hab
    ext <;> simp [Fin.fin_one_eq_zero]
  have hXN : X ≤ N := by
    have : (n₀ : ℝ) + 1 ≤ N := by exact_mod_cast hNn₀
    linarith
  have hXW' : W ≤ X := by
    rw [hX]; exact le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_left _ _))
  have hX28' : 28 * lamc ≤ X := by
    rw [hX]; exact le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_left _ _))
  have hX8a' : 8192 * (β + 1) * amp ≤ X := by
    rw [hX]; exact le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_left _ _)
  have hX8c' : 8192 * β * lamc / η + 1 ≤ X := by
    rw [hX]; exact le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_left _ _)
  have hXe' : 200 * 4 ^ (7 * (m + 1)) * (β + 1) * W ^ 2 * (1 + Real.exp (2 * Real.pi * W)) / amp
      ≤ X := by
    rw [hX]; exact le_max_right _ _
  have hXW : W ≤ N := hXW'.trans hXN
  have hN1 : (1 : ℝ) ≤ N := hW1.trans hXW
  have hNsq : (N : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
  have hNpos : (0 : ℝ) < N := by linarith
  have hX28 : 28 * lamc ≤ N := hX28'.trans hXN
  have hX8a : 8192 * (β + 1) * amp ≤ (N : ℝ) ^ 2 := hX8a'.trans (hXN.trans hNsq)
  have hX8c : 8192 * β * lamc / η + 1 ≤ (N : ℝ) ^ 2 := hX8c'.trans (hXN.trans hNsq)
  have hXe : 200 * 4 ^ (7 * (m + 1)) * (β + 1) * W ^ 2 * (1 + Real.exp (2 * Real.pi * W)) / amp
      ≤ (N : ℝ) ^ 2 := hXe'.trans (hXN.trans hNsq)
  obtain ⟨hexp, hquad₁⟩ := clock_unmarked_conditions hβ hampp hNpos hXe hX8a hW
  have hc : IsCostEnvelope (clockShiftCost β N) ((β + 1) / (N : ℝ) ^ 2)
      ((β + 1) * W ^ 2 / (N : ℝ) ^ 2) W := by
    have hN2pos : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
    refine isCostEnvelope_mono (clockShiftCost_isCostEnvelope hβ hN1 hXW) ?_ ?_
    · exact div_le_div_of_nonneg_right (by linarith) hN2pos.le
    · exact div_le_div_of_nonneg_right (by nlinarith [sq_nonneg W]) hN2pos.le
  have hcost : 8192 * β * lamc ≤ η * (N : ℝ) ^ 2 := by
    have : 8192 * β * lamc / η ≤ (N : ℝ) ^ 2 := by linarith
    rw [div_le_iff₀ hη] at this
    linarith
  have hquad₂ : amp ≤ (2 : ℝ) ^ (gradExponent (7 / 4) * ((7 * (m + 1) : ℕ) : ℝ)) / 28 := by
    rw [rpow_gradExponent_seven, le_div_iff₀ (by norm_num)]
    linarith
  have hamp1 : (2 : ℝ) + 4 ≤ amp / 8 := by rw [hamp]; nlinarith
  have hamp2 : 200 + (4 : ℝ) ≤ amp / (8 * D₁) := by
    rw [hamp, show 2000 * D₁ / (8 * D₁) = 250 by field_simp; ring]; norm_num
  have hratio := clock_fejerRatio_le hL hD₁1 hmono (h21 (L + 1) hL).1 hN hβ hc (by positivity)
    hampp (by rw [hW]) (by omega) hexp hquad₁ hquad₂ hamp1 hamp2 hab hξ0 hξN hη hηξ
    (by rw [hlamc]; positivity) hX28 hcost C1 C2 C3
  have hlim := tendsto_clockFejerRatio N L hN hβ ξ a b
  have hle := le_of_tendsto hlim (eventually_atTop.2 ⟨1, fun M hM => hratio M hM⟩)
  refine hle.trans (le_of_eq ?_)
  have hdist : latticeDistance .free (L + 1) a b = Lattice2D.freeRadius a b := by
    show (squareFree (L + 1)).toSimpleGraph.dist a b = _
    exact squareFree_dist_eq_freeRadius hL a b
  rw [hdist, hlη, show 10 ^ 7 * D₁ * Mc ^ 2 / (32 * D₁) = 10 ^ 7 * Mc ^ 2 / 32 by field_simp]
  have hd : (0 : ℝ) < (Lattice2D.freeRadius a b : ℝ) + 1 := by positivity
  rw [Real.rpow_def_of_pos hd, Real.logb, clockDecay, ← hMc]
  congr 2
  ring

/-- The `ℓ¹` distance `|u − v|₁` of two points of `ℤ²`. -/
def l1Dist (u v : ℤ × ℤ) : ℕ := (u.1 - v.1).natAbs + (u.2 - v.2).natAbs

theorem freeRadius_boxSite {L : ℕ} {u v : ℤ × ℤ} (hu : boxRadius u ≤ L) (hv : boxRadius v ≤ L) :
    Lattice2D.freeRadius (boxSite L u) (boxSite L v) = l1Dist u v := by
  have h₁ := siteToZ_boxSite hu
  have h₂ := siteToZ_boxSite hv
  simp only [siteToZ, Prod.ext_iff, Prod.fst_add, Prod.snd_add] at h₁ h₂
  unfold Lattice2D.freeRadius l1Dist
  obtain ⟨h₁a, h₁b⟩ := h₁
  obtain ⟨h₂a, h₂b⟩ := h₂
  have e1 : (Nat.dist (boxSite L u).1.val (boxSite L v).1.val : ℤ) = |u.1 - v.1| := by
    rw [Nat.dist]
    rcases le_total 0 (u.1 - v.1) with h | h
    · rw [abs_of_nonneg h]; omega
    · rw [abs_of_nonpos h]; omega
  have e2 : (Nat.dist (boxSite L u).2.val (boxSite L v).2.val : ℤ) = |u.2 - v.2| := by
    rw [Nat.dist]
    rcases le_total 0 (u.2 - v.2) with h | h
    · rw [abs_of_nonneg h]; omega
    · rw [abs_of_nonpos h]; omega
  zify
  rw [e1, e2]

/-- **FS81 Theorem 7.1(2) on the centred free boxes** `[-L, L]²` (free boundary condition): the
same bound as `clock_twoPoint_squareBox_le` for every `u, v ∈ [-L, L]²`, with the `ℓ¹` distance
`|u − v|₁`. -/
theorem clock_twoPoint_freeBox_le :
    ∃ c : ℝ, 0 < c ∧ ∀ η : ℝ, 0 < η → ∀ β : ℝ, 0 ≤ β → ∃ n₀ : ℕ, 0 < n₀ ∧
      ∀ N : ℕ, n₀ ≤ N → ∀ (hN : 0 < N) (hβ : 0 ≤ β) (ξ : ℕ), 0 < ξ → ξ < N →
        η ≤ dipoleGap ((ξ : ℝ) / N) → ∀ (L : ℕ) (u v : ℤ × ℤ), boxRadius u ≤ L →
          boxRadius v ≤ L →
          (clockModel N hN β hβ).twoPoint (ξ : ℤ) (freeBox L) u v ≤
            2 * ((l1Dist u v : ℝ) + 1) ^ (-c) := by
  obtain ⟨c, hc, h⟩ := clock_twoPoint_squareBox_le
  refine ⟨c, hc, fun η hη β hβ0 => ?_⟩
  obtain ⟨n₀, hn₀, hN₀⟩ := h η hη β hβ0
  refine ⟨n₀, hn₀, fun N hNn hN hβ ξ hξ0 hξN hηξ L u v hu hv => ?_⟩
  have hsq := hN₀ N hNn hN hβ ξ hξ0 hξN hηξ (2 * L) (boxSite L u) (boxSite L v)
  rw [freeRadius_boxSite hu hv, siteToZ_boxSite hu, siteToZ_boxSite hv] at hsq
  rw [freeBox_eq_translateDomain]
  have ht := (clockModel N hN β hβ).twoPoint_translate (ξ : ℤ) (squareBoxZ (2 * L))
    (u + ((L : ℤ), (L : ℤ))) (v + ((L : ℤ), (L : ℤ))) (-(L : ℤ), -(L : ℤ))
  have hu' : u + ((L : ℤ), (L : ℤ)) + (-(L : ℤ), -(L : ℤ)) = u := by ext <;> simp
  have hv' : v + ((L : ℤ), (L : ℤ)) + (-(L : ℤ), -(L : ℤ)) = v := by ext <;> simp
  rw [hu', hv'] at ht
  rw [ht]
  exact hsq

/-- **FS81 Theorem 7.1(2) for the free thermodynamic limit** (`BKT/Ginibre`): there is an absolute
`c > 0` such that for every `η > 0` and `β ≥ 0` there is `n₀` with: for every `N ≥ n₀` and every
integer harmonic `0 < ξ < N` with `min(ξ/N, 1 − ξ/N) ≥ η`, the infinite-volume free two-point
function of the `ℤ_N` clock satisfies `⟨cos(ξ(θ_u − θ_v))⟩ ≤ 2 (|u − v|₁ + 1)^{−c}` for all
`u, v ∈ ℤ²`. -/
theorem clock_twoPointLimit_le :
    ∃ c : ℝ, 0 < c ∧ ∀ η : ℝ, 0 < η → ∀ β : ℝ, 0 ≤ β → ∃ n₀ : ℕ, 0 < n₀ ∧
      ∀ N : ℕ, n₀ ≤ N → ∀ (hN : 0 < N) (hβ : 0 ≤ β) (ξ : ℕ), 0 < ξ → ξ < N →
        η ≤ dipoleGap ((ξ : ℝ) / N) → ∀ u v : ℤ × ℤ,
          (clockModel N hN β hβ).twoPointLimit (ξ : ℤ) u v ≤
            2 * ((l1Dist u v : ℝ) + 1) ^ (-c) := by
  obtain ⟨c, hc, h⟩ := clock_twoPoint_freeBox_le
  refine ⟨c, hc, fun η hη β hβ0 => ?_⟩
  obtain ⟨n₀, hn₀, hN₀⟩ := h η hη β hβ0
  refine ⟨n₀, hn₀, fun N hNn hN hβ ξ hξ0 hξN hηξ u v => ?_⟩
  refine le_of_tendsto ((clockModel N hN β hβ).tendsto_twoPointLimit (ξ : ℤ) u v) ?_
  filter_upwards [eventually_ge_atTop (max (boxRadius u) (boxRadius v))] with L hL
  exact hN₀ N hNn hN hβ ξ hξ0 hξN hηξ L u v ((le_max_left _ _).trans hL)
    ((le_max_right _ _).trans hL)

end Square

end FroehlichSpencer.BKT.Clock.Compact

end
