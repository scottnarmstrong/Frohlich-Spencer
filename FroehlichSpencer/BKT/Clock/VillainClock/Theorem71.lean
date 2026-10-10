/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Clock.VillainClock.CompactMarkedDomain
public import FroehlichSpencer.BKT.Clock.VillainClock.CompactFejer
public import FroehlichSpencer.BKT.Clock.Compact.Theorem71
import Mathlib.Tactic

/-!
# FS81 Theorem 7.1(2) for the Villain clock

FS81 Remark 4: the methods give Theorem 7.1 for the `ℤ_N` models obtained from the Villain model by
constraining the angles to `ℤ_N`. Part (1) is `Model.lean`. This module proves part (2) by the same
route as the cosine clock (`Clock/Compact/Theorem71.lean`):

1. For each Fejér cutoff `M`, the clock comb is replaced by the Fejér weights, a positive site
   mixture. `villain_markedDomain_bound` bounds each Fejér ratio on the KP square uniformly in `M`,
   under the compact Villain law.
2. `tendsto_villainFejerRatio` identifies the limit `M → ∞` with the Ginibre Villain-clock two-point
   function.

The marked expansion uses the cosine clock cost `β(cosh(u/n) − 1)`, which bounds the Villain shift
ratio. The cost envelope, the wave selection and all constants are therefore those of the cosine
clock: the decay exponent is the same absolute `clockDecay`, and `n₀(β, η)` is the same threshold.

* `villain_twoPoint_squareBox_le`: on the squares `{0, …, L}²`;
* `villain_twoPoint_freeBox_le`: on the centred boxes `[−L, L]²`;
* **`villain_twoPointLimit_le`**: for the free thermodynamic limit of `BKT/Ginibre`.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Clock.VillainClock

open MeasureTheory Filter Topology
open FroehlichSpencer.BKT
open SpinWaves Reduction
open FroehlichSpencer.BKT.Clock.Periodic
open FroehlichSpencer.BKT.Clock.Compact
open FroehlichSpencer.BKT.Generic
open FroehlichSpencer.BKT.Generic.Marked

section Square

open FroehlichSpencer.BKT.Ginibre FroehlichSpencer.BKT.Rotator FroehlichSpencer.BKT.Rotator.Ginibre

/-- **The Fejér-ratio bound on one free square**, uniform in the Fejér cutoff `M`. -/
theorem villain_fejerRatio_le {L : ℕ} (hL : 1 < L + 1) {D₁ D₀ : ℝ} (hD₁ : 1 ≤ D₁)
    (hmono : P21Step .free (L + 1) D₀ → P21Step .free (L + 1) D₁)
    (h21 : P21Step .free (L + 1) D₀) {N : ℕ} (hN : 0 < N) {β : ℝ} (hβ : 0 < β)
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
        ∂villainCompactLaw β N (squareFree (L + 1))) /
      (∫ φ, ∏ v, fejerPolynomial M (φ v - clockOffset N) ∂villainCompactLaw β N (squareFree (L + 1)))
      ≤ 2 * Real.exp (-(lamc * η / (32 * D₁)) *
          Real.logb 2 (latticeDistance .free (L + 1) a b + 1)) := by
  have hMpos : 0 < M := hM
  obtain ⟨hZ, hI⟩ := villain_markedDomain_bound (boundary := .free) hL (Or.inl rfl)
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

/-- **FS81 Theorem 7.1(2) on the free squares** (the Villain `ℤ_N` clock, high harmonics). There is an
absolute `c > 0` such that for every `η > 0` and `β ≥ 0` there is `n₀` with: for every `N ≥ n₀`,
every integer harmonic `0 < ξ < N` with `min(ξ/N, 1 − ξ/N) ≥ η`, every square `{0, …, L}²` and
sites `a, b` of it, the free-boundary Villain-clock two-point function satisfies
`⟨cos(ξ(θ_a − θ_b))⟩ ≤ 2 (|a − b|₁ + 1)^{−c}`. -/
theorem villain_twoPoint_squareBox_le :
    ∃ c : ℝ, 0 < c ∧ ∀ η : ℝ, 0 < η → ∀ β : ℝ, 0 < β → ∃ n₀ : ℕ, 0 < n₀ ∧
      ∀ N : ℕ, n₀ ≤ N → ∀ (hN : 0 < N) (hβ : 0 < β) (ξ : ℕ), 0 < ξ → ξ < N →
        η ≤ dipoleGap ((ξ : ℝ) / N) → ∀ (L : ℕ) (a b : RotatorSpinSite L),
          (model N hN β hβ).twoPoint (ξ : ℤ) (squareBoxZ L) (siteToZ a) (siteToZ b) ≤
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
    have h1 := (model N hN β hβ).twoPoint_le_one (ξ : ℤ) (squareBoxZ L) (siteToZ a)
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
  obtain ⟨hexp, hquad₁⟩ := clock_unmarked_conditions hβ.le hampp hNpos hXe hX8a hW
  have hc : IsCostEnvelope (clockShiftCost β N) ((β + 1) / (N : ℝ) ^ 2)
      ((β + 1) * W ^ 2 / (N : ℝ) ^ 2) W := by
    have hN2pos : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
    refine isCostEnvelope_mono (clockShiftCost_isCostEnvelope hβ.le hN1 hXW) ?_ ?_
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
  have hratio := villain_fejerRatio_le hL hD₁1 hmono (h21 (L + 1) hL).1 hN hβ hc (by positivity)
    hampp (by rw [hW]) (by omega) hexp hquad₁ hquad₂ hamp1 hamp2 hab hξ0 hξN hη hηξ
    (by rw [hlamc]; positivity) hX28 hcost C1 C2 C3
  have hlim := tendsto_villainFejerRatio N L hN hβ ξ a b
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

/-- **FS81 Theorem 7.1(2) on the centred free boxes** `[-L, L]²` (free boundary condition): the
same bound as `villain_twoPoint_squareBox_le` for every `u, v ∈ [-L, L]²`, with the `ℓ¹` distance
`|u − v|₁`. -/
theorem villain_twoPoint_freeBox_le :
    ∃ c : ℝ, 0 < c ∧ ∀ η : ℝ, 0 < η → ∀ β : ℝ, 0 < β → ∃ n₀ : ℕ, 0 < n₀ ∧
      ∀ N : ℕ, n₀ ≤ N → ∀ (hN : 0 < N) (hβ : 0 < β) (ξ : ℕ), 0 < ξ → ξ < N →
        η ≤ dipoleGap ((ξ : ℝ) / N) → ∀ (L : ℕ) (u v : ℤ × ℤ), boxRadius u ≤ L →
          boxRadius v ≤ L →
          (model N hN β hβ).twoPoint (ξ : ℤ) (freeBox L) u v ≤
            2 * ((l1Dist u v : ℝ) + 1) ^ (-c) := by
  obtain ⟨c, hc, h⟩ := villain_twoPoint_squareBox_le
  refine ⟨c, hc, fun η hη β hβ0 => ?_⟩
  obtain ⟨n₀, hn₀, hN₀⟩ := h η hη β hβ0
  refine ⟨n₀, hn₀, fun N hNn hN hβ ξ hξ0 hξN hηξ L u v hu hv => ?_⟩
  have hsq := hN₀ N hNn hN hβ ξ hξ0 hξN hηξ (2 * L) (boxSite L u) (boxSite L v)
  rw [freeRadius_boxSite hu hv, siteToZ_boxSite hu, siteToZ_boxSite hv] at hsq
  rw [freeBox_eq_translateDomain]
  have ht := (model N hN β hβ).twoPoint_translate (ξ : ℤ) (squareBoxZ (2 * L))
    (u + ((L : ℤ), (L : ℤ))) (v + ((L : ℤ), (L : ℤ))) (-(L : ℤ), -(L : ℤ))
  have hu' : u + ((L : ℤ), (L : ℤ)) + (-(L : ℤ), -(L : ℤ)) = u := by ext <;> simp
  have hv' : v + ((L : ℤ), (L : ℤ)) + (-(L : ℤ), -(L : ℤ)) = v := by ext <;> simp
  rw [hu', hv'] at ht
  rw [ht]
  exact hsq

/-- **FS81 Theorem 7.1(2) for the free thermodynamic limit** (`BKT/Ginibre`): there is an absolute
`c > 0` such that for every `η > 0` and `β ≥ 0` there is `n₀` with: for every `N ≥ n₀` and every
integer harmonic `0 < ξ < N` with `min(ξ/N, 1 − ξ/N) ≥ η`, the infinite-volume free two-point
function of the Villain `ℤ_N` clock satisfies `⟨cos(ξ(θ_u − θ_v))⟩ ≤ 2 (|u − v|₁ + 1)^{−c}` for all
`u, v ∈ ℤ²`. -/
theorem villain_twoPointLimit_le :
    ∃ c : ℝ, 0 < c ∧ ∀ η : ℝ, 0 < η → ∀ β : ℝ, 0 < β → ∃ n₀ : ℕ, 0 < n₀ ∧
      ∀ N : ℕ, n₀ ≤ N → ∀ (hN : 0 < N) (hβ : 0 < β) (ξ : ℕ), 0 < ξ → ξ < N →
        η ≤ dipoleGap ((ξ : ℝ) / N) → ∀ u v : ℤ × ℤ,
          (model N hN β hβ).twoPointLimit (ξ : ℤ) u v ≤
            2 * ((l1Dist u v : ℝ) + 1) ^ (-c) := by
  obtain ⟨c, hc, h⟩ := villain_twoPoint_freeBox_le
  refine ⟨c, hc, fun η hη β hβ0 => ?_⟩
  obtain ⟨n₀, hn₀, hN₀⟩ := h η hη β hβ0
  refine ⟨n₀, hn₀, fun N hNn hN hβ ξ hξ0 hξN hηξ u v => ?_⟩
  refine le_of_tendsto ((model N hN β hβ).tendsto_twoPointLimit (ξ : ℤ) u v) ?_
  filter_upwards [eventually_ge_atTop (max (boxRadius u) (boxRadius v))] with L hL
  exact hN₀ N hNn hN hβ ξ hξ0 hξN hηξ L u v ((le_max_left _ _).trans hL)
    ((le_max_right _ _).trans hL)

end Square

end FroehlichSpencer.BKT.Clock.VillainClock

end
