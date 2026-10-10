/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Clock.VillainClock.FourierAlias
public import FroehlichSpencer.BKT.Coulomb.ConditionLambdaTheoremBGeneral
import Mathlib.Tactic
import Mathlib.Order.Filter.AtTopBot.Ring

/-!
# Condition-λ data for the Villain-clock Gaussian alias activity

For fixed inverse temperature `β` and clock order `N`, the Gaussian alias sum is a nonnegative,
even, `N`-periodic activity.

It is bounded by the full Gaussian Fourier-coefficient sum, so it
satisfies Condition λ with `α = ε = 0`.

Its vacancy is at least the zero alias, hence at least one.

The general Condition-λ Theorem B can therefore be specialized to this activity, with constants
independent of `N`.

This module proves the activity and theorem specialization only.

It does not identify the
Villain-clock two-point function with this Coulomb-gas correlation; that finite-volume duality is a
separate obligation.
-/

@[expose] public section

open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Coulomb
open FroehlichSpencer.BKT.Generic.Marked
open Filter Topology

noncomputable section

namespace FroehlichSpencer.BKT.Clock.VillainClock

/-- One real Gaussian Fourier coefficient of the Villain interaction. -/
def gaussianAliasTerm (β : ℝ) (q : ℤ) : ℝ :=
  Real.exp (-((q : ℝ) ^ 2) / (2 * β))

/-- The real Gaussian alias activity at residue `q` modulo the clock order `N`. -/
def gaussianAliasActivity (β : ℝ) (N : ℕ) (q : ℤ) : ℝ :=
  ∑' ell : ℤ, gaussianAliasTerm β (q + (N : ℤ) * ell)

/-- The full Gaussian Fourier-coefficient sum bounding every alias class. -/
def gaussianAliasEnvelope (β : ℝ) : ℝ :=
  ∑' q : ℤ, gaussianAliasTerm β q

/-- The dual Villain inverse temperature for an `N`-clock sample. -/
def gaussianAliasDualTemperature (β : ℝ) (N : ℕ) : ℝ :=
  (N : ℝ) ^ 2 / (4 * Real.pi ^ 2 * β)

/-- The Coulomb energy coefficient corresponding to the dual Villain temperature. -/
def gaussianAliasCoulombCoupling (β : ℝ) (N : ℕ) : ℝ :=
  (N : ℝ) ^ 2 / (2 * β)

theorem gaussianAliasCoulombCoupling_eq_dualScale {β : ℝ} (hβ : 0 < β) (N : ℕ) :
    gaussianAliasCoulombCoupling β N =
      2 * Real.pi ^ 2 * gaussianAliasDualTemperature β N := by
  unfold gaussianAliasCoulombCoupling gaussianAliasDualTemperature
  have hβne : β ≠ 0 := ne_of_gt hβ
  field_simp [hβne]
  ring

theorem gaussianAliasTerm_pos {β : ℝ} (q : ℤ) : 0 < gaussianAliasTerm β q :=
  Real.exp_pos _

theorem gaussianAliasTerm_nonneg {β : ℝ} (q : ℤ) : 0 ≤ gaussianAliasTerm β q :=
  (gaussianAliasTerm_pos q).le

theorem gaussianAliasActivity_summable {β : ℝ} (hβ : 0 < β) {N : ℕ} (hN : 0 < N)
    (q : ℤ) :
    Summable (fun ell : ℤ => gaussianAliasTerm β (q + (N : ℤ) * ell)) := by
  have hbase := VillainWeight.villainWeight_fourier_coeff_summable hβ
  have hNint : (N : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have hinj : Function.Injective (fun ell : ℤ => q + (N : ℤ) * ell) := by
    intro a b hab
    have hmul : (N : ℤ) * a = (N : ℤ) * b := by linarith
    exact mul_left_cancel₀ hNint hmul
  exact hbase.comp_injective hinj

theorem gaussianAliasEnvelope_summable {β : ℝ} (hβ : 0 < β) :
    Summable (gaussianAliasTerm β) := by
  change Summable (fun q : ℤ => Real.exp (-((q : ℝ) ^ 2) / (2 * β)))
  exact VillainWeight.villainWeight_fourier_coeff_summable hβ

theorem gaussianAliasEnvelope_nonneg {β : ℝ} :
    0 ≤ gaussianAliasEnvelope β := by
  exact tsum_nonneg fun q => gaussianAliasTerm_nonneg q

theorem gaussianAliasActivity_nonneg (β : ℝ) (N : ℕ) (q : ℤ) :
    0 ≤ gaussianAliasActivity β N q := by
  exact tsum_nonneg fun ell => gaussianAliasTerm_nonneg _

theorem gaussianAliasActivity_pos {β : ℝ} (hβ : 0 < β) {N : ℕ} (hN : 0 < N)
    (q : ℤ) : 0 < gaussianAliasActivity β N q := by
  unfold gaussianAliasActivity
  exact (gaussianAliasActivity_summable hβ hN q).tsum_pos
    (fun ell => gaussianAliasTerm_nonneg _) 0 (gaussianAliasTerm_pos _)

/-- Every alias class is bounded by the full Gaussian coefficient sum. -/
theorem gaussianAliasActivity_le_envelope {β : ℝ} (hβ : 0 < β) {N : ℕ} (hN : 0 < N)
    (q : ℤ) : gaussianAliasActivity β N q ≤ gaussianAliasEnvelope β := by
  let e : ℤ → ℤ := fun ell => q + (N : ℤ) * ell
  have hNint : (N : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have he : Function.Injective e := by
    intro a b hab
    have hmul : (N : ℤ) * a = (N : ℤ) * b := by dsimp [e] at hab; linarith
    exact mul_left_cancel₀ hNint hmul
  have hfull := gaussianAliasEnvelope_summable hβ
  have halias := hfull.comp_injective he
  have hle := Summable.tsum_le_tsum_of_inj e he
    (fun p _ => gaussianAliasTerm_nonneg (β := β) p) (fun _ => le_rfl) halias hfull
  change (∑' ell : ℤ, gaussianAliasTerm β (q + (N : ℤ) * ell)) ≤
    ∑' p : ℤ, gaussianAliasTerm β p
  exact hle

/-- The alias activity is even, by reindexing the aliases with `ell ↦ -ell`. -/
theorem gaussianAliasActivity_even (β : ℝ) (N : ℕ) (q : ℤ) :
    gaussianAliasActivity β N (-q) = gaussianAliasActivity β N q := by
  let f : ℤ → ℝ := fun ell => gaussianAliasTerm β (q + (N : ℤ) * ell)
  calc
    gaussianAliasActivity β N (-q) = ∑' ell : ℤ, f (-ell) := by
      unfold gaussianAliasActivity
      apply tsum_congr
      intro ell
      dsimp [f, gaussianAliasTerm]
      congr 2
      push_cast
      ring
    _ = gaussianAliasActivity β N q := by
      unfold gaussianAliasActivity
      exact (Equiv.tsum_eq (Equiv.neg ℤ) f)

/-- The alias activity is periodic in the residue modulo `N`. -/
theorem gaussianAliasActivity_add_period (β : ℝ) (N : ℕ) (q k : ℤ) :
    gaussianAliasActivity β N (q + (N : ℤ) * k) = gaussianAliasActivity β N q := by
  let f : ℤ → ℝ := fun ell => gaussianAliasTerm β (q + (N : ℤ) * ell)
  calc
    gaussianAliasActivity β N (q + (N : ℤ) * k) = ∑' ell : ℤ, f (ell + k) := by
      unfold gaussianAliasActivity
      apply tsum_congr
      intro ell
      dsimp [f, gaussianAliasTerm]
      congr 2
      push_cast
      ring
    _ = gaussianAliasActivity β N q := by
      unfold gaussianAliasActivity
      exact Equiv.tsum_eq (Equiv.addRight k) f

/-- The Gaussian alias activity is exactly a Villain weight at the dual temperature. -/
theorem gaussianAliasActivity_eq_dualVillainWeight {β : ℝ} (hβ : 0 < β) {N : ℕ}
    (hN : 0 < N) (q : ℤ) :
    gaussianAliasActivity β N q =
      villainWeight (gaussianAliasDualTemperature β N)
        (2 * Real.pi * (q : ℝ) / N) := by
  unfold gaussianAliasActivity villainWeight
  apply tsum_congr
  intro ell
  unfold gaussianAliasTerm gaussianAliasDualTemperature
  apply congrArg Real.exp
  have hβne : β ≠ 0 := ne_of_gt hβ
  have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  push_cast
  field_simp [hβne, hNne]
  ring

/-- The sampled Fourier coefficient is the alias activity times the common Poisson scalar. -/
theorem gaussianAliasCoefficient_eq_activity (β : ℝ) (N : ℕ) (q : ℤ) :
    gaussianAliasCoefficient β N q =
      (((2 * Real.pi * β) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        (gaussianAliasActivity β N q : ℂ) := by
  have hsum : (gaussianAliasActivity β N q : ℂ) =
      ∑' ell : ℤ, gaussianMode β (q + (N : ℤ) * ell) := by
    rw [gaussianAliasActivity, Complex.ofReal_tsum]
    rfl
  rw [gaussianAliasCoefficient, hsum]

/-- The DFT of sampled Villain weights is, up to the common Poisson scalar, a Villain weight at
the exact dual temperature `N² / (4π²β)`. -/
theorem sampledFourierCoefficient_eq_dualVillain {β : ℝ} (hβ : 0 < β) {N : ℕ}
    (hN : 0 < N) (q : ℤ) :
    sampledFourierCoefficient β N q =
      (((2 * Real.pi * β) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        (villainWeight (gaussianAliasDualTemperature β N)
          (2 * Real.pi * (q : ℝ) / N) : ℂ) := by
  rw [sampledFourierCoefficient_eq_gaussianAlias β hN hβ q,
    gaussianAliasCoefficient_eq_activity β N q,
    gaussianAliasActivity_eq_dualVillainWeight hβ hN q]

/-- The vacancy alias includes the zero Fourier mode, so it is at least one. -/
theorem one_le_gaussianAliasActivity_zero {β : ℝ} (hβ : 0 < β) {N : ℕ}
    (hN : 0 < N) : 1 ≤ gaussianAliasActivity β N 0 := by
  have hs := gaussianAliasActivity_summable hβ hN 0
  have hle := hs.le_tsum 0 (fun ell _ => gaussianAliasTerm_nonneg _)
  have hzero : gaussianAliasTerm β (0 + (N : ℤ) * 0) = 1 := by
    simp [gaussianAliasTerm]
  calc
    1 = gaussianAliasTerm β (0 + (N : ℤ) * 0) := hzero.symm
    _ ≤ gaussianAliasActivity β N 0 := by
      simpa [gaussianAliasActivity] using hle

/-- The Gaussian alias activity satisfies Condition λ with explicit parameters
`(C, α, ε) = (gaussianAliasEnvelope β, 0, 0)`, for every `κ`. -/
theorem gaussianAliasActivity_conditionLambda {β κ : ℝ} (hβ : 0 < β) {N : ℕ}
    (hN : 0 < N) :
  ConditionLambdaInternal (gaussianAliasEnvelope β) 0 0 κ (gaussianAliasActivity β N) := by
  refine ⟨fun q => gaussianAliasActivity_even β N q, fun q => ?_⟩
  rw [abs_of_nonneg (gaussianAliasActivity_nonneg β N q)]
  have hbound := gaussianAliasActivity_le_envelope hβ hN q
  simpa [gaussianAliasEnvelope, gaussianAliasTerm] using hbound

/-- Theorem B applies to each Gaussian alias activity, with the uniform positive vacancy `ν=1`.
This is only a Coulomb-gas estimate for the indicated activity; the Villain-clock correlation
identification is not asserted here. -/
theorem gaussianAliasActivity_conditionLambda_bound :
    ∃ c : ℝ, 0 < c ∧ ∀ β : ℝ, 0 < β → ∀ η : ℝ, 0 < η →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, κ₀ < κ → ∀ N : ℕ, 0 < N →
        ∀ (Λ : Finset (ℤ × ℤ)) (ξ : ℝ) (x y : ℤ × ℤ),
          x ∈ Λ → y ∈ Λ → x ≠ y → 0 < ξ → ξ < 1 → η ≤ dipoleGap ξ →
          0 ≤ regionConditionLambdaFracCorrInternal Λ κ (gaussianAliasActivity β N)
              ξ x y ∧
          regionConditionLambdaFracCorrInternal Λ κ (gaussianAliasActivity β N) ξ x y ≤
            2 * Real.exp ((1 / 4 : ℝ) * κ) *
              ((((y.1 - x.1).natAbs + (y.2 - x.2).natAbs : ℕ) + 1 : ℝ) ^
                (-(c * (1 / 16 : ℝ) * η ^ 2 * κ))) := by
  obtain ⟨c, hc, hB⟩ := Coulomb.coulombB_conditionLambda_free_fullRange_general
  refine ⟨c, hc, fun β hβ η hη => ?_⟩
  obtain ⟨κ₀, hκ₀, hκ⟩ := hB (gaussianAliasEnvelope β) 0 0
    (gaussianAliasEnvelope_nonneg) le_rfl (by norm_num) 1 (by norm_num) η hη
  refine ⟨κ₀, hκ₀, fun κ hκκ₀ N hN Λ ξ x y hx hy hxy hξ0 hξ1 hηξ => ?_⟩
  have hbound := hκ κ hκκ₀ (gaussianAliasActivity β N)
    (gaussianAliasActivity_conditionLambda hβ hN)
    (gaussianAliasActivity_nonneg β N) (one_le_gaussianAliasActivity_zero hβ hN)
    Λ ξ x y hx hy hxy hξ0 hξ1 hηξ
  have hmax : max (0 : ℝ) 0 = 0 := max_self _
  have hpref : 1 / (64 * (1 / 16 - (0 : ℝ))) = 1 / 4 := by norm_num
  have hexp : c * (1 / 16 - (0 : ℝ)) * η ^ 2 * κ = c * (1 / 16 : ℝ) * η ^ 2 * κ := by ring
  simp only [hmax] at hbound
  rw [hpref, hexp] at hbound
  exact hbound

/-- Since the Coulomb coupling is `2π²` times the dual Villain temperature, hence `N²/(2β)`,
Theorem B's threshold is reached for all sufficiently large clock orders. This is the resulting
finite-region bound for the alias Coulomb gas. -/
theorem gaussianAliasActivity_conditionLambda_bound_large_N :
    ∃ c : ℝ, 0 < c ∧ ∀ β : ℝ, 0 < β → ∀ η : ℝ, 0 < η →
      ∃ n₀ : ℕ, 0 < n₀ ∧ ∀ N : ℕ, n₀ ≤ N →
        ∀ (Λ : Finset (ℤ × ℤ)) (ξ : ℝ) (x y : ℤ × ℤ),
          x ∈ Λ → y ∈ Λ → x ≠ y → 0 < ξ → ξ < 1 → η ≤ dipoleGap ξ →
          0 ≤ regionConditionLambdaFracCorrInternal Λ
              (gaussianAliasCoulombCoupling β N) (gaussianAliasActivity β N) ξ x y ∧
          regionConditionLambdaFracCorrInternal Λ
              (gaussianAliasCoulombCoupling β N) (gaussianAliasActivity β N) ξ x y ≤
            2 * Real.exp ((1 / 4 : ℝ) * gaussianAliasCoulombCoupling β N) *
              ((((y.1 - x.1).natAbs + (y.2 - x.2).natAbs : ℕ) + 1 : ℝ) ^
                (-(c * (1 / 16 : ℝ) * η ^ 2 *
                  gaussianAliasCoulombCoupling β N))) := by
  obtain ⟨c, hc, hB⟩ := gaussianAliasActivity_conditionLambda_bound
  refine ⟨c, hc, fun β hβ η hη => ?_⟩
  obtain ⟨κ₀, hκ₀, hκ⟩ := hB β hβ η hη
  have hpow : Tendsto (fun N : ℕ => (N : ℝ) ^ 2) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : 2 ≠ 0)).comp tendsto_natCast_atTop_atTop
  have hscale : 0 < (2 * β)⁻¹ := by positivity
  have hκT : Tendsto (fun N : ℕ => gaussianAliasCoulombCoupling β N) atTop atTop := by
    unfold gaussianAliasCoulombCoupling
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      hpow.const_mul_atTop hscale
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1
    (hκT.eventually_gt_atTop κ₀)
  refine ⟨max 1 N₀, by omega, fun N hN Λ ξ x y hx hy hxy hξ0 hξ1 hηξ => ?_⟩
  have hN₀N : N₀ ≤ N := (le_max_right 1 N₀).trans hN
  have hNpos : 0 < N := by omega
  have hbound := hκ (gaussianAliasCoulombCoupling β N) (hN₀ N hN₀N) N hNpos
    Λ ξ x y hx hy hxy hξ0 hξ1 hηξ
  exact hbound

/-- The general Condition-λ theorem also gives a bound on every limit point of the finite-region
alias-gas correlations. The volume sequence need not be nested, and no convergence is asserted. -/
theorem gaussianAliasActivity_thermodynamicLimit_bound :
    ∃ c : ℝ, 0 < c ∧ ∀ β : ℝ, 0 < β → ∀ η : ℝ, 0 < η →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, κ₀ < κ → ∀ N : ℕ, 0 < N →
        ∀ ξ : ℝ, 0 < ξ → ξ < 1 → η ≤ dipoleGap ξ →
          ∀ x y : ℤ × ℤ, x ≠ y → ∀ Λs : ℕ → Finset (ℤ × ℤ),
            (∀ k, x ∈ Λs k ∧ y ∈ Λs k) →
            (∀ k, 0 ≤ regionConditionLambdaFracCorrInternal (Λs k) κ
                (gaussianAliasActivity β N) ξ x y ∧
              regionConditionLambdaFracCorrInternal (Λs k) κ
                (gaussianAliasActivity β N) ξ x y ≤
                2 * Real.exp ((1 / 4 : ℝ) * κ) *
                  ((((y.1 - x.1).natAbs + (y.2 - x.2).natAbs : ℕ) + 1 : ℝ) ^
                    (-(c * (1 / 16 : ℝ) * η ^ 2 * κ)))) ∧
            (∃ ℓ : ℝ, ∃ φ : ℕ → ℕ, StrictMono φ ∧
              Tendsto (fun k => regionConditionLambdaFracCorrInternal (Λs (φ k)) κ
                (gaussianAliasActivity β N) ξ x y) atTop (𝓝 ℓ)) ∧
            ∀ ℓ : ℝ,
              MapClusterPt ℓ atTop
                (fun k => regionConditionLambdaFracCorrInternal (Λs k) κ
                  (gaussianAliasActivity β N) ξ x y) →
              0 ≤ ℓ ∧ ℓ ≤
                2 * Real.exp ((1 / 4 : ℝ) * κ) *
                  ((((y.1 - x.1).natAbs + (y.2 - x.2).natAbs : ℕ) + 1 : ℝ) ^
                    (-(c * (1 / 16 : ℝ) * η ^ 2 * κ))) := by
  obtain ⟨c, hc, hB⟩ :=
    Coulomb.coulombB_conditionLambda_thermodynamicLimit_fullRange_general
  refine ⟨c, hc, fun β hβ η hη => ?_⟩
  obtain ⟨κ₀, hκ₀, hκ⟩ := hB (gaussianAliasEnvelope β) 0 0
    (gaussianAliasEnvelope_nonneg) le_rfl (by norm_num) 1 (by norm_num) η hη
  refine ⟨κ₀, hκ₀, fun κ hκκ₀ N hN ξ hξ0 hξ1 hηξ x y hxy Λs hΛs => ?_⟩
  have hlim := hκ κ hκκ₀ (gaussianAliasActivity β N)
    (gaussianAliasActivity_conditionLambda hβ hN)
    (gaussianAliasActivity_nonneg β N) (one_le_gaussianAliasActivity_zero hβ hN)
    ξ hξ0 hξ1 hηξ x y hxy Λs hΛs
  have hpref : 1 / (64 * (1 / 16 - (0 : ℝ))) = 1 / 4 := by norm_num
  have hexp : c * (1 / 16 - (0 : ℝ)) * η ^ 2 * κ =
      c * (1 / 16 : ℝ) * η ^ 2 * κ := by ring
  simpa only [max_eq_right (show (0 : ℝ) ≤ 0 by norm_num), hpref, hexp] using hlim

/-- For sufficiently large clock order, every limit point of the alias-gas correlation obeys the
same power bound with Coulomb coupling `N²/(2β)`. -/
theorem gaussianAliasActivity_thermodynamicLimit_bound_large_N :
    ∃ c : ℝ, 0 < c ∧ ∀ β : ℝ, 0 < β → ∀ η : ℝ, 0 < η →
      ∃ n₀ : ℕ, 0 < n₀ ∧ ∀ N : ℕ, n₀ ≤ N →
        ∀ ξ : ℝ, 0 < ξ → ξ < 1 → η ≤ dipoleGap ξ →
          ∀ x y : ℤ × ℤ, x ≠ y → ∀ Λs : ℕ → Finset (ℤ × ℤ),
            (∀ k, x ∈ Λs k ∧ y ∈ Λs k) →
            (∀ k, 0 ≤ regionConditionLambdaFracCorrInternal (Λs k)
                (gaussianAliasCoulombCoupling β N) (gaussianAliasActivity β N) ξ x y ∧
              regionConditionLambdaFracCorrInternal (Λs k)
                (gaussianAliasCoulombCoupling β N) (gaussianAliasActivity β N) ξ x y ≤
                2 * Real.exp ((1 / 4 : ℝ) * gaussianAliasCoulombCoupling β N) *
                  ((((y.1 - x.1).natAbs + (y.2 - x.2).natAbs : ℕ) + 1 : ℝ) ^
                    (-(c * (1 / 16 : ℝ) * η ^ 2 * gaussianAliasCoulombCoupling β N)))) ∧
            (∃ ℓ : ℝ, ∃ φ : ℕ → ℕ, StrictMono φ ∧
              Tendsto (fun k => regionConditionLambdaFracCorrInternal (Λs (φ k))
                (gaussianAliasCoulombCoupling β N) (gaussianAliasActivity β N) ξ x y)
                atTop (𝓝 ℓ)) ∧
            ∀ ℓ : ℝ,
              MapClusterPt ℓ atTop
                (fun k => regionConditionLambdaFracCorrInternal (Λs k)
                  (gaussianAliasCoulombCoupling β N) (gaussianAliasActivity β N) ξ x y) →
              0 ≤ ℓ ∧ ℓ ≤
                2 * Real.exp ((1 / 4 : ℝ) * gaussianAliasCoulombCoupling β N) *
                  ((((y.1 - x.1).natAbs + (y.2 - x.2).natAbs : ℕ) + 1 : ℝ) ^
                    (-(c * (1 / 16 : ℝ) * η ^ 2 * gaussianAliasCoulombCoupling β N))) := by
  obtain ⟨c, hc, hB⟩ := gaussianAliasActivity_thermodynamicLimit_bound
  refine ⟨c, hc, fun β hβ η hη => ?_⟩
  obtain ⟨κ₀, hκ₀, hκ⟩ := hB β hβ η hη
  have hpow : Tendsto (fun N : ℕ => (N : ℝ) ^ 2) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : 2 ≠ 0)).comp tendsto_natCast_atTop_atTop
  have hscale : 0 < (2 * β)⁻¹ := by positivity
  have hκT : Tendsto (fun N : ℕ => gaussianAliasCoulombCoupling β N) atTop atTop := by
    unfold gaussianAliasCoulombCoupling
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      hpow.const_mul_atTop hscale
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1
    (hκT.eventually_gt_atTop κ₀)
  refine ⟨max 1 N₀, by omega, fun N hN ξ hξ0 hξ1 hηξ x y hxy Λs hΛs => ?_⟩
  have hN₀N : N₀ ≤ N := (le_max_right 1 N₀).trans hN
  have hNpos : 0 < N := by omega
  exact hκ (gaussianAliasCoulombCoupling β N) (hN₀ N hN₀N) N hNpos
    ξ hξ0 hξ1 hηξ x y hxy Λs hΛs

end FroehlichSpencer.BKT.Clock.VillainClock

end
