/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Rotator.TheoremC.Defs
public import FroehlichSpencer.BKT.Generic.PinnedCharges.SelectionGExpansion

/-!
`dirichletComb N ψ = 1 + 2 ∑_{q=1}^N cos(qψ)` is a convex combination of the single-charge factors
`1 + K_q cos(qψ)` with weights `w_q = 2^{-q}/Z_N` (`Z_N = ∑_{q=1}^N 2^{-q} ≤ 1`) and coefficients
`K_q = 2/w_q = 2 Z_N 2^q ≤ 2^{q+1}`, uniformly in the cutoff `N` (`dirichletComb_eq_mixture`).

Over the box, `∏_x dirichletComb N (φ x)` is the convex combination, over charge assignments
`f : Site L → [1, N]`, of the charge-factor products of the single-site ensembles
`{f x δ_x : x}` with the one coefficient function `combActivity N ρ = 2 Z_N 2^{‖ρ‖₁}`
(`prod_dirichletComb_eq`).
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic.PinnedCharges.Layer

open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Rotator.TheoremC

variable {L : ℕ}

/-- The normalizer `Z_N = ∑_{q=1}^N 2^{-q}`. -/
def combNorm (N : ℕ) : ℝ := ∑ q ∈ Finset.Icc 1 N, (1 / 2 : ℝ) ^ q

/-- The mixture weight of frequency `q`. -/
def combWeight (N q : ℕ) : ℝ := (1 / 2 : ℝ) ^ q / combNorm N

/-- The mixture coefficient of frequency `n`: `2 Z_N 2^n`. -/
def combCoeff (N n : ℕ) : ℝ := 2 * combNorm N * 2 ^ n

theorem combNorm_eq (N : ℕ) : combNorm N = 1 - (1 / 2 : ℝ) ^ N := by
  induction N with
  | zero => simp [combNorm]
  | succ n ih =>
    unfold combNorm at ih ⊢
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    ring

theorem combNorm_pos {N : ℕ} (hN : 1 ≤ N) : 0 < combNorm N := by
  rw [combNorm_eq]
  have : (1 / 2 : ℝ) ^ N ≤ 1 / 2 := by
    calc (1 / 2 : ℝ) ^ N ≤ (1 / 2) ^ 1 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hN
      _ = 1 / 2 := by norm_num
  linarith

theorem combNorm_le_one (N : ℕ) : combNorm N ≤ 1 := by
  rw [combNorm_eq]
  have : (0 : ℝ) ≤ (1 / 2) ^ N := by positivity
  linarith

theorem combWeight_pos {N : ℕ} (hN : 1 ≤ N) (q : ℕ) : 0 < combWeight N q :=
  div_pos (by positivity) (combNorm_pos hN)

theorem sum_combWeight {N : ℕ} (hN : 1 ≤ N) : ∑ q ∈ Finset.Icc 1 N, combWeight N q = 1 := by
  unfold combWeight
  rw [← Finset.sum_div]
  exact div_self (combNorm_pos hN).ne'

theorem combCoeff_pos {N : ℕ} (hN : 1 ≤ N) (n : ℕ) : 0 < combCoeff N n := by
  have := combNorm_pos hN
  unfold combCoeff
  positivity

theorem combCoeff_le (N n : ℕ) : combCoeff N n ≤ 2 ^ (n + 1) := by
  unfold combCoeff
  have h1 := combNorm_le_one N
  have h2 : (0 : ℝ) ≤ 2 ^ n := by positivity
  rw [pow_succ]
  nlinarith

theorem combWeight_mul_combCoeff {N : ℕ} (hN : 1 ≤ N) (q : ℕ) :
    combWeight N q * combCoeff N q = 2 := by
  unfold combWeight combCoeff
  have hZ := (combNorm_pos hN).ne'
  have hq : (1 / 2 : ℝ) ^ q * 2 ^ q = 1 := by
    rw [← mul_pow]
    norm_num
  calc (1 / 2 : ℝ) ^ q / combNorm N * (2 * combNorm N * 2 ^ q)
      = 2 * ((1 / 2 : ℝ) ^ q * 2 ^ q) * (combNorm N / combNorm N) := by ring
    _ = 2 := by rw [hq, div_self hZ]; ring

/-- **The comb as a single-charge mixture**, with coefficients uniform in `N`. -/
theorem dirichletComb_eq_mixture {N : ℕ} (hN : 1 ≤ N) (ψ : ℝ) :
    dirichletComb N ψ =
      ∑ q ∈ Finset.Icc 1 N, combWeight N q * (1 + combCoeff N q * Real.cos (q * ψ)) := by
  simp only [mul_add, mul_one, Finset.sum_add_distrib, sum_combWeight hN, ← mul_assoc,
    combWeight_mul_combCoeff hN]
  rw [dirichletComb, ← Finset.mul_sum]

/-! ### Single-site ensembles -/

/-- The single charge `f x` at the site `x`. -/
def siteCharge (f : Site L → ℕ) (x : Site L) : ChargeDensity L := Pi.single x (f x : ℤ)

/-- The single-site ensemble of a charge assignment. -/
def singleSiteEnsemble (f : Site L → ℕ) : Finset (ChargeDensity L) :=
  Finset.univ.image (siteCharge f)

/-- The comb coefficient as a function of the density: `2 Z_N 2^{‖ρ‖₁}`. -/
def combActivity (N : ℕ) (ρ : ChargeDensity L) : ℝ := 2 * combNorm N * 2 ^ (∑ x, (ρ x).natAbs)

theorem siteCharge_apply (f : Site L → ℕ) (x y : Site L) :
    siteCharge f x y = if y = x then (f x : ℤ) else 0 := by
  simp [siteCharge, Pi.single_apply]

theorem chargeSupport_siteCharge {f : Site L → ℕ} (hf : ∀ x, 1 ≤ f x) (x : Site L) :
    chargeSupport (siteCharge f x) = {x} := by
  ext y
  have := hf x
  by_cases h : y = x
  · subst h
    simp [chargeSupport, siteCharge_apply]
    omega
  · simp [chargeSupport, siteCharge_apply, h]

theorem siteCharge_injective {f : Site L → ℕ} (hf : ∀ x, 1 ≤ f x) :
    Function.Injective (siteCharge f) := by
  intro x y hxy
  have h := congrArg chargeSupport hxy
  rw [chargeSupport_siteCharge hf, chargeSupport_siteCharge hf] at h
  exact Finset.singleton_injective h

theorem combActivity_siteCharge (N : ℕ) (f : Site L → ℕ) (x : Site L) :
    combActivity N (siteCharge f x) = combCoeff N (f x) := by
  unfold combActivity combCoeff
  congr 2
  rw [Finset.sum_eq_single x (fun y _ hy => by simp [siteCharge_apply, hy]) (by simp)]
  simp [siteCharge_apply]

theorem chargePhase_siteCharge (φ : Site L → ℝ) (f : Site L → ℕ) (x : Site L) :
    chargePhase φ (siteCharge f x) = (f x : ℝ) * φ x := by
  unfold chargePhase
  rw [Finset.sum_eq_single x (fun y _ hy => by simp [siteCharge_apply, hy]) (by simp)]
  simp [siteCharge_apply, mul_comm]

theorem singleSiteEnsemble_pinned {f : Site L → ℕ} (hf : ∀ x, 1 ≤ f x) :
    IsPinnedChargeEnsemble (singleSiteEnsemble f) := by
  refine ⟨fun ρ hρ => ?_, fun ρ hρ σ hσ hne => ?_⟩
  · obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hρ
    intro h0
    have := chargeSupport_siteCharge hf x
    rw [h0] at this
    have hx : x ∈ chargeSupport (0 : ChargeDensity L) := by rw [this]; exact Finset.mem_singleton_self x
    simp [chargeSupport] at hx
  · obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hρ
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hσ
    rw [chargeSupport_siteCharge hf, chargeSupport_siteCharge hf, Finset.disjoint_singleton]
    exact fun h => hne (h ▸ rfl)

theorem singleSiteEnsemble_card_support {f : Site L → ℕ} (hf : ∀ x, 1 ≤ f x) :
    ∀ ρ ∈ singleSiteEnsemble f, (chargeSupport ρ).card = 1 := by
  intro ρ hρ
  obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hρ
  rw [chargeSupport_siteCharge hf]
  rfl

theorem prod_singleSite_eq {f : Site L → ℕ} (hf : ∀ x, 1 ≤ f x) (N : ℕ) (φ : Site L → ℝ) :
    ∏ x, (1 + combCoeff N (f x) * Real.cos ((f x : ℝ) * φ x)) =
      chargeFactorProduct (singleSiteEnsemble f) (combActivity N) φ := by
  unfold chargeFactorProduct singleSiteEnsemble
  rw [Finset.prod_image fun x _ y _ h => siteCharge_injective hf h]
  refine Finset.prod_congr rfl fun x _ => ?_
  rw [chargeFactor, combActivity_siteCharge, chargePhase_siteCharge]

/-- **The box comb** as a convex combination over charge assignments of single-site ensembles. -/
theorem prod_dirichletComb_eq {N : ℕ} (hN : 1 ≤ N) (φ : Site L → ℝ) :
    ∏ x, dirichletComb N (φ x) =
      ∑ f ∈ Fintype.piFinset (fun _ : Site L => Finset.Icc 1 N),
        (∏ x, combWeight N (f x)) *
          chargeFactorProduct (singleSiteEnsemble f) (combActivity N) φ := by
  simp_rw [dirichletComb_eq_mixture hN]
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun f hf => ?_
  have hf1 : ∀ x, 1 ≤ f x := fun x => (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hf x)).1
  rw [Finset.prod_mul_distrib, ← prod_singleSite_eq hf1]

end FroehlichSpencer.BKT.Generic.PinnedCharges.Layer

end
