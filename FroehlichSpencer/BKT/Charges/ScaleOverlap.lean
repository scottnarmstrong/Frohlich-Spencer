/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Charges.BasicLemmaRepaired
public import FroehlichSpencer.BKT.Charges.SupportCover
public import FroehlichSpencer.BKT.Charges.SquareDiameterBounds
public import FroehlichSpencer.BKT.Charges.SiteWeightMixture

import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Overlap of separated ensembles with the covering cost, and the site-mode normalization

Also the
normalization bound `2 C(N) ≤ 1` ( and the resulting bound on the site-mode coefficients.
-/

@[expose] public section

namespace FroehlichSpencer.BKT

/--  (KP (4.20) with constant 1): distinct members of a scale-`i` ensemble with supports in
`supp ϱ` have total `A_{i-1}` at most `A_{i-1}(ϱ)`. -/
theorem sum_chargeA_le_of_scaleSeparated (boundary : SquareBoundary) {L : ℕ} (hL : 1 < L)
    (i : ℕ) (P : ChargeEnsemble L) (hP : IsChargeScaleEnsemble boundary P (.ofNat i))
    (ρ : ChargeDensity L) (hsub : ∀ b ∈ P, chargeSupport b ⊆ chargeSupport ρ) :
    ∑ b ∈ P, chargeA boundary L b (basicLemmaPreviousScale i) ≤
      chargeA boundary L ρ (basicLemmaPreviousScale i) := by
  classical
  have hsupp : ∀ b ∈ P, ∀ c ∈ P, b ≠ c → Disjoint (chargeSupport b) (chargeSupport c) := by
    intro b hb c hc hbc
    rw [Finset.disjoint_left]
    intro x hx hx'
    have hdisj := hP.1.2 b hb c hc hbc
    have h1 : x ∈ Function.support b := by simpa [chargeSupport] using hx
    have h2 : x ∈ Function.support c := by simpa [chargeSupport] using hx'
    exact Set.disjoint_left.mp hdisj h1 h2
  have hcardcase : ∑ b ∈ P, (chargeSupport b).card ≤ (chargeSupport ρ).card := by
    rw [← Finset.card_biUnion hsupp]
    exact Finset.card_le_card (Finset.biUnion_subset.mpr hsub)
  rcases i with _ | _ | m
  · exact hcardcase
  · exact hcardcase
  · show ∑ b ∈ P, squareCoverNumber boundary L (m + 1) b ≤ squareCoverNumber boundary L (m + 1) ρ
    obtain ⟨C, hC, hCcard⟩ := exists_squareCover_attaining_number boundary L (m + 1) ρ
    have hdiam : ∀ s ∈ C, squareDiameter boundary L s ≤
        ChargeScale.separationThreshold (.ofNat (m + 2)) := by
      intro s hs
      have hs' := hC.1 hs
      have h2 : squareDiameter boundary L s ≤ 2 * (squareSide (m + 1) - 1) := by
        cases boundary with
        | free => exact free_squareDiameter_le_all L (m + 1) s hs'
        | periodic => exact periodic_squareDiameter_le L (m + 1) hL s hs'
      have : squareSide (m + 1) = 2 ^ (m + 1) := rfl
      have hpos : 1 ≤ 2 ^ (m + 1) := Nat.one_le_two_pow
      simp only [ChargeScale.separationThreshold]
      rw [pow_succ] at *
      omega
    let Cb : ChargeDensity L → Finset (Finset (Fin L × Fin L)) := fun b =>
      C.filter (fun s => ∃ x ∈ chargeSupport b, x ∈ s)
    have hle : ∀ b ∈ P, squareCoverNumber boundary L (m + 1) b ≤ (Cb b).card := by
      intro b hb
      refine squareCoverNumber_le boundary L (m + 1) b _ ⟨?_, ?_⟩
      · exact (Finset.filter_subset _ _).trans hC.1
      · intro x hx
        obtain ⟨s, hs, hxs⟩ := hC.2 x (hsub b hb hx)
        exact ⟨s, Finset.mem_filter.mpr ⟨hs, x, hx, hxs⟩, hxs⟩
    have hdisj : ∀ b ∈ P, ∀ c ∈ P, b ≠ c → Disjoint (Cb b) (Cb c) := by
      intro b hb c hc hbc
      rw [Finset.disjoint_left]
      intro s hsb hsc
      have hsC := (Finset.mem_filter.mp hsb).1
      have hone := atMostOne_chargeSupport_meets_cell boundary (.ofNat (m + 2)) P hP s
        (hdiam s hsC)
      have hbmem : b ∈ P.filter (fun ρ => ∃ x ∈ chargeSupport ρ, x ∈ s) :=
        Finset.mem_filter.mpr ⟨hb, (Finset.mem_filter.mp hsb).2⟩
      have hcmem : c ∈ P.filter (fun ρ => ∃ x ∈ chargeSupport ρ, x ∈ s) :=
        Finset.mem_filter.mpr ⟨hc, (Finset.mem_filter.mp hsc).2⟩
      exact hbc (Finset.card_le_one.mp hone b hbmem c hcmem)
    calc ∑ b ∈ P, squareCoverNumber boundary L (m + 1) b ≤ ∑ b ∈ P, (Cb b).card :=
          Finset.sum_le_sum hle
      _ = (P.biUnion Cb).card := (Finset.card_biUnion hdisj).symm
      _ ≤ C.card := Finset.card_le_card
          (Finset.biUnion_subset.mpr fun b _ => Finset.filter_subset _ _)
      _ = _ := hCcard

private theorem sum_exp_neg_sq_le (N : ℕ) :
    ∑ q ∈ Finset.Icc 1 N, Real.exp (-((q : ℝ) ^ 2)) ≤
      Real.exp (-1) / (1 - Real.exp (-1) ^ 2) * (1 - (Real.exp (-1) ^ 2) ^ N) := by
  have ht0 : 0 < Real.exp (-1) := Real.exp_pos _
  have ht1 : Real.exp (-1) < 1 := by
    rw [Real.exp_lt_one_iff]; norm_num
  have hden : 0 < 1 - Real.exp (-1) ^ 2 := by nlinarith
  induction N with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by omega)]
      have hstep : Real.exp (-(((n + 1 : ℕ) : ℝ) ^ 2)) ≤ Real.exp (-1) ^ (2 * n + 1) := by
        rw [← Real.exp_nat_mul]
        apply Real.exp_le_exp.mpr
        push_cast
        nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      have heq : Real.exp (-1) / (1 - Real.exp (-1) ^ 2) * (1 - (Real.exp (-1) ^ 2) ^ (n + 1)) =
          Real.exp (-1) / (1 - Real.exp (-1) ^ 2) * (1 - (Real.exp (-1) ^ 2) ^ n) +
            Real.exp (-1) ^ (2 * n + 1) := by
        field_simp
        ring
      rw [heq]
      linarith

/-- `2 C(N) ≤ 1` for `C(N) = ∑_{q=1}^N e^{-q²}` (: `C(N) ≤ e/(e²−1) < 1/2`). -/
theorem two_mul_siteModeNormalization_le_one (N : ℕ) : 2 * siteModeNormalization N ≤ 1 := by
  have ht0 : 0 < Real.exp (-1) := Real.exp_pos _
  have ht : Real.exp (-1) < 2 / 5 := by
    have h := Real.exp_one_gt_d9
    rw [Real.exp_neg, inv_lt_comm₀ (Real.exp_pos 1) (by norm_num)]
    linarith
  have hden : 0 < 1 - Real.exp (-1) ^ 2 := by nlinarith
  have hsum : siteModeNormalization N = ∑ q ∈ Finset.Icc 1 N, Real.exp (-((q : ℝ) ^ 2)) :=
    Finset.sum_coe_sort (Finset.Icc 1 N) fun q => Real.exp (-((q : ℝ) ^ 2))
  have h1 := sum_exp_neg_sq_le N
  have hr : 0 ≤ (Real.exp (-1) ^ 2) ^ N := by positivity
  have hfrac : Real.exp (-1) / (1 - Real.exp (-1) ^ 2) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hden (by norm_num)]
    nlinarith
  have h2 : Real.exp (-1) / (1 - Real.exp (-1) ^ 2) * (1 - (Real.exp (-1) ^ 2) ^ N) ≤
      Real.exp (-1) / (1 - Real.exp (-1) ^ 2) := by
    have : 0 ≤ Real.exp (-1) / (1 - Real.exp (-1) ^ 2) := by positivity
    nlinarith
  rw [hsum]
  linarith

theorem abs_siteModeCoefficient_le (N : ℕ) (hat : ℕ → ℝ) (q : SiteMode N) :
    |siteModeCoefficient N hat q| ≤ Real.exp ((q.1 : ℝ) ^ 2) * |hat q.1| := by
  have hC : 0 ≤ siteModeNormalization N :=
    Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le
  have h2 := two_mul_siteModeNormalization_le_one N
  unfold siteModeCoefficient
  rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2),
    abs_of_nonneg hC, abs_of_pos (Real.exp_pos _)]
  have hnn : 0 ≤ Real.exp ((q.1 : ℝ) ^ 2) * |hat q.1| := by positivity
  nlinarith

end FroehlichSpencer.BKT

end
