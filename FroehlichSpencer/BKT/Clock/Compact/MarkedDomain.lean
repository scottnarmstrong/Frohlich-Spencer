/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Clock.Compact.MarkedBranch
public import FroehlichSpencer.BKT.Generic.Marked.Domain
import Mathlib.Tactic

/-!
# The marked bound on one square domain under the clock law

The renormalized
activities of the clock are **linear** in the charges (`e^{−s(∑|m| + log₂(d+1))}`), not quadratic,
so the exploration weights, the neighbour count and the composite mass are taken in linear form.

* `sum_abs_markedDensity_ge`: `∑|ρ| ≥ (η/2)(|X| + ∑_C ∑|m|)`.
* `linMemberWeight`, `linExplorationWeight`, and `sum_linNeighbourWeight_le` (the linear packing
  count).
* `linCluster_estimate`: one neutral cluster, against the exploration weight.
* `clock_renormalizedActivity_le`: the clock renormalized activity is at most the linear member
  weight.
* **`clock_markedDomain_bound`**: for site weights given by a positive mixture with leaves
  `≤ e^{hq}`, on the KP squares, under the clock law,
  `|∫ cos((ξ/n)(φ_o − φ_x)) ∏ λ_j dμ| ≤ 2 e^{−(λ_c η/(32 D₁)) log₂(|o − x| + 1)} ∫ ∏ λ_j dμ`.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Clock.Compact

open MeasureTheory
open SpinWaves SpinWaves.P47 Reduction
open FroehlichSpencer.BKT.Clock.Periodic
open FroehlichSpencer.BKT.Generic
open FroehlichSpencer.BKT.Generic.Marked

/-! ### The linear mass of the marked composite -/

section Mass

variable {L : ℕ}

/-- With pairwise disjoint member supports, `|ϱ^𝒩(j)| = ∑_{m ∈ C} |m(j)|`. -/
theorem satellite_abs {C T : Finset (ChargeDensity L)} (hT : T ⊆ C)
    (hdisj : ∀ m ∈ C, ∀ m' ∈ C, m ≠ m' → Disjoint (Function.support m) (Function.support m'))
    (j : Fin L × Fin L) :
    |((satellite L C T j : ℤ) : ℝ)| = ∑ m ∈ C, |((m j : ℤ) : ℝ)| := by
  classical
  by_cases h : ∃ m ∈ C, m j ≠ 0
  · obtain ⟨m₀, hm₀, hj⟩ := h
    have hother : ∀ m ∈ C, m ≠ m₀ → m j = 0 := fun m hm hne => by
      by_contra h'
      exact Set.disjoint_left.1 (hdisj m hm m₀ hm₀ hne) h' hj
    have hsum : ∀ U ⊆ C, ∑ m ∈ U, m j = if m₀ ∈ U then m₀ j else 0 := by
      intro U hU
      rw [Finset.sum_congr rfl fun m hm => (show m j = if m = m₀ then m₀ j else 0 by
        split_ifs with h
        · rw [h]
        · exact hother m (hU hm) h), Finset.sum_ite_eq']
    have hsat : satellite L C T j = (if m₀ ∈ T then m₀ j else 0) -
        (if m₀ ∈ C \ T then m₀ j else 0) := by
      unfold satellite
      rw [hsum T hT, hsum (C \ T) Finset.sdiff_subset]
    rw [Finset.sum_eq_single_of_mem m₀ hm₀ fun m hm hne => by
      rw [hother m hm hne, Int.cast_zero, abs_zero], hsat]
    by_cases hmT : m₀ ∈ T
    · rw [ite_eq_left hmT, ite_eq_right fun h => (Finset.mem_sdiff.1 h).2 hmT, sub_zero]
    · rw [ite_eq_right hmT, ite_eq_left (Finset.mem_sdiff.2 ⟨hm₀, hmT⟩)]
      push_cast
      rw [zero_sub, abs_neg]
  · push Not at h
    have hsat : satellite L C T j = 0 := by
      unfold satellite
      rw [Finset.sum_eq_zero fun m hm => h m (hT hm),
        Finset.sum_eq_zero fun m hm => h m (Finset.mem_sdiff.1 hm).1, sub_zero]
    rw [hsat, Finset.sum_eq_zero fun m hm => by rw [h m hm, Int.cast_zero, abs_zero]]
    simp

/-- **The linear mass of the dipole composite**: for `0 < ξ < 1`, `0 ≤ η ≤ min(ξ, 1 − ξ)` and a
cluster with pairwise disjoint member supports,
`∑_j |ξ(δ_o − δ_x)(j) + ϱ^𝒩(j)| ≥ (η/2)(|X| + ∑_{m ∈ C} ∑_j |m(j)|)`, `X = supp ϱ₀ ∪ ⋃ C`. -/
theorem sum_abs_markedDensity_ge {o x : Fin L × Fin L} (hox : o ≠ x) {ξ η : ℝ} (hξ0 : 0 < ξ)
    (hξ1 : ξ < 1) (hη : 0 ≤ η) (hηξ : η ≤ dipoleGap ξ) {C T : Finset (ChargeDensity L)}
    (hT : T ⊆ C)
    (hdisj : ∀ m ∈ C, ∀ m' ∈ C, m ≠ m' →
      Disjoint (Function.support m) (Function.support m')) :
    η / 2 * ((markedSupport L (dipoleMark o x) C).card +
        ∑ m ∈ C, ∑ j, |((m j : ℤ) : ℝ)|) ≤
      ∑ j, |markedDensity ξ (dipoleMark o x) (satellite L C T) j| := by
  classical
  set X := markedSupport L (dipoleMark o x) C with hX
  have hηh : η ≤ 1 / 2 := hηξ.trans (dipoleGap_le_half ξ)
  have hη1 : η ≤ 1 - ξ := hηξ.trans (min_le_right _ _)
  have hcard : (X.card : ℝ) = ∑ j, (if j ∈ X then (1 : ℝ) else 0) := by
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one]
  have habs : ∑ m ∈ C, ∑ j, |((m j : ℤ) : ℝ)| = ∑ j, |((satellite L C T j : ℤ) : ℝ)| := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => (satellite_abs hT hdisj j).symm
  rw [hcard, habs, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  set s : ℝ := ((satellite L C T j : ℤ) : ℝ) with hs
  have hρ : markedDensity ξ (dipoleMark o x) (satellite L C T) j =
      ξ * (dipoleMark o x j : ℝ) + s := rfl
  rw [hρ]
  have hsint : s = 0 ∨ 1 ≤ |s| := by
    by_cases h0 : satellite L C T j = 0
    · left; rw [hs, h0, Int.cast_zero]
    · right; rw [hs, ← Int.cast_abs]; exact_mod_cast Int.one_le_abs h0
  by_cases hjX : j ∈ X
  · rw [ite_eq_left hjX]
    by_cases hm0 : dipoleMark o x j = 0
    · rw [hm0, Int.cast_zero, mul_zero, zero_add]
      obtain ⟨m, hmC, hmj⟩ := (mem_markedSupport.1 hjX).resolve_left (by simpa using hm0)
      have hs1 : (1 : ℝ) ≤ |s| := by
        rw [hs, satellite_abs hT hdisj j]
        have h1 : (1 : ℝ) ≤ |((m j : ℤ) : ℝ)| := by
          rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hmj
        exact h1.trans (Finset.single_le_sum (fun m _ => abs_nonneg ((m j : ℤ) : ℝ)) hmC)
      nlinarith
    · have hk : dipoleMark o x j = 1 ∨ dipoleMark o x j = -1 := by
        unfold dipoleMark at hm0 ⊢
        by_cases hjo : j = o
        · subst hjo
          simp [hox]
        · by_cases hjx : j = x
          · subst hjx
            simp [hjo]
          · simp [hjo, hjx] at hm0
      have hg := (isGapped_mul_add_int (ξ := ξ) hk (satellite L C T j)).le_abs
      rw [mul_comm] at hg
      have hgap : η ≤ |ξ * (dipoleMark o x j : ℝ) + s| := hηξ.trans hg
      have hk' : |ξ * (dipoleMark o x j : ℝ)| = ξ := by
        rcases hk with h | h <;> simp [h, abs_of_pos hξ0]
      have hlow : |s| - ξ ≤ |ξ * (dipoleMark o x j : ℝ) + s| := by
        have h2 := abs_add_le (ξ * (dipoleMark o x j : ℝ) + s) (-(ξ * (dipoleMark o x j : ℝ)))
        rw [abs_neg, show ξ * (dipoleMark o x j : ℝ) + s + -(ξ * (dipoleMark o x j : ℝ)) = s by
          ring, hk'] at h2
        linarith
      rcases hsint with h0 | h1
      · have hs0 : |s| = 0 := by rw [h0, abs_zero]
        rw [hs0]
        nlinarith
      · have : η * |s| ≤ |ξ * (dipoleMark o x j : ℝ) + s| := by nlinarith
        nlinarith
  · rw [ite_eq_right hjX]
    have hm0 : dipoleMark o x j = 0 := by
      by_contra h
      exact hjX (chargeSupport_subset_markedSupport _ C (mem_chargeSupport'.2 h))
    have hs0 : s = 0 := by
      rw [hs]
      have : satellite L C T j = 0 := by
        unfold satellite
        have hzero : ∀ m ∈ C, m j = 0 := fun m hm => by
          by_contra h
          exact hjX (chargeSupport_subset_markedSupport_of_mem hm (mem_chargeSupport'.2 h))
        rw [Finset.sum_eq_zero fun m hm => hzero m (hT hm),
          Finset.sum_eq_zero fun m hm => hzero m (Finset.mem_sdiff.1 hm).1, sub_zero]
      rw [this, Int.cast_zero]
    rw [hm0, hs0]
    simp

end Mass

/-! ### The linear member and exploration weights -/

section Weights

variable (boundary : SquareBoundary) {L : ℕ}

/-- The linear member weight `θ_m = e^{-s(∑_j |m(j)| + log₂(d(m) + 1))}`, a bound on the clock
renormalized activity of a neutral member (the linear gain of the compact cost). -/
def linMemberWeight (s : ℝ) (m : ChargeDensity L) : ℝ :=
  Real.exp (-s * (∑ j, |(m j : ℝ)| + Real.logb 2 (chargeDiameter boundary L m + 1)))

/-- The exploration weight: `θ_m` for neutral members, `1/2` for the (at most one) charged one. -/
def linExplorationWeight (s : ℝ) (m : ChargeDensity L) : ℝ :=
  if ∑ j, m j = 0 then linMemberWeight boundary s m else 1 / 2

variable {boundary}

theorem linMemberWeight_pos (s : ℝ) (m : ChargeDensity L) :
    0 < linMemberWeight boundary s m :=
  Real.exp_pos _

theorem one_le_sum_abs_of_ne_zero {m : ChargeDensity L} (hm : m ≠ 0) :
    (1 : ℝ) ≤ ∑ j, |(m j : ℝ)| := by
  obtain ⟨j₀, hj₀⟩ : ∃ j, m j ≠ 0 := by
    by_contra h
    push Not at h
    exact hm (funext h)
  have h1 : (1 : ℝ) ≤ |(m j₀ : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hj₀
  exact h1.trans (Finset.single_le_sum (fun j _ => abs_nonneg (m j : ℝ)) (Finset.mem_univ j₀))

theorem linMemberWeight_le {s : ℝ} (hs : 0 < s) {m : ChargeDensity L} (hm : m ≠ 0) :
    linMemberWeight boundary s m ≤ Real.exp (-s) := by
  have h1 := one_le_sum_abs_of_ne_zero hm
  have hl : 0 ≤ Real.logb 2 (chargeDiameter boundary L m + 1) :=
    Real.logb_nonneg (by norm_num) (by
      have := (chargeDiameter boundary L m).cast_nonneg (α := ℝ)
      linarith)
  unfold linMemberWeight
  refine Real.exp_le_exp.2 ?_
  nlinarith

/-- Step 2 (generic in the weights): the factors dropped from the branch normalizer are those of
`C` and of its neutral neighbours. -/
theorem cluster_dropped_le' {θ : ChargeDensity L → ℝ} {N C R : Finset (ChargeDensity L)}
    (hθ0 : ∀ m, 0 < θ m) (hθ1 : ∀ m ∈ N, θ m ≤ 1) (hCN : C ⊆ N) :
    (∏ m ∈ C, (1 - θ m)) * ∏ m ∈ (N \ (C ∪ R)).filter (fun m => ∑ j, m j = 0), (1 - θ m) ≤
      ∏ m ∈ neutralPart N \ neutralPart R, (1 - θ m) := by
  classical
  set Bd := (N \ (C ∪ R)).filter (fun m => ∑ j, m j = 0) with hBd
  have hBdC : Disjoint C Bd := by
    rw [Finset.disjoint_left]
    intro m hmC hmB
    exact (Finset.mem_sdiff.1 (Finset.mem_filter.1 hmB).1).2 (Finset.mem_union_left _ hmC)
  have hsub : neutralPart N \ neutralPart R ⊆ C ∪ Bd := by
    intro m hm
    obtain ⟨hmN₀, hmR₀⟩ := Finset.mem_sdiff.1 hm
    obtain ⟨hmN, hmn⟩ := mem_neutralPart.1 hmN₀
    by_cases hmC : m ∈ C
    · exact Finset.mem_union_left _ hmC
    · refine Finset.mem_union_right _ (Finset.mem_filter.2 ⟨Finset.mem_sdiff.2 ⟨hmN, ?_⟩, hmn⟩)
      intro hmCR
      rcases Finset.mem_union.1 hmCR with h' | h'
      · exact hmC h'
      · exact hmR₀ (mem_neutralPart.2 ⟨h', hmn⟩)
  have hmemN : ∀ m ∈ C ∪ Bd, m ∈ N := by
    intro m hm
    rcases Finset.mem_union.1 hm with h' | h'
    · exact hCN h'
    · exact (Finset.mem_sdiff.1 (Finset.mem_filter.1 h').1).1
  rw [← Finset.prod_union hBdC, ← Finset.prod_sdiff hsub]
  have h1 : ∏ m ∈ (C ∪ Bd) \ (neutralPart N \ neutralPart R), (1 - θ m) ≤ 1 :=
    Finset.prod_le_one₀ (fun m hm => by
      have := hθ1 m (hmemN m (Finset.mem_sdiff.1 hm).1); linarith)
      fun m _ => by have := hθ0 m; linarith
  have h2 : 0 ≤ ∏ m ∈ neutralPart N \ neutralPart R, (1 - θ m) :=
    Finset.prod_nonneg fun m hm => by
      have := hθ1 m (mem_neutralPart.1 (Finset.mem_sdiff.1 hm).1).1; linarith
  calc (∏ m ∈ (C ∪ Bd) \ (neutralPart N \ neutralPart R), (1 - θ m)) *
        ∏ m ∈ neutralPart N \ neutralPart R, (1 - θ m)
      ≤ 1 * ∏ m ∈ neutralPart N \ neutralPart R, (1 - θ m) :=
        mul_le_mul_of_nonneg_right h1 h2
    _ = _ := one_mul _

/-- Step 3: the linear exploration weight of a neutral cluster is at least
`∏_C θ · ½ ∏_{Bd} (1 − θ)`. -/
theorem linCluster_exploration_ge {s : ℝ} {N C R : Finset (ChargeDensity L)}
    (hNa : AtMostOneNonNeutral N) (hθ1 : ∀ m ∈ N, linMemberWeight boundary s m ≤ 1)
    (hCn : ∀ m ∈ C, ∑ j, m j = 0) :
    (∏ m ∈ C, linMemberWeight boundary s m) *
        (1 / 2 * ∏ m ∈ (N \ (C ∪ R)).filter (fun m => ∑ j, m j = 0),
          (1 - linMemberWeight boundary s m)) ≤
      (∏ m ∈ C, linExplorationWeight boundary s m) *
        ∏ m ∈ N \ (C ∪ R), (1 - linExplorationWeight boundary s m) := by
  classical
  have hπC : ∏ m ∈ C, linExplorationWeight boundary s m =
      ∏ m ∈ C, linMemberWeight boundary s m :=
    Finset.prod_congr rfl fun m hm => by simp only [linExplorationWeight, hCn m hm, ↓reduceIte]
  rw [hπC]
  refine mul_le_mul_of_nonneg_left ?_
    (Finset.prod_nonneg fun m _ => (linMemberWeight_pos (boundary := boundary) s m).le)
  rw [← Finset.prod_filter_mul_prod_filter_not (N \ (C ∪ R)) (fun m => ∑ j, m j = 0)]
  have h1 : ∏ m ∈ (N \ (C ∪ R)).filter (fun m => ∑ j, m j = 0),
      (1 - linExplorationWeight boundary s m) =
      ∏ m ∈ (N \ (C ∪ R)).filter (fun m => ∑ j, m j = 0),
        (1 - linMemberWeight boundary s m) :=
    Finset.prod_congr rfl fun m hm => by
      simp only [linExplorationWeight, (Finset.mem_filter.1 hm).2, ↓reduceIte]
  have h2 : ∏ m ∈ (N \ (C ∪ R)).filter (fun m => ¬ ∑ j, m j = 0),
      (1 - linExplorationWeight boundary s m) =
      (1 / 2) ^ ((N \ (C ∪ R)).filter (fun m => ¬ ∑ j, m j = 0)).card := by
    have h2' : ∏ m ∈ (N \ (C ∪ R)).filter (fun m => ¬ ∑ j, m j = 0),
        (1 - linExplorationWeight boundary s m) =
        ∏ _m ∈ (N \ (C ∪ R)).filter (fun m => ¬ ∑ j, m j = 0), (1 / 2 : ℝ) :=
      Finset.prod_congr rfl fun m hm => by
        simp only [linExplorationWeight, (Finset.mem_filter.1 hm).2, ↓reduceIte]
        norm_num
    rw [h2', Finset.prod_const]
  have hcard : ((N \ (C ∪ R)).filter (fun m => ¬ ∑ j, m j = 0)).card ≤ 1 := by
    refine Finset.card_le_one.2 fun a ha b hb => ?_
    obtain ⟨ha1, ha2⟩ := Finset.mem_filter.1 ha
    obtain ⟨hb1, hb2⟩ := Finset.mem_filter.1 hb
    exact hNa a (Finset.mem_sdiff.1 ha1).1 b (Finset.mem_sdiff.1 hb1).1 ha2 hb2
  have h3 : (1 / 2 : ℝ) ≤ (1 / 2) ^ ((N \ (C ∪ R)).filter (fun m => ¬ ∑ j, m j = 0)).card := by
    calc (1 / 2 : ℝ) = (1 / 2) ^ 1 := by norm_num
      _ ≤ _ := pow_le_pow_of_le_one (by norm_num) (by norm_num) hcard
  have hB0 : 0 ≤ ∏ m ∈ (N \ (C ∪ R)).filter (fun m => ∑ j, m j = 0),
      (1 - linMemberWeight boundary s m) :=
    Finset.prod_nonneg fun m hm => by
      have := hθ1 m (Finset.mem_sdiff.1 (Finset.mem_filter.1 hm).1).1; linarith
  rw [h1, h2, mul_comm]
  exact mul_le_mul_of_nonneg_left h3 hB0

end Weights

/-! ### The neighbours of a cluster, linear weights -/

section Count

variable {boundary : SquareBoundary} {L : ℕ}

/-- **The linear weight of the neighbours of a neutral cluster** (the linear analogue of
`sum_neighbourWeight_le`): `∑ e^{-s(∑|m| + log₂(d(m)+1))} ≤ 288 M² e^{-s} |X|`. -/
theorem sum_linNeighbourWeight_le (hL : 1 < L) {N : Finset (ChargeDensity L)}
    (hens : IsChargeEnsemble N) {o x : Fin L × Fin L} (hox : o ≠ x)
    {C : Finset (ChargeDensity L)} (hCn : ∀ m ∈ C, ∑ j, m j = 0) {sw : ℝ} (hsw : 0 < sw)
    (hq : Real.exp (-sw) ≤ 1 / 32) :
    ∑ m ∈ (N \ (C ∪ markedRemainder boundary L (dipoleMark o x) N C)).filter
        (fun m => ∑ j, m j = 0),
      Real.exp (-sw * (∑ j, |(m j : ℝ)| +
        Real.logb 2 (chargeDiameter boundary L m + 1))) ≤
      288 * (chargeCoverScale : ℝ) ^ 2 * Real.exp (-sw) *
        (markedSupport L (dipoleMark o x) C).card := by
  classical
  set ρ₀ := dipoleMark o x with hρ₀
  set X := markedSupport L ρ₀ C with hX
  set F := (N \ (C ∪ markedRemainder boundary L ρ₀ N C)).filter (fun m => ∑ j, m j = 0) with hF
  set q := Real.exp (-sw) with hqdef
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  set M : ℝ := (chargeCoverScale : ℝ) with hM
  have hMpos : (1 : ℝ) ≤ M := by norm_num [hM, chargeCoverScale]
  -- membership facts
  have hFmem : ∀ m ∈ F, m ∈ N ∧ ∑ j, m j = 0 ∧ MarkAdjacent boundary L ρ₀ m C := by
    intro m hm
    obtain ⟨hm1, hmn⟩ := Finset.mem_filter.1 hm
    obtain ⟨hmN, hmCR⟩ := Finset.mem_sdiff.1 hm1
    refine ⟨hmN, hmn, ?_⟩
    by_contra hadj
    apply hmCR
    by_cases hmC : m ∈ C
    · exact Finset.mem_union_left _ hmC
    · exact Finset.mem_union_right _
        (Finset.mem_filter.2 ⟨Finset.mem_sdiff.2 ⟨hmN, hmC⟩, hadj⟩)
  have hdisjF : ∀ m ∈ F, ∀ m' ∈ F, m ≠ m' →
      Disjoint (Function.support m) (Function.support m') := fun m hm m' hm' hne =>
    hens.2 m (hFmem m hm).1 m' (hFmem m' hm').1 hne
  have hXne : X.Nonempty := ⟨o, chargeSupport_subset_markedSupport _ C
    (mem_chargeSupport'.2 (by simp [hρ₀, dipoleMark, hox]))⟩
  -- the scale class of a member
  set kf : ChargeDensity L → ℕ := fun m => Nat.log 2 (chargeDiameter boundary L m + 1) with hkf
  have hd1 : ∀ m ∈ F, 1 ≤ chargeDiameter boundary L m := fun m hm =>
    one_le_chargeDiameter_of_neutral boundary hL m (hens.1 m (hFmem m hm).1) (hFmem m hm).2.1
  have hdlt : ∀ m, (chargeDiameter boundary L m : ℝ) < 2 ^ (kf m + 1) := by
    intro m
    have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (chargeDiameter boundary L m + 1)
    have h' : chargeDiameter boundary L m < 2 ^ (kf m + 1) := by
      simp only [hkf]
      omega
    exact_mod_cast h'
  -- each member is near `X` at its scale
  have hnear : ∀ m ∈ F, ∃ y, m y ≠ 0 ∧ ∃ z ∈ X,
      latticeDistance boundary L y z ≤ chargeCoverScale * 4 ^ (kf m + 1) := by
    intro m hm
    obtain ⟨hmN, hmn, hadj⟩ := hFmem m hm
    have hm0 := hens.1 m hmN
    obtain ⟨y, hy, z, hz, hyz⟩ := exists_squareDistance_witness boundary L (chargeSupport m) X
      (chargeSupport_nonempty' hm0) hXne
    refine ⟨y, mem_chargeSupport'.1 hy, z, hz, ?_⟩
    rw [hyz]
    unfold MarkAdjacent at hadj
    rw [markScale_of_neutral hmn hCn] at hadj
    have hd := hd1 m hm
    have hdR : (1 : ℝ) ≤ chargeDiameter boundary L m := by exact_mod_cast hd
    have hmin : ((min (chargeDiameter boundary L m) (squareDiameter boundary L
        (markedSupport L ρ₀ C)) : ℕ) : ℝ) ^ chargeCoverExponent ≤
        (chargeDiameter boundary L m : ℝ) ^ (2 : ℝ) := by
      calc ((min (chargeDiameter boundary L m) (squareDiameter boundary L
            (markedSupport L ρ₀ C)) : ℕ) : ℝ) ^ chargeCoverExponent
          ≤ (chargeDiameter boundary L m : ℝ) ^ chargeCoverExponent :=
            Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast min_le_left _ _)
              (by norm_num [chargeCoverExponent])
        _ ≤ (chargeDiameter boundary L m : ℝ) ^ (2 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hdR (by norm_num [chargeCoverExponent])
    have hsq : (chargeDiameter boundary L m : ℝ) ^ (2 : ℝ) < 4 ^ (kf m + 1) := by
      rw [Real.rpow_two, show (4 : ℝ) ^ (kf m + 1) = ((2 : ℝ) ^ (kf m + 1)) ^ 2 by
        rw [sq, ← mul_pow]; norm_num]
      exact pow_lt_pow_left₀ (hdlt m) (Nat.cast_nonneg _) (by norm_num)
    have hlt : (squareDistance boundary L (chargeSupport m) (markedSupport L ρ₀ C) : ℝ) <
        (chargeCoverScale : ℝ) * 4 ^ (kf m + 1) := by
      refine lt_of_lt_of_le hadj ?_
      exact mul_le_mul_of_nonneg_left (hmin.trans hsq.le) (by norm_num [chargeCoverScale])
    have : squareDistance boundary L (chargeSupport m) X < chargeCoverScale * 4 ^ (kf m + 1) := by
      exact_mod_cast hlt
    exact this.le
  -- the weight of one member
  have hweight : ∀ m ∈ F, Real.exp (-sw * (∑ j, |(m j : ℝ)| +
      Real.logb 2 (chargeDiameter boundary L m + 1))) ≤ q * q ^ kf m := by
    intro m hm
    have hm0 := hens.1 m (hFmem m hm).1
    have hs : (1 : ℝ) ≤ ∑ j, |(m j : ℝ)| := one_le_sum_abs_of_ne_zero hm0
    have hl : (kf m : ℝ) ≤ Real.logb 2 (chargeDiameter boundary L m + 1) := by
      have hpow : (2 : ℝ) ^ kf m ≤ (chargeDiameter boundary L m : ℝ) + 1 := by
        have := Nat.pow_log_le_self 2 (Nat.succ_ne_zero (chargeDiameter boundary L m))
        exact_mod_cast this
      rw [Real.le_logb_iff_rpow_le (by norm_num) (by positivity), Real.rpow_natCast]
      exact_mod_cast hpow
    have hcb : 0 < sw := hsw
    rw [hqdef, ← Real.exp_nat_mul, ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    nlinarith
  -- sum by scale classes
  have hF_le : ∑ m ∈ F, Real.exp (-sw * (∑ j, |(m j : ℝ)| +
      Real.logb 2 (chargeDiameter boundary L m + 1))) ≤
      ∑ k ∈ F.image kf, (X.card : ℝ) * (9 * M ^ 2 * 16 ^ (k + 1)) * (q * q ^ k) := by
    refine (Finset.sum_le_sum hweight).trans ?_
    rw [← Finset.sum_fiberwise_of_maps_to (g := kf) (t := F.image kf)
      fun m hm => Finset.mem_image_of_mem kf hm]
    refine Finset.sum_le_sum fun k _ => ?_
    have hcongr : ∑ m ∈ F with kf m = k, q * q ^ kf m = ∑ m ∈ F with kf m = k, q * q ^ k :=
      Finset.sum_congr rfl fun m hm => by rw [(Finset.mem_filter.1 hm).2]
    rw [hcongr, Finset.sum_const, nsmul_eq_mul]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    have hcard := card_le_of_near (boundary := boundary) (F.filter fun m => kf m = k)
      (fun m hm m' hm' => hdisjF m (Finset.mem_filter.1 hm).1 m' (Finset.mem_filter.1 hm').1) X
      (chargeCoverScale * 4 ^ (k + 1)) fun m hm => by
        have := hnear m (Finset.mem_filter.1 hm).1
        rwa [(Finset.mem_filter.1 hm).2] at this
    have hr1 : 1 ≤ chargeCoverScale * 4 ^ (k + 1) :=
      Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by norm_num [chargeCoverScale])
        (pow_ne_zero _ (by norm_num)))
    have hcardR : ((F.filter fun m => kf m = k).card : ℝ) ≤
        (X.card : ℝ) * (2 * ((chargeCoverScale * 4 ^ (k + 1) : ℕ) : ℝ) + 1) ^ 2 := by
      exact_mod_cast hcard
    refine hcardR.trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _))
    have hr1R : (1 : ℝ) ≤ ((chargeCoverScale * 4 ^ (k + 1) : ℕ) : ℝ) := by exact_mod_cast hr1
    have h3 : (2 * ((chargeCoverScale * 4 ^ (k + 1) : ℕ) : ℝ) + 1) ^ 2 ≤
        9 * ((chargeCoverScale * 4 ^ (k + 1) : ℕ) : ℝ) ^ 2 := by nlinarith
    refine h3.trans (le_of_eq ?_)
    push_cast
    rw [hM, show (16 : ℝ) ^ (k + 1) = ((4 : ℝ) ^ (k + 1)) ^ 2 by
      rw [sq, ← mul_pow]; norm_num]
    ring
  refine hF_le.trans ?_
  -- the geometric sum
  have hgeom : ∑ k ∈ F.image kf, (16 * q) ^ k ≤ 2 := by
    set n := (F.image kf).sup id + 1
    have hsub : F.image kf ⊆ Finset.range n := fun k hk =>
      Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.le_sup (f := id) hk))
    calc ∑ k ∈ F.image kf, (16 * q) ^ k ≤ ∑ k ∈ Finset.range n, (16 * q) ^ k :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun k _ _ => by positivity
      _ ≤ ∑ k ∈ Finset.range n, (1 / (2 : ℝ)) ^ k :=
          Finset.sum_le_sum fun k _ => pow_le_pow_left₀ (by positivity) (by linarith) k
      _ ≤ 2 := sum_geometric_two_le n
  have hrw : ∑ k ∈ F.image kf, (X.card : ℝ) * (9 * M ^ 2 * 16 ^ (k + 1)) * (q * q ^ k) =
      144 * M ^ 2 * q * X.card * ∑ k ∈ F.image kf, (16 * q) ^ k := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_pow, pow_succ]
    ring
  rw [hrw]
  have hXc : (0 : ℝ) ≤ X.card := Nat.cast_nonneg _
  calc 144 * M ^ 2 * q * X.card * ∑ k ∈ F.image kf, (16 * q) ^ k
      ≤ 144 * M ^ 2 * q * X.card * 2 :=
        mul_le_mul_of_nonneg_left hgeom (by positivity)
    _ = 288 * M ^ 2 * q * X.card := by ring

end Count

/-! ### The per-cluster estimate, linear weights -/

section ClusterEstimate

variable {boundary : SquareBoundary} {L : ℕ}

/-- Step 1: the activity of the cluster against the clock gain of all its orientations,
`∑_T 2^{-|C|} |∏_C K| e^{-G(C,T)} ≤ e^{289 D₂ A(X) + h Σ − G*}` with
`G* = λη(|X|/16 + Σ/8 + A(X)/(16 D₁))`, `Σ = ∑_{m ∈ C} ∑_j |m(j)|`. -/
theorem linCluster_orientationSum_le (hL : 1 < L) {D₁ D₂ : ℝ} (hD₁ : 1 ≤ D₁) (hD₂ : 0 ≤ D₂)
    (h21 : P21Step boundary L D₁) {N : Finset (ChargeDensity L)} (hens : IsChargeEnsemble N)
    (hNb : IsScaleSeparated boundary L N)
    (K : ChargeDensity L → ℝ) {lamHat : Fin L × Fin L → ℕ → ℝ} {h : ℝ}
    (hd : ∀ ϱ ∈ N, ∑ j, ϱ j = 0 →
      |K ϱ| ≤ Real.exp (D₂ * chargeCoverCost boundary L ϱ) *
        ∏ j ∈ chargeSupport ϱ, Real.exp ((ϱ j : ℝ) ^ 2) * |lamHat j (ϱ j).natAbs|)
    (hlam : ∀ ϱ ∈ N, ∏ j ∈ chargeSupport ϱ, Real.exp ((ϱ j : ℝ) ^ 2) * |lamHat j (ϱ j).natAbs| ≤
      Real.exp (h * ∑ j, |(ϱ j : ℝ)|))
    {o x : Fin L × Fin L} (hox : o ≠ x) {ξ η : ℝ} (hξ0 : 0 < ξ) (hξ1 : ξ < 1) (hη : 0 < η)
    (hηξ : η ≤ dipoleGap ξ) {lam : ℝ} (hlam0 : 0 ≤ lam)
    {C : Finset (ChargeDensity L)} (hC : C ∈ markedClusters boundary L (dipoleMark o x) N)
    (hCn : ∀ m ∈ C, ∑ j, m j = 0) :
    ∑ T ∈ C.powerset, |(1 / 2) ^ C.card * ∏ m ∈ C, K m| *
        Real.exp (-clockCompositeGain boundary (by omega) ξ η lam (dipoleMark o x) C T) ≤
      Real.exp (289 * D₂ * (chargeCoverCost boundary L
          (supportProxy (markedSupport L (dipoleMark o x) C)) : ℝ) +
        h * ∑ m ∈ C, ∑ j, |((m j : ℤ) : ℝ)| -
        lam * η * ((markedSupport L (dipoleMark o x) C).card / 16 +
          (∑ m ∈ C, ∑ j, |((m j : ℤ) : ℝ)|) / 8 +
          (chargeCoverCost boundary L (supportProxy (markedSupport L (dipoleMark o x) C)) : ℝ) /
            (16 * D₁))) := by
  classical
  have hL0 : 0 < L := by omega
  obtain ⟨X, hX⟩ : ∃ X, X = markedSupport L (dipoleMark o x) C := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = (chargeCoverCost boundary L (supportProxy X) : ℝ) := ⟨_, rfl⟩
  obtain ⟨sm, hsm⟩ : ∃ sm : ℝ, sm = ∑ m ∈ C, ∑ j, |((m j : ℤ) : ℝ)| := ⟨_, rfl⟩
  obtain ⟨nX, hnX⟩ : ∃ nX : ℝ, nX = (X.card : ℝ) := ⟨_, rfl⟩
  rw [← hX, ← hA, ← hsm, ← hnX]
  have hCN : C ⊆ N := (mem_clusters.1 hC).1
  have hdisjC : ∀ m ∈ C, ∀ m' ∈ C, m ≠ m' →
      Disjoint (Function.support m) (Function.support m') :=
    fun m hm m' hm' hne => hens.2 m (hCN hm) m' (hCN hm') hne
  have hdX : 1 ≤ squareDiameter boundary L (markedSupport L (dipoleMark o x) C) :=
    one_le_squareDiameter_markedSupport_dipole hL hox C
  have hnX0 : 0 ≤ nX := by rw [hnX]; exact Nat.cast_nonneg _
  -- the activity
  have hact : |(1 / 2) ^ C.card * ∏ m ∈ C, K m| ≤
      (1 / 2) ^ C.card * Real.exp (289 * D₂ * A) * Real.exp (h * sm) := by
    refine (abs_clusterWeight_le_coverCost hL hD₂ hd hens hNb hCN hCn hdX).trans ?_
    rw [hA, hX]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [hsm, Finset.mul_sum, Real.exp_sum]
    exact Finset.prod_le_prod₀ (fun m _ => Finset.prod_nonneg fun j _ => by positivity)
      fun m hm => hlam m (hCN hm)
  -- the gain of each orientation
  have hgain : ∀ T ∈ C.powerset, lam * η * (nX / 16 + sm / 8 + A / (16 * D₁)) ≤
      clockCompositeGain boundary hL0 ξ η lam (dipoleMark o x) C T := by
    intro T hT
    have hT' : T ⊆ C := Finset.mem_powerset.1 hT
    have hmass := sum_abs_markedDensity_ge hox hξ0 hξ1 hη.le hηξ hT' hdisjC
    rw [← hX, ← hsm, ← hnX] at hmass
    have hsuppP : chargeSupport (markedProxy (dipoleMark o x) C T) = X := by
      rw [hX]; exact chargeSupport_markedProxy_dipole hox hT' hdisjC
    have hp0 : markedProxy (dipoleMark o x) C T ≠ 0 := by
      intro h0
      have ho : o ∈ X := by
        rw [hX]
        exact chargeSupport_subset_markedSupport _ C
          (mem_chargeSupport'.2 (by simp [dipoleMark, hox]))
      rw [← hsuppP, h0] at ho
      exact (mem_chargeSupport'.1 ho) rfl
    obtain ⟨-, hP21⟩ := h21 (fun ϱ k => sharedMinimumSquareCover boundary L ϱ hL0 k) _ hp0
    have hAeq : chargeCoverCost boundary L (markedProxy (dipoleMark o x) C T) =
        chargeCoverCost boundary L (supportProxy X) :=
      chargeCoverCost_congr (by rw [hsuppP, chargeSupport_supportProxy])
    have hS0 : (squareCoverNumber boundary L 0 (markedProxy (dipoleMark o x) C T) : ℝ) ≤ nX := by
      have := squareCoverNumber_zero_le_card boundary L (markedProxy (dipoleMark o x) C T)
      rw [hsuppP] at this
      rw [hnX]
      exact_mod_cast this
    rw [hAeq, ← hA] at hP21
    obtain ⟨S, hS⟩ : ∃ S : ℝ, S = (separatedSquareTotal boundary L
        (fun ϱ k => sharedMinimumSquareCover boundary L ϱ hL0 k)
        (markedProxy (dipoleMark o x) C T) : ℝ) := ⟨_, rfl⟩
    rw [← hS] at hP21
    have hS0' : 0 ≤ S := by rw [hS]; exact Nat.cast_nonneg _
    have hAS : A / D₁ ≤ nX + S := by
      rw [div_le_iff₀ (by linarith)]
      have h2 : D₁ * ((squareCoverNumber boundary L 0 (markedProxy (dipoleMark o x) C T) : ℝ) +
          S) ≤ D₁ * (nX + S) := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      linarith
    obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = ∑ j, |markedDensity ξ (dipoleMark o x) (satellite L C T) j| :=
      ⟨_, rfl⟩
    rw [← hQ] at hmass
    have hcg : clockCompositeGain boundary hL0 ξ η lam (dipoleMark o x) C T =
        lam / 4 * Q + lam * η / 2 * S := by
      unfold clockCompositeGain
      rw [hQ, hS]
    rw [hcg]
    have hlη : 0 ≤ lam * η := mul_nonneg hlam0 hη.le
    have e1 : lam * η * (A / D₁) ≤ lam * η * nX + lam * η * S :=
      by nlinarith [mul_le_mul_of_nonneg_left hAS hlη]
    have e2 : lam / 4 * (η / 2 * (nX + sm)) ≤ lam / 4 * Q :=
      mul_le_mul_of_nonneg_left hmass (by positivity)
    have e3 : 0 ≤ lam * η * S := mul_nonneg hlη hS0'
    have key : lam * η * (nX / 16 + sm / 8 + A / (16 * D₁)) =
        lam * η * nX / 16 + lam * η * sm / 8 + lam * η * (A / D₁) / 16 := by
      field_simp
    rw [key]
    nlinarith
  -- the sum over orientations
  calc ∑ T ∈ C.powerset, |(1 / 2) ^ C.card * ∏ m ∈ C, K m| *
        Real.exp (-clockCompositeGain boundary hL0 ξ η lam (dipoleMark o x) C T)
      ≤ ∑ _T ∈ C.powerset, (1 / 2) ^ C.card * Real.exp (289 * D₂ * A) *
          Real.exp (h * sm) * Real.exp (-(lam * η * (nX / 16 + sm / 8 + A / (16 * D₁)))) :=
        Finset.sum_le_sum fun T hT => mul_le_mul hact
          (Real.exp_le_exp.2 (neg_le_neg (hgain T hT))) (Real.exp_pos _).le (by positivity)
    _ = Real.exp (289 * D₂ * A + h * sm -
          lam * η * (nX / 16 + sm / 8 + A / (16 * D₁))) := by
        rw [Finset.sum_const, Finset.card_powerset, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat,
          sub_eq_add_neg, Real.exp_add, Real.exp_add]
        have h2 : (2 : ℝ) ^ C.card * (1 / 2) ^ C.card = 1 := by
          rw [← mul_pow]; norm_num
        calc (2 : ℝ) ^ C.card * ((1 / 2) ^ C.card * Real.exp (289 * D₂ * A) *
              Real.exp (h * sm) * Real.exp (-(lam * η * (nX / 16 + sm / 8 +
                A / (16 * D₁)))))
            = ((2 : ℝ) ^ C.card * (1 / 2) ^ C.card) * (Real.exp (289 * D₂ * A) *
                Real.exp (h * sm) * Real.exp (-(lam * η * (nX / 16 + sm / 8 +
                  A / (16 * D₁))))) := by ring
          _ = _ := by rw [h2, one_mul]

/-- Step 4a: `∏_C θ (1 − θ) ≥ e^{-s(Σ + 289 A(X))} e^{-Σ}`. -/
theorem linCluster_memberWeight_ge (hL : 1 < L) {D₁ : ℝ} (h21 : P21Step boundary L D₁)
    {N : Finset (ChargeDensity L)} (hens : IsChargeEnsemble N)
    (hNb : IsScaleSeparated boundary L N) {o x : Fin L × Fin L} (hox : o ≠ x) {s : ℝ}
    (hs : 0 < s) (H4 : Real.exp (-s) ≤ 1 / 32)
    {C : Finset (ChargeDensity L)} (hC : C ∈ markedClusters boundary L (dipoleMark o x) N) :
    Real.exp (-s * (∑ m ∈ C, ∑ j, |((m j : ℤ) : ℝ)| +
        289 * (chargeCoverCost boundary L
          (supportProxy (markedSupport L (dipoleMark o x) C)) : ℝ))) *
        Real.exp (-∑ m ∈ C, ∑ j, |((m j : ℤ) : ℝ)|) ≤
      (∏ m ∈ C, linMemberWeight boundary s m) * ∏ m ∈ C, (1 - linMemberWeight boundary s m) := by
  classical
  have hL0 : 0 < L := by omega
  have hCN : C ⊆ N := (mem_clusters.1 hC).1
  have hdX := one_le_squareDiameter_markedSupport_dipole (boundary := boundary) hL hox C
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = (chargeCoverCost boundary L
      (supportProxy (markedSupport L (dipoleMark o x) C)) : ℝ) := ⟨_, rfl⟩
  obtain ⟨sm, hsm⟩ : ∃ sm : ℝ, sm = ∑ m ∈ C, ∑ j, |((m j : ℤ) : ℝ)| := ⟨_, rfl⟩
  rw [← hA, ← hsm]
  have hθle : ∀ m ∈ N, linMemberWeight boundary s m ≤ 1 / 32 := fun m hm =>
    (linMemberWeight_le hs (hens.1 m hm)).trans H4
  have hcover := fun ϱ k => sharedMinimumSquareCover boundary L ϱ hL0 k
  have hsumA : ∑ m ∈ C, Real.logb 2 (chargeDiameter boundary L m + 1) ≤ 289 * A := by
    have h289 := sum_chargeCoverCost_le hL hens hNb hCN
      (fun m hm => chargeSupport_subset_markedSupport_of_mem hm) hdX
    have h289R : (∑ m ∈ C, (chargeCoverCost boundary L m : ℝ)) ≤ 289 * A := by
      rw [hA]; exact_mod_cast h289
    exact (Finset.sum_le_sum fun m hm => (h21 hcover m (hens.1 m (hCN hm))).1).trans h289R
  have hcardC : (C.card : ℝ) ≤ sm := by
    rw [hsm, Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
    exact Finset.sum_le_sum fun m hm => one_le_sum_abs_of_ne_zero (hens.1 m (hCN hm))
  have hθC : ∏ m ∈ C, linMemberWeight boundary s m = Real.exp (-s *
      (sm + ∑ m ∈ C, Real.logb 2 (chargeDiameter boundary L m + 1))) := by
    unfold linMemberWeight
    rw [← Real.exp_sum]
    congr 1
    rw [hsm, ← Finset.sum_add_distrib, Finset.mul_sum]
  have h1 : Real.exp (-s * (sm + 289 * A)) ≤ ∏ m ∈ C, linMemberWeight boundary s m := by
    rw [hθC]
    refine Real.exp_le_exp.2 ?_
    have := mul_le_mul_of_nonneg_left (add_le_add_left hsumA sm) hs.le
    linarith
  have h2 : Real.exp (-sm) ≤ ∏ m ∈ C, (1 - linMemberWeight boundary s m) := by
    calc Real.exp (-sm) ≤ Real.exp (-(C.card : ℝ)) := Real.exp_le_exp.2 (by linarith)
      _ = (Real.exp (-1)) ^ C.card := by rw [← Real.exp_nat_mul]; ring_nf
      _ ≤ (1 / 2) ^ C.card := by
          refine pow_le_pow_left₀ (Real.exp_pos _).le ?_ _
          have := Real.add_one_le_exp (1 : ℝ)
          rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
          linarith
      _ = ∏ _m ∈ C, (1 / 2 : ℝ) := by rw [Finset.prod_const]
      _ ≤ ∏ m ∈ C, (1 - linMemberWeight boundary s m) :=
          Finset.prod_le_prod₀ (fun _ _ => by norm_num)
            fun m hm => by have := hθle m (hCN hm); linarith
  exact mul_le_mul h1 h2 (Real.exp_pos _).le
    (Finset.prod_nonneg fun m _ => (linMemberWeight_pos (boundary := boundary) s m).le)

/-- Step 4b: the neutral neighbours, `∏_{Bd} (1 − θ) ≥ e^{-2κ|X|}`, `κ = 288 M² e^{-s}`. -/
theorem linCluster_neighbourWeight_ge (hL : 1 < L) {N : Finset (ChargeDensity L)}
    (hens : IsChargeEnsemble N) {o x : Fin L × Fin L} (hox : o ≠ x)
    {C : Finset (ChargeDensity L)} (hCn : ∀ m ∈ C, ∑ j, m j = 0) {s : ℝ} (hs : 0 < s)
    (H4 : Real.exp (-s) ≤ 1 / 32) :
    Real.exp (-(2 * (288 * (chargeCoverScale : ℝ) ^ 2 * Real.exp (-s)) *
        (markedSupport L (dipoleMark o x) C).card)) ≤
      ∏ m ∈ (N \ (C ∪ markedRemainder boundary L (dipoleMark o x) N C)).filter
          (fun m => ∑ j, m j = 0), (1 - linMemberWeight boundary s m) := by
  have hsumB := sum_linNeighbourWeight_le (boundary := boundary) hL hens hox hCn hs H4
  have hθle : ∀ m ∈ N, linMemberWeight boundary s m ≤ 1 / 32 := fun m hm =>
    (linMemberWeight_le hs (hens.1 m hm)).trans H4
  calc Real.exp (-(2 * (288 * (chargeCoverScale : ℝ) ^ 2 * Real.exp (-s)) *
        (markedSupport L (dipoleMark o x) C).card))
      ≤ Real.exp (-(2 * ∑ m ∈ (N \ (C ∪ markedRemainder boundary L (dipoleMark o x) N C)).filter
          (fun m => ∑ j, m j = 0), linMemberWeight boundary s m)) := by
        refine Real.exp_le_exp.2 ?_
        unfold linMemberWeight
        linarith
    _ = ∏ m ∈ (N \ (C ∪ markedRemainder boundary L (dipoleMark o x) N C)).filter
          (fun m => ∑ j, m j = 0), Real.exp (-(2 * linMemberWeight boundary s m)) := by
        rw [← Real.exp_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
    _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => (Real.exp_pos _).le)
        fun m hm => exp_neg_two_mul_le_one_sub (linMemberWeight_pos (boundary := boundary) s m).le
          ((hθle m (Finset.mem_sdiff.1 (Finset.mem_filter.1 hm).1).1).trans (by norm_num))

/-- Step 5: the exponent algebra of the clock cluster estimate (conditions (C1)–(C3)). -/
theorem linCluster_exponent_le {D₁ D₂ h s lam η A sm nX ℓ κ : ℝ} (hD₁ : 1 ≤ D₁)
    (hlη : 0 ≤ lam * η) (hA : 0 ≤ A) (hsm : 0 ≤ sm) (hnX : 0 ≤ nX) (hℓ : ℓ ≤ A)
    (C1 : h + s + 1 ≤ lam * η / 8) (C2 : 4 * κ ≤ lam * η / 16)
    (C3 : 289 * D₂ + 289 * s ≤ lam * η / (32 * D₁)) :
    289 * D₂ * A + h * sm - lam * η * (nX / 16 + sm / 8 + A / (16 * D₁)) ≤
      -(lam * η / (32 * D₁)) * ℓ - s * (sm + 289 * A) - sm - 2 * κ * nX - 2 * κ * nX := by
  have hD₁pos : 0 < D₁ := by linarith
  have k1 : (h + s + 1 - lam * η / 8) * sm ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) hsm
  have k2 : (289 * D₂ + 289 * s - lam * η / (32 * D₁)) * A ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) hA
  have k3 : (4 * κ - lam * η / 16) * nX ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) hnX
  have hdec : 0 ≤ lam * η / (32 * D₁) := div_nonneg hlη (by positivity)
  have k4 : lam * η / (32 * D₁) * ℓ ≤ lam * η / (32 * D₁) * A :=
    mul_le_mul_of_nonneg_left hℓ hdec
  have e5 : lam * η * (A / (16 * D₁)) = lam * η / (32 * D₁) * A + lam * η / (32 * D₁) * A := by
    field_simp
    ring
  have e6 : lam * η * (nX / 16 + sm / 8 + A / (16 * D₁)) =
      lam * η * nX / 16 + lam * η * sm / 8 + lam * η * (A / (16 * D₁)) := by ring
  rw [e6, e5]
  nlinarith [k1, k2, k3, k4]

/-- **The estimate of one neutral cluster under the clock law** (FS81 (5.31)–(5.33), §7.1,
with linear exploration weights). Under (C1)–(C3) and `e^{-s} ≤ 1/32`, the bound of
`abs_clockMarkedBranch_le` for a neutral cluster `C` is at most
`2 e^{-(λη/(32 D₁)) log₂(|o − x| + 1)}` times its exploration weight. -/
theorem linCluster_estimate (hL : 1 < L) {D₁ D₂ : ℝ} (hD₁ : 1 ≤ D₁) (hD₂ : 0 ≤ D₂)
    (h21 : P21Step boundary L D₁) {N : Finset (ChargeDensity L)} (hens : IsChargeEnsemble N)
    (hNa : AtMostOneNonNeutral N) (hNb : IsScaleSeparated boundary L N)
    (K : ChargeDensity L → ℝ) {lamHat : Fin L × Fin L → ℕ → ℝ} {h : ℝ}
    (hd : ∀ ϱ ∈ N, ∑ j, ϱ j = 0 →
      |K ϱ| ≤ Real.exp (D₂ * chargeCoverCost boundary L ϱ) *
        ∏ j ∈ chargeSupport ϱ, Real.exp ((ϱ j : ℝ) ^ 2) * |lamHat j (ϱ j).natAbs|)
    (hlam : ∀ ϱ ∈ N, ∏ j ∈ chargeSupport ϱ, Real.exp ((ϱ j : ℝ) ^ 2) * |lamHat j (ϱ j).natAbs| ≤
      Real.exp (h * ∑ j, |(ϱ j : ℝ)|))
    {o x : Fin L × Fin L} (hox : o ≠ x) {ξ η : ℝ} (hξ0 : 0 < ξ) (hξ1 : ξ < 1) (hη : 0 < η)
    (hηξ : η ≤ dipoleGap ξ) {s lam : ℝ} (hs : 0 < s) (hlam0 : 0 ≤ lam)
    (C1 : h + s + 1 ≤ lam * η / 8)
    (C2 : 4 * (288 * (chargeCoverScale : ℝ) ^ 2 * Real.exp (-s)) ≤ lam * η / 16)
    (C3 : 289 * D₂ + 289 * s ≤ lam * η / (32 * D₁))
    (H4 : Real.exp (-s) ≤ 1 / 32)
    {C : Finset (ChargeDensity L)} (hC : C ∈ markedClusters boundary L (dipoleMark o x) N)
    (hCn : ∀ m ∈ C, ∑ j, m j = 0) :
    (∑ T ∈ C.powerset, |(1 / 2) ^ C.card * ∏ m ∈ C, K m| *
        Real.exp (-clockCompositeGain boundary (by omega) ξ η lam (dipoleMark o x) C T)) /
      ∏ m ∈ neutralPart N \ neutralPart (markedRemainder boundary L (dipoleMark o x) N C),
        (1 - linMemberWeight boundary s m) ≤
      2 * Real.exp (-(lam * η / (32 * D₁)) *
          Real.logb 2 (latticeDistance boundary L o x + 1)) *
        ((∏ m ∈ C, linExplorationWeight boundary s m) *
          ∏ m ∈ N \ (C ∪ markedRemainder boundary L (dipoleMark o x) N C),
            (1 - linExplorationWeight boundary s m)) := by
  classical
  have hCN : C ⊆ N := (mem_clusters.1 hC).1
  have hθle : ∀ m ∈ N, linMemberWeight boundary s m ≤ 1 / 32 := fun m hm =>
    (linMemberWeight_le hs (hens.1 m hm)).trans H4
  have hθ1 : ∀ m ∈ N, linMemberWeight boundary s m ≤ 1 := fun m hm =>
    (hθle m hm).trans (by norm_num)
  have h1 := linCluster_orientationSum_le hL hD₁ hD₂ h21 hens hNb K hd hlam hox hξ0 hξ1 hη hηξ
    hlam0 hC hCn
  have h2 := cluster_dropped_le' (θ := linMemberWeight boundary s)
    (R := markedRemainder boundary L (dipoleMark o x) N C)
    (fun m => linMemberWeight_pos (boundary := boundary) s m) hθ1 hCN
  have h3 := linCluster_exploration_ge (boundary := boundary) (s := s)
    (R := markedRemainder boundary L (dipoleMark o x) N C) hNa hθ1 hCn
  have h4 := linCluster_memberWeight_ge hL h21 hens hNb hox hs H4 hC
  have h5 := linCluster_neighbourWeight_ge (boundary := boundary) hL hens hox hCn hs H4
  have h6 := logb_latticeDistance_le_coverCost hL h21 hox C
  obtain ⟨X, hX⟩ : ∃ X, X = markedSupport L (dipoleMark o x) C := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = (chargeCoverCost boundary L (supportProxy X) : ℝ) := ⟨_, rfl⟩
  obtain ⟨sm, hsm⟩ : ∃ sm : ℝ, sm = ∑ m ∈ C, ∑ j, |((m j : ℤ) : ℝ)| := ⟨_, rfl⟩
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = 288 * (chargeCoverScale : ℝ) ^ 2 * Real.exp (-s) := ⟨_, rfl⟩
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : ℝ, ℓ = Real.logb 2 (latticeDistance boundary L o x + 1) := ⟨_, rfl⟩
  obtain ⟨PC, hPC⟩ : ∃ PC : ℝ, PC = ∏ m ∈ C, linMemberWeight boundary s m := ⟨_, rfl⟩
  obtain ⟨QC, hQC⟩ : ∃ QC : ℝ, QC = ∏ m ∈ C, (1 - linMemberWeight boundary s m) := ⟨_, rfl⟩
  obtain ⟨QB, hQB⟩ : ∃ QB : ℝ, QB = ∏ m ∈ (N \ (C ∪ markedRemainder boundary L
      (dipoleMark o x) N C)).filter (fun m => ∑ j, m j = 0), (1 - linMemberWeight boundary s m) :=
    ⟨_, rfl⟩
  rw [← hX, ← hA, ← hsm] at h1
  rw [← hQC, ← hQB] at h2
  rw [← hPC, ← hQB] at h3
  rw [← hX, ← hA, ← hsm, ← hPC, ← hQC] at h4
  rw [← hκ, ← hX, ← hQB] at h5
  rw [← hX, ← hA, ← hℓ] at h6
  rw [← hκ] at C2
  rw [← hℓ]
  have hA0 : 0 ≤ A := by rw [hA]; exact Nat.cast_nonneg _
  have hsm0 : 0 ≤ sm := by
    rw [hsm]; exact Finset.sum_nonneg fun m _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  have hnX0 : (0 : ℝ) ≤ X.card := Nat.cast_nonneg _
  have hexp := linCluster_exponent_le (D₂ := D₂) (h := h) hD₁ (mul_nonneg hlam0 hη.le) hA0 hsm0
    hnX0 h6 C1 C2 C3
  have hQCpos : 0 < QC := by
    rw [hQC]
    exact Finset.prod_pos fun m hm => by have := hθle m (hCN hm); linarith
  have hQBpos : 0 < QB := by
    rw [hQB]
    exact Finset.prod_pos fun m hm => by
      have := hθle m (Finset.mem_sdiff.1 (Finset.mem_filter.1 hm).1).1; linarith
  have hPC0 : 0 ≤ PC := by
    rw [hPC]
    exact Finset.prod_nonneg fun m _ => (linMemberWeight_pos (boundary := boundary) s m).le
  have hDpos : 0 < QC * QB := mul_pos hQCpos hQBpos
  have hE : Real.exp (289 * D₂ * A + h * sm -
        lam * η * (X.card / 16 + sm / 8 + A / (16 * D₁))) ≤
      Real.exp (-(lam * η / (32 * D₁)) * ℓ) * (PC * QC) * (QB * QB) := by
    calc Real.exp (289 * D₂ * A + h * sm -
          lam * η * (X.card / 16 + sm / 8 + A / (16 * D₁)))
        ≤ Real.exp (-(lam * η / (32 * D₁)) * ℓ) *
            (Real.exp (-s * (sm + 289 * A)) * Real.exp (-sm)) *
            (Real.exp (-(2 * κ * X.card)) * Real.exp (-(2 * κ * X.card))) := by
          rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
          refine Real.exp_le_exp.2 ?_
          linarith
      _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left h4 (Real.exp_pos _).le)
          (mul_le_mul h5 h5 (Real.exp_pos _).le hQBpos.le) (by positivity)
          (mul_nonneg (Real.exp_pos _).le (mul_nonneg hPC0 hQCpos.le))
  calc (∑ T ∈ C.powerset, |(1 / 2) ^ C.card * ∏ m ∈ C, K m| *
        Real.exp (-clockCompositeGain boundary (by omega) ξ η lam (dipoleMark o x) C T)) /
        ∏ m ∈ neutralPart N \ neutralPart (markedRemainder boundary L (dipoleMark o x) N C),
          (1 - linMemberWeight boundary s m)
      ≤ Real.exp (289 * D₂ * A + h * sm -
          lam * η * (X.card / 16 + sm / 8 + A / (16 * D₁))) / (QC * QB) :=
        div_le_div₀ (Real.exp_pos _).le h1 hDpos h2
    _ ≤ 2 * Real.exp (-(lam * η / (32 * D₁)) * ℓ) * (PC * (1 / 2 * QB)) := by
        rw [div_le_iff₀ hDpos]
        calc Real.exp (289 * D₂ * A + h * sm -
              lam * η * (X.card / 16 + sm / 8 + A / (16 * D₁)))
            ≤ Real.exp (-(lam * η / (32 * D₁)) * ℓ) * (PC * QC) * (QB * QB) := hE
          _ = _ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h3 (by positivity)

end ClusterEstimate

/-! ### The marked bound on one square domain under the clock law -/

section DomainBound

variable {boundary : SquareBoundary} {L : ℕ}

/-- **The clock renormalized activity of a neutral member**: with the mixture activity bound
`|K| ≤ e^{200 A(ϱ)} ∏_{supp} λ̃_j(|ϱ_j|)`, `λ̃_j(q) ≤ e^{hq}`, and a wave with clock gain
`(λ/8) ∑|ϱ| + λ/(8D₁) A(ϱ)`, `λ/8 ≥ h + s` and `λ/(8D₁) ≥ 200 + s`,
`|K| e^{-E_c} ≤ e^{-s(∑|ϱ| + log₂(d(ϱ) + 1))}`. -/
theorem clock_renormalizedActivity_le {D₁ : ℝ} (h21 : P21Step boundary L D₁)
    (hL0 : 0 < L) {Nq : Fin L × Fin L → ℕ} {lamHat : Fin L × Fin L → ℕ → ℝ}
    {ζ : ∀ j, SiteMode (Nq j) → ℝ} (hζ : ∀ j q, 0 < ζ j q) {h : ℝ}
    (hleaf : ∀ j q, mixtureLeaf Nq lamHat ζ j q ≤ Real.exp (h * q)) {s amp : ℝ} (hs : 0 ≤ s)
    (hamp1 : h + s ≤ amp / 8) (hamp2 : 200 + s ≤ amp / (8 * D₁)) {ϱ : ChargeDensity L}
    (hϱ0 : ϱ ≠ 0) {K E : ℝ}
    (hK : |K| ≤ Real.exp (200 * (chargeCoverCost boundary L ϱ : ℝ)) *
      ∏ j ∈ chargeSupport ϱ, mixtureLeaf Nq lamHat ζ j (ϱ j).natAbs)
    (hE : amp / 8 * ∑ j, |(ϱ j : ℝ)| + amp / (8 * D₁) * (chargeCoverCost boundary L ϱ : ℝ) ≤ E) :
    |K| * Real.exp (-E) ≤ linMemberWeight boundary s ϱ := by
  have hlog := (h21 (fun ϱ k => sharedMinimumSquareCover boundary L ϱ hL0 k) ϱ hϱ0).1
  set A : ℝ := (chargeCoverCost boundary L ϱ : ℝ)
  set X : ℝ := ∑ j, |(ϱ j : ℝ)|
  have hprod :
      ∏ j ∈ chargeSupport ϱ, mixtureLeaf Nq lamHat ζ j (ϱ j).natAbs ≤ Real.exp (h * X) := by
    calc ∏ j ∈ chargeSupport ϱ, mixtureLeaf Nq lamHat ζ j (ϱ j).natAbs
        ≤ ∏ j ∈ chargeSupport ϱ, Real.exp (h * ((ϱ j).natAbs : ℝ)) :=
          Finset.prod_le_prod₀ (fun j _ => mixtureLeaf_nonneg lamHat hζ j _) fun j _ => hleaf j _
      _ = Real.exp (h * ∑ j ∈ chargeSupport ϱ, |(ϱ j : ℝ)|) := by
          rw [← Real.exp_sum, Finset.mul_sum]
          congr 1
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Nat.cast_natAbs, Int.cast_abs]
      _ = Real.exp (h * X) := by
          congr 2
          refine Finset.sum_subset (Finset.subset_univ _) fun j _ hj => ?_
          have : ϱ j = 0 := by
            by_contra h'
            exact hj (mem_chargeSupport'.2 h')
          simp [this]
  have hA0 : 0 ≤ A := Nat.cast_nonneg _
  have hX0 : 0 ≤ X := Finset.sum_nonneg fun j _ => abs_nonneg _
  have hK' : |K| ≤ Real.exp (200 * A + h * X) := by
    rw [Real.exp_add]
    exact hK.trans (mul_le_mul_of_nonneg_left hprod (Real.exp_pos _).le)
  calc |K| * Real.exp (-E) ≤ Real.exp (200 * A + h * X) * Real.exp (-E) :=
        mul_le_mul_of_nonneg_right hK' (Real.exp_pos _).le
    _ = Real.exp (200 * A + h * X - E) := by rw [← Real.exp_add]; ring_nf
    _ ≤ linMemberWeight boundary s ϱ := by
        unfold linMemberWeight
        refine Real.exp_le_exp.2 ?_
        have h1 : (h + s) * X ≤ amp / 8 * X := mul_le_mul_of_nonneg_right hamp1 hX0
        have h2 : (200 + s) * A ≤ amp / (8 * D₁) * A := mul_le_mul_of_nonneg_right hamp2 hA0
        have h3 : s * Real.logb 2 (chargeDiameter boundary L ϱ + 1) ≤ s * A :=
          mul_le_mul_of_nonneg_left hlog hs
        nlinarith

/-- **The marked bound on one square domain under the clock law** (FS81 Theorem 7.1(2) before
the limit, for site weights given by a positive mixture, e.g. the Fejér weights of the clock comb).
Let the domain carry KP's mixture T2.2, P2.1 and L4.6, the site mixture have leaves
`λ̃_j(q) ≤ e^{hq}`, the clock cost have a two-branch envelope with the unmarked amplitude `λ`
(the conditions of `clockWaveSelection_kp`) beating the leaves and the cover entropy
(`λ/8 ≥ h + s`, `λ/(8D₁) ≥ 200 + s`, `e^{-s} ≤ 1/32`), and the composite amplitude `λ_c` satisfy
`28 λ_c ≤ n`, `8192 β λ_c ≤ η n²` and (C1)–(C3). Then for the dipole at `o ≠ x` with clock mark
`ξ/n` (`0 < ξ < n`, `η ≤ min(ξ/n, 1 − ξ/n)`), `0 < 𝒵 = ∫ ∏_j λ_j(φ_j) dμ` and
`|∫ cos((ξ/n)(φ_o − φ_x)) ∏_j λ_j(φ_j) dμ| ≤ 2 e^{-(λ_c η/(32 D₁)) log₂(|o − x| + 1)} 𝒵`
under the compact clock law `μ`. -/
theorem clock_markedDomain_bound (hL : 1 < L) (hdom : boundary = .free ∨ Even L) {E : Type}
    [Fintype E] (Λ : Multigraph (Fin L × Fin L) E) (hΛ : Λ.toSimpleGraph.Connected)
    (hdist : ∀ x y, latticeDistance boundary L x y = Λ.toSimpleGraph.dist x y)
    (B : SpinWaves.BipartiteDegreeFour Λ) (h46 : SpinWaves.L46Step boundary Λ)
    {D₁ : ℝ} (hD₁ : 1 ≤ D₁) (h21 : P21Step boundary L D₁)
    (lam : Fin L × Fin L → ℝ → ℝ) (Nq : Fin L × Fin L → ℕ) (lamHat : Fin L × Fin L → ℕ → ℝ)
    (ζ : ∀ j, SiteMode (Nq j) → ℝ) (hNq : ∀ j, 0 < Nq j)
    (hcut : ∀ j q, Nq j < q → lamHat j q = 0)
    (hlam : ∀ j φ, lam j φ = 1 + 2 * ∑ q ∈ Finset.Icc 1 (Nq j), lamHat j q * Real.cos (q * φ))
    (hζpos : ∀ j q, 0 < ζ j q) (hζsum : ∀ j, ∑ q, ζ j q = 1) {h : ℝ}
    (hleaf : ∀ j q, mixtureLeaf Nq lamHat ζ j q ≤ Real.exp (h * q))
    {n : ℕ} (hn : 0 < n) {β : ℝ} (hβ : 0 ≤ β)
    {κ κ' W : ℝ} (hc : IsCostEnvelope (clockShiftCost β n) κ κ' W) (hκ : 0 < κ)
    {amp : ℝ} (hamp : 0 ≤ amp) (hampW : amp * 28 ≤ W) {k₀ : ℕ} (hk₀ : 1 ≤ k₀)
    (hexp : 100 * 4 ^ k₀ * costMajorant κ κ' (amp * 28) ≤ amp / 2)
    (hquad₁ : amp ≤ 1 / (2 * κ * 4096))
    (hquad₂ : amp ≤ (2 : ℝ) ^ (gradExponent (7 / 4) * k₀) / 28)
    {s : ℝ} (hs : 0 < s) (H4 : Real.exp (-s) ≤ 1 / 32)
    (hamp1 : h + s ≤ amp / 8) (hamp2 : 200 + s ≤ amp / (8 * D₁))
    {o x : Fin L × Fin L} (hox : o ≠ x) {ξ : ℕ} (hξ0 : 0 < ξ) (hξn : ξ < n) {η : ℝ}
    (hη : 0 < η) (hηξ : η ≤ dipoleGap ((ξ : ℝ) / n)) {lamc : ℝ} (hlamc0 : 0 ≤ lamc)
    (hlamcn : 28 * lamc ≤ n) (hcost : 8192 * β * lamc ≤ η * n ^ 2)
    (C1 : h + s + 1 ≤ lamc * η / 8)
    (C2 : 4 * (288 * (chargeCoverScale : ℝ) ^ 2 * Real.exp (-s)) ≤ lamc * η / 16)
    (C3 : 289 * 200 + 289 * s ≤ lamc * η / (32 * D₁)) :
    0 < ∫ φ, ∏ j, lam j (φ j) ∂clockLaw β n Λ ∧
      |∫ φ, Real.cos ((ξ : ℝ) / n * (φ o - φ x)) * ∏ j, lam j (φ j) ∂clockLaw β n Λ| ≤
        2 * Real.exp (-(lamc * η / (32 * D₁)) *
            Real.logb 2 (latticeDistance boundary L o x + 1)) *
          ∫ φ, ∏ j, lam j (φ j) ∂clockLaw β n Λ := by
  classical
  have hL0 : 0 < L := by omega
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hD₁pos : 0 < D₁ := by linarith
  set μ := clockLaw β n Λ with hμ
  have := isProbabilityMeasure_clockLaw Λ hβ hn'
  set ξ' : ℝ := (ξ : ℝ) / n with hξ'
  have hξ'0 : 0 < ξ' := div_pos (by exact_mod_cast hξ0) hn'
  have hξ'1 : ξ' < 1 := (div_lt_one hn').2 (by exact_mod_cast hξn)
  -- the mixture Theorem 2.2
  obtain ⟨m, N, cc, K, hens, hcpos, hcsum, hid, hprop⟩ :=
    t22MixStep_holds boundary hL hdom lam Nq lamHat ζ hNq hcut hlam hζpos hζsum
  -- the center choice and the wave selection
  have hcex : ∀ ϱ : Fin L × Fin L → ℤ, ∃ j, ϱ ≠ 0 → Λ.IsDensityCenter ϱ j := by
    intro ϱ
    by_cases hϱ : ϱ = 0
    · exact ⟨o, fun h' => absurd hϱ h'⟩
    · obtain ⟨j, hj⟩ := Λ.exists_isDensityCenter ϱ hϱ
      exact ⟨j, fun _ => hj⟩
  choose centerOf hcenter using hcex
  have h24 := clockWaveSelection_kp boundary hL Λ hΛ hdist B h46 hD₁pos h21 centerOf hcenter
    hc hκ hamp hampW hk₀ hexp hquad₁ hquad₂
  -- the activity data in the form of the cluster estimate
  set lamHat' : Fin L × Fin L → ℕ → ℝ := fun j q =>
    mixtureLeaf Nq lamHat ζ j q * Real.exp (-((q : ℝ) ^ 2)) with hlamHat'
  have hleafform : ∀ ϱ : ChargeDensity L, ∏ j ∈ chargeSupport ϱ,
      Real.exp ((ϱ j : ℝ) ^ 2) * |lamHat' j (ϱ j).natAbs| =
      ∏ j ∈ chargeSupport ϱ, mixtureLeaf Nq lamHat ζ j (ϱ j).natAbs := by
    intro ϱ
    refine Finset.prod_congr rfl fun j _ => ?_
    simp only [hlamHat']
    rw [abs_mul, abs_of_nonneg (mixtureLeaf_nonneg lamHat hζpos j _), Real.abs_exp,
      show (((ϱ j).natAbs : ℕ) : ℝ) ^ 2 = (ϱ j : ℝ) ^ 2 by
        rw [Nat.cast_natAbs, Int.cast_abs, sq_abs]]
    rw [mul_left_comm, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
  set ε := 2 * Real.exp (-(lamc * η / (32 * D₁)) *
    Real.logb 2 (latticeDistance boundary L o x + 1)) with hε
  have hθle : ∀ i, ∀ ϱ ∈ N i, linMemberWeight boundary s ϱ ≤ 1 / 32 := fun i ϱ hϱ =>
    (linMemberWeight_le hs ((hens i).1 ϱ hϱ)).trans H4
  have hbranch : ∀ i, 0 < ∫ φ, ∏ ϱ ∈ N i, (1 + K i ϱ * Real.cos (∑ j, φ j * (ϱ j : ℝ))) ∂μ ∧
      |∫ φ, Real.cos (ξ' * ∑ j, φ j * (dipoleMark o x j : ℝ)) *
          ∏ ϱ ∈ N i, (1 + K i ϱ * Real.cos (∑ j, φ j * (ϱ j : ℝ))) ∂μ| ≤
        ε * ∫ φ, ∏ ϱ ∈ N i, (1 + K i ϱ * Real.cos (∑ j, φ j * (ϱ j : ℝ))) ∂μ := by
    intro i
    obtain ⟨hNa, hNb, hNc, hd⟩ := hprop i
    have hz : ∀ ϱ ∈ N i, ∑ j, ϱ j = 0 → ∀ a : Fin L × Fin L → ℝ,
        amp / 8 * ∑ j, |(ϱ j : ℝ)| + amp / (8 * D₁) * (chargeCoverCost boundary L ϱ : ℝ) ≤
          translationEnergy (clockShiftCost β n) (gradLinear Λ) a (fun j => (ϱ j : ℝ)) →
        |K i ϱ| * Real.exp (-translationEnergy (clockShiftCost β n) (gradLinear Λ) a
          (fun j => (ϱ j : ℝ))) ≤ linMemberWeight boundary s ϱ :=
      fun ϱ hϱ hϱn a ha => clock_renormalizedActivity_le h21 hL0 hζpos hleaf hs.le hamp1 hamp2
        ((hens i).1 ϱ hϱ) (hd ϱ hϱ hϱn) ha
    obtain ⟨hZ, hI⟩ := abs_clockMarkedBranch_le hL Λ hΛ hdist B h46 centerOf hcenter hβ hn h24
      (hens i) hNa hNb hNc (K i) (linMemberWeight boundary s)
      (fun ϱ hϱ => (hθle i ϱ hϱ).trans_lt (by norm_num)) hz hox hξ0 hξn hη hηξ hlamc0 hlamcn
      hcost
    refine ⟨hZ, hI.trans (mul_le_mul_of_nonneg_right ?_ hZ.le)⟩
    have hmono := markAdjacent_monotone (boundary := boundary) (dipoleMark_ne_zero hox)
    refine sum_le_of_le_explorationWeight hmono (N i) (linExplorationWeight boundary s)
      (fun ϱ hϱ => ?_) _ fun C hC => ?_
    · unfold linExplorationWeight
      split_ifs
      · exact (hθle i ϱ hϱ).trans_lt (by norm_num)
      · norm_num
    · split_ifs with hCn
      · exact linCluster_estimate hL hD₁ (by norm_num) h21 (hens i) hNa hNb (K i)
          (lamHat := lamHat') (h := h)
          (fun ϱ hϱ hϱn => by rw [hleafform]; exact hd ϱ hϱ hϱn)
          (fun ϱ _ => by
            rw [hleafform]
            calc ∏ j ∈ chargeSupport ϱ, mixtureLeaf Nq lamHat ζ j (ϱ j).natAbs
                ≤ ∏ j ∈ chargeSupport ϱ, Real.exp (h * ((ϱ j).natAbs : ℝ)) :=
                  Finset.prod_le_prod₀ (fun j _ => mixtureLeaf_nonneg lamHat hζpos j _)
                    fun j _ => hleaf j _
              _ = Real.exp (h * ∑ j ∈ chargeSupport ϱ, |(ϱ j : ℝ)|) := by
                  rw [← Real.exp_sum, Finset.mul_sum]
                  congr 1
                  refine Finset.sum_congr rfl fun j _ => ?_
                  rw [Nat.cast_natAbs, Int.cast_abs]
              _ = Real.exp (h * ∑ j, |(ϱ j : ℝ)|) := by
                  congr 2
                  refine Finset.sum_subset (Finset.subset_univ _) fun j _ hj => ?_
                  have : ϱ j = 0 := by
                    by_contra h'
                    exact hj (mem_chargeSupport'.2 h')
                  simp [this])
          hox hξ'0 hξ'1 hη hηξ hs hlamc0 C1 C2 C3 H4 hC hCn
      · have hπ0 : ∀ ϱ ∈ N i, 0 ≤ linExplorationWeight boundary s ϱ := fun ϱ _ => by
          unfold linExplorationWeight
          split_ifs
          · exact (linMemberWeight_pos s ϱ).le
          · norm_num
        have hπ1 : ∀ ϱ ∈ N i, linExplorationWeight boundary s ϱ ≤ 1 := fun ϱ hϱ => by
          unfold linExplorationWeight
          split_ifs
          · exact (hθle i ϱ hϱ).trans (by norm_num)
          · norm_num
        have hCN : C ⊆ N i := (mem_clusters.1 hC).1
        refine mul_nonneg (by positivity) (mul_nonneg
          (Finset.prod_nonneg fun ϱ hϱ => hπ0 ϱ (hCN hϱ))
          (Finset.prod_nonneg fun ϱ hϱ => ?_))
        have := hπ1 ϱ (Finset.mem_sdiff.1 hϱ).1
        linarith
  -- assemble the branches
  have hlamid : ∀ φ : Fin L × Fin L → ℝ, ∏ j, lam j (φ j) =
      ∑ i, cc i * ∏ ϱ ∈ N i, (1 + K i ϱ * Real.cos (∑ j, φ j * (ϱ j : ℝ))) := fun φ => hid φ
  have hint : ∀ i, Integrable (fun φ : Fin L × Fin L → ℝ =>
      ∏ ϱ ∈ N i, (1 + K i ϱ * Real.cos (∑ j, φ j * (ϱ j : ℝ)))) μ := fun i =>
    Reduction.integrable_prod_one_add_mul_cos μ (N i) (K i) (fun ϱ φ => ∑ j, φ j * (ϱ j : ℝ))
      (fun ϱ => by fun_prop)
  have hintc : ∀ i, Integrable (fun φ : Fin L × Fin L → ℝ =>
      Real.cos (ξ' * ∑ j, φ j * (dipoleMark o x j : ℝ)) *
        ∏ ϱ ∈ N i, (1 + K i ϱ * Real.cos (∑ j, φ j * (ϱ j : ℝ)))) μ := fun i =>
    (hint i).bdd_mul (c := 1) (Continuous.aestronglyMeasurable (by fun_prop))
      (ae_of_all _ fun φ => by rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)
  have hZ : ∫ φ, ∏ j, lam j (φ j) ∂μ =
      ∑ i, cc i * ∫ φ, ∏ ϱ ∈ N i, (1 + K i ϱ * Real.cos (∑ j, φ j * (ϱ j : ℝ))) ∂μ := by
    simp_rw [hlamid]
    rw [integral_finsetSum _ fun i _ => (hint i).const_mul (cc i)]
    simp_rw [integral_const_mul]
  have hI : ∫ φ, Real.cos (ξ' * (φ o - φ x)) * ∏ j, lam j (φ j) ∂μ =
      ∑ i, cc i * ∫ φ, Real.cos (ξ' * ∑ j, φ j * (dipoleMark o x j : ℝ)) *
        ∏ ϱ ∈ N i, (1 + K i ϱ * Real.cos (∑ j, φ j * (ϱ j : ℝ))) ∂μ := by
    have hpt : ∀ φ : Fin L × Fin L → ℝ,
        Real.cos (ξ' * (φ o - φ x)) * ∏ j, lam j (φ j) =
        ∑ i, cc i * (Real.cos (ξ' * ∑ j, φ j * (dipoleMark o x j : ℝ)) *
          ∏ ϱ ∈ N i, (1 + K i ϱ * Real.cos (∑ j, φ j * (ϱ j : ℝ)))) := by
      intro φ
      rw [hlamid, Finset.mul_sum, sum_mul_dipoleMark]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [integral_congr_ae (ae_of_all _ hpt),
      integral_finsetSum _ fun i _ => (hintc i).const_mul (cc i)]
    simp_rw [integral_const_mul]
  have hne : (Finset.univ : Finset (Fin m)).Nonempty := by
    by_contra h'
    rw [Finset.not_nonempty_iff_eq_empty] at h'
    rw [h', Finset.sum_empty] at hcsum
    exact zero_ne_one hcsum
  refine ⟨?_, ?_⟩
  · rw [hZ]
    exact Finset.sum_pos (fun i _ => mul_pos (hcpos i) (hbranch i).1) hne
  · rw [hI, hZ, Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [abs_mul, abs_of_pos (hcpos i), mul_left_comm]
    exact mul_le_mul_of_nonneg_left (hbranch i).2 (hcpos i).le

end DomainBound

end FroehlichSpencer.BKT.Clock.Compact

end
