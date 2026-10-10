/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.Marked.Renormalization
public import FroehlichSpencer.BKT.Charges.DensityBall
public import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# Exploration weights and the neighbours of a cluster

* `sum_explorationWeight_eq_one`, `sum_le_of_le_explorationWeight`: for a monotone adjacency, the
  weights `p_C = ∏_C π ∏_{∂C} (1 − π)` of the clusters sum to one, where
  `∂C = N ∖ (C ∪ rem(C))`. This is the regrouping identity `prod_one_add_eq_sum_clusters` at
  `u = π/(1 − π)`. It turns the cluster sum of the marked branch bound into a maximum.
* `card_le_of_near`, **`sum_neighbourWeight_le`**: the neutral members adjacent to a neutral
  cluster `C` but outside it carry total weight
  `∑ e^{-(c/β)(‖m‖² + log₂(d(m)+1))} ≤ 288 M² e^{-c/β} |X|`.
  - A neighbour of diameter `< 2^{k+1}` lies within `M 4^{k+1}` of `X`.
  - Members have disjoint supports, so there are at most `|X| (2M 4^{k+1} + 1)²` of them at
    each scale `k`.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic.Marked

open Reduction

/-! ### Exploration weights -/

section Exploration

variable {ι : Type*} [DecidableEq ι] {adj : ι → Finset ι → Prop}

/-- **Exploration weights sum to one.** For a monotone adjacency and `π_m < 1`, the weights
`p_C = ∏_{m ∈ C} π_m ∏_{m ∈ ∂C} (1 - π_m)`, `∂C = N ∖ (C ∪ rem(C))`, of the clusters of `N` sum
to one (`prod_one_add_eq_sum_clusters` with `u = π/(1 - π)`). A bound `Y_C ≤ ε p_C` on every
cluster then gives `∑_C Y_C ≤ ε`. -/
theorem sum_explorationWeight_eq_one (hmono : AdjMonotone adj) (N : Finset ι) (π : ι → ℝ)
    (hπ : ∀ m ∈ N, π m < 1) :
    ∑ C ∈ clusters adj N, (∏ m ∈ C, π m) * ∏ m ∈ N \ (C ∪ remainder adj N C), (1 - π m) = 1 := by
  classical
  have hpos : ∀ m ∈ N, 0 < 1 - π m := fun m hm => by linarith [hπ m hm]
  have hone : ∀ m ∈ N, 1 + π m / (1 - π m) = 1 / (1 - π m) := fun m hm => by
    field_simp [(hpos m hm).ne']
    ring
  have key := prod_one_add_eq_sum_clusters hmono N (fun m => π m / (1 - π m))
  rw [Finset.prod_congr rfl hone] at key
  have hP : (∏ m ∈ N, (1 - π m)) * ∏ m ∈ N, (1 / (1 - π m)) = 1 := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun m hm => by field_simp [(hpos m hm).ne']
  have hterm : ∀ C ∈ clusters adj N,
      (∏ m ∈ C, π m) * ∏ m ∈ N \ (C ∪ remainder adj N C), (1 - π m) =
        (∏ m ∈ N, (1 - π m)) * ((∏ m ∈ C, π m / (1 - π m)) *
          ∏ m ∈ remainder adj N C, (1 / (1 - π m))) := by
    intro C hC
    have hCN : C ⊆ N := (mem_clusters.1 hC).1
    have hRN : remainder adj N C ⊆ N := remainder_subset N C
    have hdisj : Disjoint C (remainder adj N C) := disjoint_remainder N C
    have hU : C ∪ remainder adj N C ⊆ N := Finset.union_subset hCN hRN
    rw [← Finset.prod_sdiff hU, Finset.prod_union hdisj]
    have hC1 : (∏ m ∈ C, (1 - π m)) * ∏ m ∈ C, (π m / (1 - π m)) = ∏ m ∈ C, π m := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun m hm => by field_simp [(hpos m (hCN hm)).ne']
    have hR1 : (∏ m ∈ remainder adj N C, (1 - π m)) *
        ∏ m ∈ remainder adj N C, (1 / (1 - π m)) = 1 := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_eq_one fun m hm => by field_simp [(hpos m (hRN hm)).ne']
    calc (∏ m ∈ C, π m) * ∏ m ∈ N \ (C ∪ remainder adj N C), (1 - π m)
        = (∏ m ∈ N \ (C ∪ remainder adj N C), (1 - π m)) *
            ((∏ m ∈ C, (1 - π m)) * ∏ m ∈ C, (π m / (1 - π m))) *
            ((∏ m ∈ remainder adj N C, (1 - π m)) *
              ∏ m ∈ remainder adj N C, (1 / (1 - π m))) := by rw [hC1, hR1]; ring
      _ = _ := by ring
  have hrem : ∀ C ∈ clusters adj N, ∏ m ∈ remainder adj N C, (1 + π m / (1 - π m)) =
      ∏ m ∈ remainder adj N C, (1 / (1 - π m)) := fun C _ =>
    Finset.prod_congr rfl fun m hm => hone m (remainder_subset N C hm)
  calc ∑ C ∈ clusters adj N, (∏ m ∈ C, π m) * ∏ m ∈ N \ (C ∪ remainder adj N C), (1 - π m)
      = ∑ C ∈ clusters adj N, (∏ m ∈ N, (1 - π m)) * ((∏ m ∈ C, π m / (1 - π m)) *
          ∏ m ∈ remainder adj N C, (1 + π m / (1 - π m))) :=
        Finset.sum_congr rfl fun C hC => by rw [hterm C hC, hrem C hC]
    _ = (∏ m ∈ N, (1 - π m)) * ∏ m ∈ N, (1 / (1 - π m)) := by
        rw [← Finset.mul_sum, ← key]
    _ = 1 := hP

/-- A family bounded by `ε` times the exploration weights sums to at most `ε`. -/
theorem sum_le_of_le_explorationWeight (hmono : AdjMonotone adj) (N : Finset ι) (π : ι → ℝ)
    (hπ : ∀ m ∈ N, π m < 1) (Y : Finset ι → ℝ) {ε : ℝ}
    (hY : ∀ C ∈ clusters adj N,
      Y C ≤ ε * ((∏ m ∈ C, π m) * ∏ m ∈ N \ (C ∪ remainder adj N C), (1 - π m))) :
    ∑ C ∈ clusters adj N, Y C ≤ ε := by
  calc ∑ C ∈ clusters adj N, Y C
      ≤ ∑ C ∈ clusters adj N,
          ε * ((∏ m ∈ C, π m) * ∏ m ∈ N \ (C ∪ remainder adj N C), (1 - π m)) :=
        Finset.sum_le_sum hY
    _ = ε := by rw [← Finset.mul_sum, sum_explorationWeight_eq_one hmono N π hπ, mul_one]

end Exploration

/-! ### The neighbours of a cluster -/

section Count

variable {boundary : SquareBoundary} {L : ℕ}

/-- **A packing count.** Members with pairwise disjoint supports, each with a point within
distance `r` of a set `X`, number at most `|X| (2r + 1)²`. -/
theorem card_le_of_near (F : Finset (ChargeDensity L))
    (hdisj : ∀ m ∈ F, ∀ m' ∈ F, m ≠ m' → Disjoint (Function.support m) (Function.support m'))
    (X : Finset (Fin L × Fin L)) (r : ℕ)
    (hnear : ∀ m ∈ F, ∃ y, m y ≠ 0 ∧ ∃ x ∈ X, latticeDistance boundary L y x ≤ r) :
    F.card ≤ X.card * (2 * r + 1) ^ 2 := by
  classical
  rcases F.eq_empty_or_nonempty with hF | ⟨m₀, hm₀⟩
  · simp [hF]
  obtain ⟨y₀, -, -⟩ := hnear m₀ hm₀
  have : Nonempty (Fin L × Fin L) := ⟨y₀⟩
  choose! y hy x hx hd using hnear
  set t := X.biUnion fun x => Finset.univ.filter fun ℓ => latticeDistance boundary L ℓ x ≤ r
    with ht
  have hmaps : ∀ m ∈ F, y m ∈ t := fun m hm =>
    Finset.mem_biUnion.2 ⟨x m, hx m hm, Finset.mem_filter.2 ⟨Finset.mem_univ _, hd m hm⟩⟩
  have hinj : Set.InjOn y F := by
    intro m hm m' hm' heq
    by_contra hne
    have h1 : m (y m) ≠ 0 := hy m hm
    have h2 : m' (y m) ≠ 0 := by rw [heq]; exact hy m' hm'
    exact Set.disjoint_left.1 (hdisj m hm m' hm' hne) h1 h2
  calc F.card ≤ t.card := Finset.card_le_card_of_injOn y hmaps hinj
    _ ≤ ∑ x ∈ X, (Finset.univ.filter fun ℓ => latticeDistance boundary L ℓ x ≤ r).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _x ∈ X, (2 * r + 1) ^ 2 :=
        Finset.sum_le_sum fun x _ => card_latticeDistance_le_le boundary L r x
    _ = X.card * (2 * r + 1) ^ 2 := by rw [Finset.sum_const, smul_eq_mul]

/-- **The weight of the neighbours of a neutral cluster.** For a neutral marked cluster `C` of a
KP ensemble (dipole mark), the neutral members adjacent to `C` but outside it carry total weight
`∑ e^{-(c/β)(‖m‖² + log₂(d(m) + 1))} ≤ 288 M² e^{-c/β} |X|`, `X = supp ϱ₀ ∪ ⋃ C`, provided
`e^{-c/β} ≤ 1/32`. A neighbour of diameter `d < 2^{k+1}` comes within `M d^{7/4} ≤ M 4^{k+1}` of
`X` (`MarkAdjacent` at the neutral scale `min(d(m), d(X)) ≤ d(m)`), so each scale has at most
`|X| (2M 4^{k+1} + 1)²` of them (`card_le_of_near`), and the weights sum geometrically. -/
theorem sum_neighbourWeight_le (hL : 1 < L) {N : Finset (ChargeDensity L)}
    (hens : IsChargeEnsemble N) {o x : Fin L × Fin L} (hox : o ≠ x)
    {C : Finset (ChargeDensity L)} (hCn : ∀ m ∈ C, ∑ j, m j = 0) {c β : ℝ} (hc : 0 < c)
    (hβ : 0 < β) (hq : Real.exp (-(c / β)) ≤ 1 / 32) :
    ∑ m ∈ (N \ (C ∪ markedRemainder boundary L (dipoleMark o x) N C)).filter
        (fun m => ∑ j, m j = 0),
      Real.exp (-(c / β) * (∑ j, (m j : ℝ) ^ 2 +
        Real.logb 2 (chargeDiameter boundary L m + 1))) ≤
      288 * (chargeCoverScale : ℝ) ^ 2 * Real.exp (-(c / β)) *
        (markedSupport L (dipoleMark o x) C).card := by
  classical
  set ρ₀ := dipoleMark o x with hρ₀
  set X := markedSupport L ρ₀ C with hX
  set F := (N \ (C ∪ markedRemainder boundary L ρ₀ N C)).filter (fun m => ∑ j, m j = 0) with hF
  set q := Real.exp (-(c / β)) with hqdef
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
  have hweight : ∀ m ∈ F, Real.exp (-(c / β) * (∑ j, (m j : ℝ) ^ 2 +
      Real.logb 2 (chargeDiameter boundary L m + 1))) ≤ q * q ^ kf m := by
    intro m hm
    have hm0 := hens.1 m (hFmem m hm).1
    obtain ⟨j₀, hj₀⟩ : ∃ j, m j ≠ 0 := by
      by_contra h
      push Not at h
      exact hm0 (funext h)
    have hs : (1 : ℝ) ≤ ∑ j, (m j : ℝ) ^ 2 := by
      have h1 : (1 : ℝ) ≤ (m j₀ : ℝ) ^ 2 := by
        have : (1 : ℝ) ≤ |(m j₀ : ℝ)| := by
          rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hj₀
        nlinarith [abs_nonneg (m j₀ : ℝ), sq_abs (m j₀ : ℝ)]
      exact h1.trans (Finset.single_le_sum (fun j _ => sq_nonneg (m j : ℝ))
        (Finset.mem_univ j₀))
    have hl : (kf m : ℝ) ≤ Real.logb 2 (chargeDiameter boundary L m + 1) := by
      have hpow : (2 : ℝ) ^ kf m ≤ (chargeDiameter boundary L m : ℝ) + 1 := by
        have := Nat.pow_log_le_self 2 (Nat.succ_ne_zero (chargeDiameter boundary L m))
        exact_mod_cast this
      rw [Real.le_logb_iff_rpow_le (by norm_num) (by positivity), Real.rpow_natCast]
      exact_mod_cast hpow
    have hcb : 0 < c / β := div_pos hc hβ
    rw [hqdef, ← Real.exp_nat_mul, ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    nlinarith
  -- sum by scale classes
  have hF_le : ∑ m ∈ F, Real.exp (-(c / β) * (∑ j, (m j : ℝ) ^ 2 +
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

end FroehlichSpencer.BKT.Generic.Marked
