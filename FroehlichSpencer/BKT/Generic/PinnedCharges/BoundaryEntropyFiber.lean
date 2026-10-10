/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.PinnedCharges.BoundaryEntropyDepth

/-! # Fiber counts for the shifted pinned scale map

The source recurrence acts on integer scales. This file transfers its
preimage-count estimate to the clamped natural scales used by the pinned
cover numbers; finite support ensures that the separated profile has exactly
the same total mass after shifting by eight.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic.PinnedCharges

open FroehlichSpencer.BKT

/-- Extend a natural scale profile to the shifted integer scale coordinate. -/
def boundaryEntropyIntProfile (P : ℕ → ℝ) (q : ℤ) : ℝ :=
  P (boundaryEntropyPhi q)

private theorem boundaryEntropyPhi_cast_eq_sub {q : ℤ} (hq : 8 ≤ q) :
    (boundaryEntropyPhi q : ℤ) = q - 8 := by
  unfold boundaryEntropyPhi
  exact Int.toNat_of_nonneg (by omega)

private theorem boundaryEntropyPhi_zero_of_le_eight {q : ℤ} (hq : q ≤ 8) :
    boundaryEntropyPhi q = 0 := by
  unfold boundaryEntropyPhi
  rw [Int.toNat_of_nonpos (by omega)]

private theorem boundaryEntropyIntProfile_support_subset {n : ℕ} (P : ℕ → ℝ)
    (hzero : P 0 = 0) (htail : ∀ j, n < j → P j = 0) :
    Function.support (boundaryEntropyIntProfile P) ⊆
      Set.Icc (9 : ℤ) ((n : ℤ) + 8) := by
  intro q hq
  have hP : P (boundaryEntropyPhi q) ≠ 0 := by
    simpa [Function.support, boundaryEntropyIntProfile] using hq
  have hphi0 : boundaryEntropyPhi q ≠ 0 := by
    intro h
    apply hP
    simpa [h] using hzero
  have hphiLe : boundaryEntropyPhi q ≤ n := by
    by_contra h
    have hz := htail (boundaryEntropyPhi q) (by omega)
    exact hP hz
  have hphiPos : 1 ≤ boundaryEntropyPhi q := Nat.one_le_iff_ne_zero.mpr hphi0
  have hq8 : 8 ≤ q := by
    by_contra h
    have hqle : q ≤ 8 := by omega
    exact hphi0 (boundaryEntropyPhi_zero_of_le_eight hqle)
  have hcast := boundaryEntropyPhi_cast_eq_sub hq8
  have hlow : (1 : ℤ) ≤ (boundaryEntropyPhi q : ℤ) := by exact_mod_cast hphiPos
  have hupp : (boundaryEntropyPhi q : ℤ) ≤ n := by exact_mod_cast hphiLe
  rw [hcast] at hlow hupp
  exact ⟨by omega, by omega⟩

/-- A profile with finite natural support has finite support after the shift. -/
theorem boundaryEntropyIntProfile_summable {n : ℕ} (P : ℕ → ℝ)
    (hzero : P 0 = 0) (htail : ∀ j, n < j → P j = 0) :
    Summable (boundaryEntropyIntProfile P) := by
  have hfinite : (Function.support (boundaryEntropyIntProfile P)).Finite :=
    (Set.finite_Icc 9 ((n : ℤ) + 8)).subset
      (boundaryEntropyIntProfile_support_subset P hzero htail)
  exact summable_of_hasFiniteSupport hfinite

/-- The integer and natural profiles have equal total mass. -/
theorem boundaryEntropyIntProfile_tsum_eq {n : ℕ} (P : ℕ → ℝ)
    (hzero : P 0 = 0) (htail : ∀ j, n < j → P j = 0) :
    (∑' q : ℤ, boundaryEntropyIntProfile P q) = ∑' j : ℕ, P j := by
  let sZ : Finset ℤ := Finset.Icc 9 ((n : ℤ) + 8)
  let sN : Finset ℕ := Finset.Icc 1 n
  have hZout : ∀ q, q ∉ sZ → boundaryEntropyIntProfile P q = 0 := by
    intro q hq
    by_contra hne
    have hsupp : q ∈ Function.support (boundaryEntropyIntProfile P) := hne
    have hmem := boundaryEntropyIntProfile_support_subset P hzero htail hsupp
    exact hq (by simpa [sZ, Finset.mem_Icc] using hmem)
  have hNout : ∀ j, j ∉ sN → P j = 0 := by
    intro j hj
    by_cases hj0 : j = 0
    · simpa [hj0] using hzero
    · have hjpos : 1 ≤ j := Nat.one_le_iff_ne_zero.mpr hj0
      have hgt : n < j := by
        by_contra h
        exact hj (by simp [sN, Finset.mem_Icc, hjpos, Nat.le_of_not_gt h])
      exact htail j hgt
  rw [tsum_eq_sum (s := sZ) hZout, tsum_eq_sum (s := sN) hNout]
  apply Finset.sum_bij'
    (s := sZ) (t := sN)
    (i := fun q _ => boundaryEntropyPhi q)
    (j := fun j _ => (j : ℤ) + 8)
  · intro q hq
    have hqlo : (9 : ℤ) ≤ q := (Finset.mem_Icc.mp hq).1
    have hqhi : q ≤ (n : ℤ) + 8 := (Finset.mem_Icc.mp hq).2
    have hcast := boundaryEntropyPhi_cast_eq_sub (by omega : 8 ≤ q)
    have hlow : (1 : ℤ) ≤ (boundaryEntropyPhi q : ℤ) := by rw [hcast]; omega
    have hupp : (boundaryEntropyPhi q : ℤ) ≤ n := by rw [hcast]; omega
    change boundaryEntropyPhi q ∈ Finset.Icc 1 n
    exact Finset.mem_Icc.mpr ⟨by exact_mod_cast hlow, by exact_mod_cast hupp⟩
  · intro j hj
    have hjlo : 1 ≤ j := (Finset.mem_Icc.mp hj).1
    have hjhi : j ≤ n := (Finset.mem_Icc.mp hj).2
    change (j : ℤ) + 8 ∈ Finset.Icc 9 ((n : ℤ) + 8)
    apply Finset.mem_Icc.mpr
    constructor <;> exact_mod_cast (by omega)
  · intro q hq
    have hqlo : (9 : ℤ) ≤ q := (Finset.mem_Icc.mp hq).1
    have hq8 : (8 : ℤ) ≤ q := le_trans (by norm_num) hqlo
    have hcast := boundaryEntropyPhi_cast_eq_sub hq8
    change (boundaryEntropyPhi q : ℤ) + 8 = q
    rw [hcast]
    omega
  · intro j hj
    have hphi : boundaryEntropyPhi ((j : ℤ) + 8) = j := by
      unfold boundaryEntropyPhi
      have hsub : (j : ℤ) + 8 - 8 = (j : ℤ) := by omega
      rw [hsub]
      simp
    simp [hphi]
  · intro q hq
    rfl

/-- One shifted recurrence layer is bounded by the exact KP fiber constant
times the total separated profile. -/
theorem boundaryEntropy_nat_layer_sum_bound (n m : ℕ) (P : ℕ → ℝ)
    (hzero : P 0 = 0) (htail : ∀ j, n < j → P j = 0)
    (hPnonneg : ∀ j, 0 ≤ P j) :
    (∑ k ∈ Finset.range (n + 1),
      P (boundaryEntropyIterate boundaryEntropyGamma (m + 1) k)) ≤
      (14 / 3 : ℝ) * (7 / 4 : ℝ) ^ (m + 1) * ∑' j : ℕ, P j := by
  let f := boundaryEntropyIntProfile P
  have hf : Summable f := boundaryEntropyIntProfile_summable P hzero htail
  have hfnn : ∀ q, 0 ≤ f q := by
    intro q
    exact hPnonneg _
  have hprofile := boundaryEntropyIntProfile_tsum_eq P hzero htail
  have hsource :
      (∑ k ∈ Finset.range (n + 1),
        P (boundaryEntropyIterate boundaryEntropyGamma (m + 1) k)) =
      ∑ k ∈ Finset.range (n + 1),
        f (recurrenceIterate (m + 1) ((k : ℤ) + 8)) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hphi := boundaryEntropyIterate_eq_phi (m + 1) ((k : ℤ) + 8)
    have hstart : boundaryEntropyPhi ((k : ℤ) + 8) = k := by
      unfold boundaryEntropyPhi
      have hsub : (k : ℤ) + 8 - 8 = (k : ℤ) := by omega
      rw [hsub]
      simp
    rw [hstart] at hphi
    change P (boundaryEntropyIterate boundaryEntropyGamma (m + 1) k) =
      P (boundaryEntropyPhi (recurrenceIterate (m + 1) ((k : ℤ) + 8)))
    exact congrArg P hphi
  rw [hsource]
  let g : ℕ → ℝ := fun q => f (recurrenceIterate (m + 1) (q : ℤ))
  let s : Finset ℕ := (Finset.range (n + 1)).image (fun k => k + 8)
  have hinj : Set.InjOn (fun k : ℕ => k + 8) (Finset.range (n + 1) : Set ℕ) := by
    intro a ha b hb hab
    exact Nat.add_right_cancel hab
  have himage : (∑ k ∈ Finset.range (n + 1), g (k + 8)) =
      ∑ q ∈ s, g q := by
    rw [Finset.sum_image hinj]
  have hsubset : s ⊆ Finset.range (n + 8 + 1) := by
    intro q hq
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hq
    simp only [Finset.mem_range] at hk ⊢
    omega
  have hgnn : ∀ q, 0 ≤ g q := fun q => hfnn _
  have hshiftBound :
      (∑ k ∈ Finset.range (n + 1),
        f (recurrenceIterate (m + 1) ((k : ℤ) + 8))) ≤
      ∑ q ∈ Finset.range (n + 8 + 1), g q := by
    have hcastSum :
        (∑ k ∈ Finset.range (n + 1),
          f (recurrenceIterate (m + 1) ((k : ℤ) + 8))) =
        ∑ k ∈ Finset.range (n + 1), g (k + 8) := by
      apply Finset.sum_congr rfl
      intro k hk
      simp [g]
    rw [hcastSum, himage]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun q _ _ => hgnn q)
  calc
    _ ≤ (14 / 3 : ℝ) * (7 / 4 : ℝ) ^ (m + 1) * ∑' q : ℤ, f q := by
      calc
        _ ≤ ∑ q ∈ Finset.range (n + 8 + 1), g q := hshiftBound
        _ ≤ (14 / 3 : ℝ) * (7 / 4 : ℝ) ^ (m + 1) * ∑' q : ℤ, f q := by
          simpa [g] using recurrenceIterate_layer_sum_bound m (n + 8) f hf hfnn
    _ = (14 / 3 : ℝ) * (7 / 4 : ℝ) ^ (m + 1) * ∑' j : ℕ, P j := by
      exact congrArg
        (fun z : ℝ => (14 / 3 : ℝ) * (7 / 4 : ℝ) ^ (m + 1) * z)
        (by simpa [f] using hprofile)

end FroehlichSpencer.BKT.Generic.PinnedCharges

end
