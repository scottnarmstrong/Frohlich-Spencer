/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.Infra.ProductMeasure
public import FroehlichSpencer.Infra.Combinatorics.Animals

/-!
# Independence over disjoint blocks

Product formula for events depending on pairwise disjoint sets of sites, and the bound
`P(⋂ A_k) ≤ q ^ |⋃ S_k|` when `P(A_k) ≤ q ^ |S_k|`, as used in Fröhlich–Spencer (1983),
Sects. 5–6 (Fröhlich–Spencer (1983)).
-/

@[expose] public section

namespace FroehlichSpencer.Infra

section Independent

open MeasureTheory
open scoped ENNReal

variable {ι κ : Type*}

theorem productMeasure_biInter_eq_prod (μ : Measure ℝ) [IsProbabilityMeasure μ] (F : Finset κ)
    (S : κ → Set ι) (hS : (F : Set κ).PairwiseDisjoint S) (A : κ → Set (ι → ℝ))
    (hA : ∀ k ∈ F, DependsOn (S k) (A k)) :
    productMeasure μ (⋂ k ∈ F, A k) = ∏ k ∈ F, productMeasure μ (A k) := by
  classical
  have h := (localSigma_iIndep (ι := ι) μ (fun k : F => S k) (fun i j hij =>
    hS i.2 j.2 (fun h => hij (Subtype.ext h)))).meas_iInter
    (s := fun k : F => A k) (fun k => hA k k.2)
  have e : (⋂ k ∈ F, A k) = ⋂ k : F, A k := by ext x; simp
  rw [e, h, Finset.prod_coe_sort F (fun k => productMeasure (ι := ι) μ (A k))]

theorem productMeasure_biInter_le_pow [DecidableEq ι] (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (F : Finset κ) (S : κ → Finset ι) (hS : (F : Set κ).PairwiseDisjoint S)
    (A : κ → Set (ι → ℝ)) (hA : ∀ k ∈ F, DependsOn (S k : Set ι) (A k)) {q : ℝ≥0∞}
    (hq : ∀ k ∈ F, productMeasure μ (A k) ≤ q ^ (S k).card) :
    productMeasure μ (⋂ k ∈ F, A k) ≤ q ^ (F.biUnion S).card := by
  have hS' : (F : Set κ).PairwiseDisjoint (fun k => (S k : Set ι)) := fun i hi j hj hij =>
    Finset.disjoint_coe.2 (hS hi hj hij)
  rw [productMeasure_biInter_eq_prod μ F (fun k => (S k : Set ι)) hS' A hA,
    Finset.card_biUnion hS, ← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_le_prod hq

end Independent

section Animals

open MeasureTheory
open scoped ENNReal

variable {V : Type*} (G : SimpleGraph V)

private theorem measure_animals_level_le [G.LocallyFinite] {Δ : ℕ} (hΔ : ∀ v, G.degree v ≤ Δ)
    (x : V) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (B : Finset V → Set Ω)
    {q : ℝ≥0∞} (hB : ∀ m, ∀ D ∈ animals G x m, P (B D) ≤ q ^ m) (m : ℕ) :
    P (⋃ D ∈ animals G x m, B D) ≤
      if m = 0 then 0 else q * ((Δ : ℝ≥0∞) ^ 2 * q) ^ (m - 1) := by
  by_cases hm : m = 0
  · subst hm
    have : animals G x 0 = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun S hS => ?_
      obtain ⟨hx, hc, -⟩ := (mem_animals G).1 hS
      simp [Finset.card_eq_zero.1 hc] at hx
    simp [this]
  · simp only [hm, ↓reduceIte]
    calc P (⋃ D ∈ animals G x m, B D) ≤ ∑ D ∈ animals G x m, P (B D) :=
          measure_biUnion_finset_le _ _
      _ ≤ ∑ _D ∈ animals G x m, q ^ m := Finset.sum_le_sum (hB m)
      _ = (animals G x m).card * q ^ m := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((Δ ^ (2 * (m - 1)) : ℕ) : ℝ≥0∞) * q ^ m := by
          gcongr
          exact_mod_cast card_animals_le G hΔ x m
      _ = q * ((Δ : ℝ≥0∞) ^ 2 * q) ^ (m - 1) := by
          obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
          rw [Nat.cast_pow, Nat.succ_sub_one, pow_succ, mul_pow, pow_mul]
          ring

theorem measure_iUnion_animals_le [G.LocallyFinite] {Δ : ℕ} (hΔ : ∀ v, G.degree v ≤ Δ) (x : V)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (B : Finset V → Set Ω) {q : ℝ≥0∞}
    (hB : ∀ m, ∀ D ∈ animals G x m, P (B D) ≤ q ^ m) (n : ℕ) :
    P (⋃ m, ⋃ (_ : n ≤ m), ⋃ D ∈ animals G x m, B D) ≤
      q * ((Δ : ℝ≥0∞) ^ 2 * q) ^ (n - 1) * (1 - (Δ : ℝ≥0∞) ^ 2 * q)⁻¹ := by
  set r : ℝ≥0∞ := (Δ : ℝ≥0∞) ^ 2 * q with hr
  have h1 : P (⋃ m, ⋃ (_ : n ≤ m), ⋃ D ∈ animals G x m, B D) ≤
      ∑' m, (if n - 1 + 1 ≤ m then q * r ^ (m - 1) else 0) := by
    refine (measure_iUnion_le _).trans (ENNReal.tsum_le_tsum fun m => ?_)
    by_cases hnm : n ≤ m
    · have e : (⋃ (_ : n ≤ m), ⋃ D ∈ animals G x m, B D) = ⋃ D ∈ animals G x m, B D := by
        ext; simp [hnm]
      rw [e]
      refine (measure_animals_level_le G hΔ x P B hB m).trans ?_
      by_cases hm : m = 0
      · simp [hm]
      · simp only [hm, ↓reduceIte, show n - 1 + 1 ≤ m by omega]; exact le_rfl
    · have e : (⋃ (_ : n ≤ m), ⋃ D ∈ animals G x m, B D) = ∅ := by ext; simp [hnm]
      rw [e, measure_empty]
      exact zero_le
  refine h1.trans (le_of_eq ?_)
  have h2 : ∀ k, (fun m => if n - 1 + 1 ≤ m then q * r ^ (m - 1) else 0) (k + (n - 1 + 1))
      = q * r ^ (n - 1) * r ^ k := fun k => by
    have e1 : n - 1 + 1 ≤ k + (n - 1 + 1) := by omega
    have e2 : k + (n - 1 + 1) - 1 = (n - 1) + k := by omega
    simp only [e1, ↓reduceIte, e2, pow_add]
    rw [mul_assoc]
  have h3 : ∑ i ∈ Finset.range (n - 1 + 1),
      (fun m => if n - 1 + 1 ≤ m then q * r ^ (m - 1) else 0) i = 0 :=
    Finset.sum_eq_zero fun i hi => by
      have : ¬ n - 1 + 1 ≤ i := by simpa using hi
      simp only [this, ↓reduceIte]
  have h4 := Summable.sum_add_tsum_nat_add' (k := n - 1 + 1)
    (f := fun m => if n - 1 + 1 ≤ m then q * r ^ (m - 1) else 0) ENNReal.summable
  rw [h3, zero_add] at h4
  refine h4.symm.trans ?_
  simp only [h2]
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]

theorem measurableSet_iUnion_animals [G.LocallyFinite] (x : V) {Ω : Type*} [MeasurableSpace Ω]
    (B : Finset V → Set Ω) (hB : ∀ D, MeasurableSet (B D)) (n : ℕ) :
    MeasurableSet (⋃ m, ⋃ (_ : n ≤ m), ⋃ D ∈ animals G x m, B D) :=
  MeasurableSet.iUnion fun m => MeasurableSet.iUnion fun _ =>
    MeasurableSet.biUnion (animals G x m).countable_toSet fun D _ => hB D

theorem measure_iUnion_animals_latticeGraph_le {ν : ℕ} (x : Fin ν → ℤ) {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) (B : Finset (Fin ν → ℤ) → Set Ω) {q : ℝ≥0∞}
    (hB : ∀ m, ∀ D ∈ animals (latticeGraph ν) x m, P (B D) ≤ q ^ m) (n : ℕ) :
    P (⋃ m, ⋃ (_ : n ≤ m), ⋃ D ∈ animals (latticeGraph ν) x m, B D) ≤
      q * (((2 * ν : ℕ) : ℝ≥0∞) ^ 2 * q) ^ (n - 1) *
        (1 - ((2 * ν : ℕ) : ℝ≥0∞) ^ 2 * q)⁻¹ :=
  measure_iUnion_animals_le (latticeGraph ν) (fun v => (latticeGraph_degree v).le) x P B hB n

end Animals

end FroehlichSpencer.Infra
