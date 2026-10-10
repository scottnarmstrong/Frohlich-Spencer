/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Ginibre.Closure
public import FroehlichSpencer.BKT.Ginibre.VillainSeries

/-!
# Villain bond weights in the closed Ginibre cone

The duplicated Villain weight `w_{β₁}(φ) w_{β₂}(φ')`, `0 < β₂ ≤ β₁`, is the bounded pointwise
limit of the evaluations of the formal polynomials `villainApprox`. After the sum–difference change
of frequencies these become the nonnegative combinations of tensor squares
`Σ_{k ≤ N} Σ_{ε = ±1} (c^k / 2k!) Y_{k,ε} ⊗ Y_{k,ε}`, `Y_{k,ε} = Σ_{|s| ≤ N} ε^s s^k e^{−a s²} e_{s d}`,
since `Σ_ε ε^s ε^t = 2·1[s + t even]` and `e^{c s t} = Σ_k (c s t)^k / k!`. The one-copy Villain
weight against the constant `1` (a bond present in one copy only) is the limit of diagonal
squares `e^{−p²/(2β)} e_{p d} ⊗ e_{p d}`. Hence `(w_{β₁}, w_{β₂})` and `(w_β, 1)` are Ginibre pairs.
-/

@[expose] public section

open AddMonoidAlgebra MeasureTheory Filter Topology
open FroehlichSpencer.BKT.Rotator.Ginibre
open scoped Real

noncomputable section

namespace FroehlichSpencer.BKT.Ginibre

variable {V : Type*}

theorem IsSquareSum.finsetSum {ι : Type*} (s : Finset ι) {P : ι → DupTrigAlgebra V}
    (hP : ∀ i ∈ s, IsSquareSum (P i)) : IsSquareSum (∑ i ∈ s, P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (IsSquareSum.zero : IsSquareSum (0 : DupTrigAlgebra V))
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (hP a (Finset.mem_insert_self a s)).add
        (ih fun i hi => hP i (Finset.mem_insert_of_mem hi))

theorem sum_single_eq {ι : Type*} (s : Finset ι) (g : Frequency V × Frequency V) (f : ι → ℝ) :
    (∑ i ∈ s, single g (f i) : DupTrigAlgebra V) = single g (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ih, single_add]

theorem tensor_sum_single {ι κ : Type*} (s : Finset ι) (t : Finset κ) (m : ι → Frequency V)
    (n : κ → Frequency V) (f : ι → ℝ) (g : κ → ℝ) :
    tensor (∑ i ∈ s, single (m i) (f i)) (∑ j ∈ t, single (n j) (g j)) =
      ∑ i ∈ s, ∑ j ∈ t, single (m i, n j) (f i * g j) := by
  rw [tensor, map_sum, map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  exact tensor_single_single _ _ _ _

theorem sum_comm4 {κ ε σ τ M : Type*} [AddCommMonoid M] (K : Finset κ) (E : Finset ε)
    (S : Finset σ) (T : Finset τ) (f : κ → ε → σ → τ → M) :
    ∑ k ∈ K, ∑ e ∈ E, ∑ s ∈ S, ∑ t ∈ T, f k e s t = ∑ s ∈ S, ∑ t ∈ T, ∑ k ∈ K, ∑ e ∈ E, f k e s t :=
  calc ∑ k ∈ K, ∑ e ∈ E, ∑ s ∈ S, ∑ t ∈ T, f k e s t
      = ∑ k ∈ K, ∑ s ∈ S, ∑ e ∈ E, ∑ t ∈ T, f k e s t :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ k ∈ K, ∑ s ∈ S, ∑ t ∈ T, ∑ e ∈ E, f k e s t :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ s ∈ S, ∑ k ∈ K, ∑ t ∈ T, ∑ e ∈ E, f k e s t := Finset.sum_comm
    _ = ∑ s ∈ S, ∑ t ∈ T, ∑ k ∈ K, ∑ e ∈ E, f k e s t :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm

variable [Fintype V]

theorem phase_zsmul (p : ℤ) (d : Frequency V) (θ : V → ℝ) :
    phase (p • d) θ = p * phase d θ := by
  simp only [phase, Pi.smul_apply, smul_eq_mul, Int.cast_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  ring

/-! ### The duplicated Villain approximants -/

/-- The coefficient of the duplicated Villain approximant at the sum–difference frequencies
`(s, t)`. -/
def villainCoef (β₁ β₂ : ℝ) (N : ℕ) (s t : ℤ) : ℝ :=
  if Even (s + t) then
    Real.exp (-(villainA β₁ β₂) * ((s : ℝ) ^ 2 + (t : ℝ) ^ 2)) *
      ∑ k ∈ Finset.range (N + 1), (villainC β₁ β₂ * s * t) ^ k / (Nat.factorial k : ℝ)
  else 0

/-- The duplicated Villain approximant along the bond frequency `d`. -/
def villainApprox (β₁ β₂ : ℝ) (d : Frequency V) (N : ℕ) : DupTrigAlgebra V :=
  ∑ s ∈ Finset.Icc (-(N : ℤ)) N, ∑ t ∈ Finset.Icc (-(N : ℤ)) N,
    single (((s + t) / 2) • d, ((s - t) / 2) • d) (villainCoef β₁ β₂ N s t)

/-- The vectors whose tensor squares make up the approximant. -/
def villainSqVec (d : Frequency V) (N k : ℕ) (ε a : ℝ) : TrigAlgebra V :=
  ∑ s ∈ Finset.Icc (-(N : ℤ)) N, single (s • d) (ε ^ s * (s : ℝ) ^ k * Real.exp (-a * (s : ℝ) ^ 2))

theorem dupEval_villainApprox (β₁ β₂ : ℝ) (d : Frequency V) (N : ℕ)
    (z : (V → ℝ) × (V → ℝ)) :
    dupEval V (villainApprox β₁ β₂ d N) z = villainSeries β₁ β₂ N (phase d z.1) (phase d z.2) := by
  simp only [villainApprox, villainSeries, map_sum, Finset.sum_apply, dupEval_single,
    character_eq_exp, phase_zsmul]
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
  simp only [villainTerm, villainCoef]
  split_ifs
  · push_cast
    ring
  · simp

theorem villain_parity_sum (s t : ℤ) :
    ∑ ε ∈ ({1, -1} : Finset ℝ), ε ^ s * ε ^ t = if Even (s + t) then 2 else 0 := by
  rw [Finset.sum_pair (by norm_num), one_zpow, one_zpow, ← zpow_add₀ (by norm_num : (-1 : ℝ) ≠ 0)]
  split_ifs with h
  · rw [h.neg_one_zpow]
    norm_num
  · rw [(Int.not_even_iff_odd.mp h).neg_one_zpow]
    norm_num

omit [Fintype V] in
theorem sumDiffMap_villainApprox (β₁ β₂ : ℝ) (d : Frequency V) (N : ℕ) :
    sumDiffMap V (villainApprox β₁ β₂ d N) =
      ∑ k ∈ Finset.range (N + 1), ∑ ε ∈ ({1, -1} : Finset ℝ),
        (villainC β₁ β₂ ^ k / (Nat.factorial k : ℝ) / 2) •
          tensor (villainSqVec d N k ε (villainA β₁ β₂)) (villainSqVec d N k ε (villainA β₁ β₂)) := by
  classical
  -- the left side as a sum over the square of frequencies
  have hL : sumDiffMap V (villainApprox β₁ β₂ d N) =
      ∑ s ∈ Finset.Icc (-(N : ℤ)) N, ∑ t ∈ Finset.Icc (-(N : ℤ)) N,
        (single (s • d, t • d) (villainCoef β₁ β₂ N s t) : DupTrigAlgebra V) := by
    simp only [villainApprox, map_sum, sumDiffMap, mapDomainRingHom_apply, mapDomain_single]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
    by_cases h : Even (s + t)
    · rw [sumDiffHom_apply, ← add_smul, ← sub_smul]
      have h1 : (s + t) / 2 + (s - t) / 2 = s := by
        rw [Int.even_iff] at h
        omega
      have h2 : (s + t) / 2 - (s - t) / 2 = t := by
        rw [Int.even_iff] at h
        omega
      rw [h1, h2]
    · simp [villainCoef, h]
  -- the right side as the same kind of sum
  have hR : (∑ k ∈ Finset.range (N + 1), ∑ ε ∈ ({1, -1} : Finset ℝ),
        (villainC β₁ β₂ ^ k / (Nat.factorial k : ℝ) / 2) •
          tensor (villainSqVec d N k ε (villainA β₁ β₂)) (villainSqVec d N k ε (villainA β₁ β₂))) =
      ∑ s ∈ Finset.Icc (-(N : ℤ)) N, ∑ t ∈ Finset.Icc (-(N : ℤ)) N,
        (single (s • d, t • d) (∑ k ∈ Finset.range (N + 1), ∑ ε ∈ ({1, -1} : Finset ℝ),
          villainC β₁ β₂ ^ k / (Nat.factorial k : ℝ) / 2 *
            ((ε ^ s * (s : ℝ) ^ k * Real.exp (-villainA β₁ β₂ * (s : ℝ) ^ 2)) *
              (ε ^ t * (t : ℝ) ^ k * Real.exp (-villainA β₁ β₂ * (t : ℝ) ^ 2)))) :
          DupTrigAlgebra V) := by
    simp only [villainSqVec, tensor_sum_single, Finset.smul_sum, smul_single, smul_eq_mul,
      ← sum_single_eq]
    exact sum_comm4 _ _ _ _ _
  rw [hL, hR]
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
  congr 1
  have hterm : ∀ k ∈ Finset.range (N + 1), (∑ ε ∈ ({1, -1} : Finset ℝ),
      villainC β₁ β₂ ^ k / (Nat.factorial k : ℝ) / 2 *
        ((ε ^ s * (s : ℝ) ^ k * Real.exp (-villainA β₁ β₂ * (s : ℝ) ^ 2)) *
          (ε ^ t * (t : ℝ) ^ k * Real.exp (-villainA β₁ β₂ * (t : ℝ) ^ 2)))) =
      villainC β₁ β₂ ^ k / (Nat.factorial k : ℝ) / 2 * (s : ℝ) ^ k * (t : ℝ) ^ k *
        Real.exp (-villainA β₁ β₂ * (s : ℝ) ^ 2) * Real.exp (-villainA β₁ β₂ * (t : ℝ) ^ 2) *
          ∑ ε ∈ ({1, -1} : Finset ℝ), ε ^ s * ε ^ t := fun k _ => by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ε _ => ?_
    ring
  rw [Finset.sum_congr rfl hterm, villain_parity_sum, villainCoef]
  split_ifs
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_pow, mul_pow, show -villainA β₁ β₂ * ((s : ℝ) ^ 2 + (t : ℝ) ^ 2) =
      -villainA β₁ β₂ * (s : ℝ) ^ 2 + -villainA β₁ β₂ * (t : ℝ) ^ 2 by ring, Real.exp_add]
    ring
  · simp

omit [Fintype V] in
theorem isGinibre_villainApprox {β₁ β₂ : ℝ} (h₂ : 0 < β₂) (h₁₂ : β₂ ≤ β₁) (d : Frequency V)
    (N : ℕ) : IsGinibre (villainApprox β₁ β₂ d N) := by
  rw [IsGinibre, sumDiffMap_villainApprox]
  refine IsSquareSum.finsetSum _ fun k _ => IsSquareSum.finsetSum _ fun ε _ => ?_
  exact IsSquareSum.square _ (div_nonneg (div_nonneg (pow_nonneg (villainC_nonneg h₂ h₁₂) k)
    (by positivity)) (by norm_num)) _

/-- `(w_{β₁}, w_{β₂})` is a Ginibre pair of Villain weights for `0 < β₂ ≤ β₁`. -/
theorem isGinibrePair_villain {β₁ β₂ : ℝ} (h₂ : 0 < β₂) (h₁₂ : β₂ ≤ β₁) :
    IsGinibrePair V (villainWeight β₁) (villainWeight β₂) := fun d => by
  obtain ⟨C, hC⟩ := exists_norm_villainSeries_le h₂ h₁₂
  have h₁ : 0 < β₁ := h₂.trans_le h₁₂
  have hn : 0 ≤ villainNorm β₁ * villainNorm β₂ :=
    mul_nonneg (Real.rpow_nonneg (mul_nonneg (by positivity) h₁.le) _)
      (Real.rpow_nonneg (mul_nonneg (by positivity) h₂.le) _)
  refine ⟨fun N => (villainNorm β₁ * villainNorm β₂) • villainApprox β₁ β₂ d N,
    (villainNorm β₁ * villainNorm β₂) * C,
    fun N => (isGinibre_villainApprox h₂ h₁₂ d N).smul hn, fun N z => ?_, fun z => ?_⟩
  · rw [map_smul, Pi.smul_apply, dupEval_villainApprox, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg hn]
    exact mul_le_mul_of_nonneg_left (hC N _ _) hn
  · simp only [map_smul, Pi.smul_apply, dupEval_villainApprox, Complex.real_smul]
    exact tendsto_villainSeries h₂ h₁₂ _ _

/-- The one-copy Villain approximant. -/
def villainOneApprox (β : ℝ) (d : Frequency V) (N : ℕ) : DupTrigAlgebra V :=
  ∑ p ∈ Finset.Icc (-(N : ℤ)) N, single (p • d, 0) (Real.exp (-((p : ℝ) ^ 2) / (2 * β)))

theorem dupEval_villainOneApprox (β : ℝ) (d : Frequency V) (N : ℕ) (z : (V → ℝ) × (V → ℝ)) :
    dupEval V (villainOneApprox β d N) z = villainOneSeries β N (phase d z.1) := by
  simp only [villainOneApprox, villainOneSeries, map_sum, Finset.sum_apply, dupEval_single,
    character_zero, mul_one]
  simp only [character_eq_exp, phase_zsmul]

omit [Fintype V] in
theorem isGinibre_villainOneApprox (β : ℝ) (d : Frequency V) (N : ℕ) :
    IsGinibre (villainOneApprox β d N) := by
  rw [IsGinibre]
  simp only [villainOneApprox, map_sum, sumDiffMap, mapDomainRingHom_apply, mapDomain_single,
    sumDiffHom_apply, add_zero, sub_zero]
  refine IsSquareSum.finsetSum _ fun p _ => ?_
  have h := IsSquareSum.square (Real.exp (-((p : ℝ) ^ 2) / (2 * β))) (Real.exp_pos _).le
    (single (p • d) 1 : TrigAlgebra V)
  rwa [tensor_single_single, smul_single, smul_eq_mul, mul_one, mul_one] at h

/-- `(w_β, 1)`: a Villain bond present in the first copy only is a Ginibre pair. -/
theorem isGinibrePair_villain_one {β : ℝ} (hβ : 0 < β) :
    IsGinibrePair V (villainWeight β) (fun _ => 1) := fun d => by
  obtain ⟨C, hC⟩ := exists_norm_villainOneSeries_le hβ
  have hn : 0 ≤ villainNorm β := Real.rpow_nonneg (mul_nonneg (by positivity) hβ.le) _
  refine ⟨fun N => villainNorm β • villainOneApprox β d N, villainNorm β * C,
    fun N => (isGinibre_villainOneApprox β d N).smul hn, fun N z => ?_, fun z => ?_⟩
  · rw [map_smul, Pi.smul_apply, dupEval_villainOneApprox, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg hn]
    exact mul_le_mul_of_nonneg_left (hC N _) hn
  · simp only [map_smul, Pi.smul_apply, dupEval_villainOneApprox, Complex.real_smul, mul_one]
    exact tendsto_villainOneSeries hβ _

end FroehlichSpencer.BKT.Ginibre

end
