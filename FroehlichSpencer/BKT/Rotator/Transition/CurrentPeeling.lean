/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Rotator.XYDualityFourier
public import FroehlichSpencer.BKT.Rotator.Transition.BesselRatio
public import FroehlichSpencer.BKT.Rotator.Transition.BoxGeometry

/-!
# High-temperature decay on the free spin box by current peeling

In the integer-current expansion of the free-box plane rotator , the two-point function
`⟨cos(θ_a − θ_x)⟩` is the ratio `S(δ_a − δ_x) / S(0)` of the sums `S(χ)` of the nonnegative current
weights `∏_e I_{q_e}(b)` over currents of divergence `χ`. A current of divergence `δ_a − δ_x`,
`a ≠ x`, has positive outflow through some bond at `a`; removing one unit of current from that bond
moves the source to the neighbouring site and lowers one weight factor `I_n` to `I_{n−1}`, at a
cost `≤ b/2`. Since `a` has at most four bonds, `S(δ_a − δ_x) ≤ 2b · max_{a' ∼ a} S(δ_{a'} − δ_x)`,
and induction on the distance gives `⟨cos(θ_a − θ_x)⟩ ≤ (2b)^{|a − x|₁}` for every `b ≥ 0`.
-/

@[expose] public section

open MeasureTheory
open FroehlichSpencer.BKT FroehlichSpencer.BKT.Villain FroehlichSpencer.BKT.Rotator.Ginibre
open scoped Real

noncomputable section

namespace FroehlichSpencer.BKT.Rotator.Transition

variable {L : ℕ}

/-- The sum of the real current weights `∏_e I_{q_e}(b)` over the currents of divergence `χ`. -/
def currentSum (L : ℕ) (b : ℝ) (χ : RotatorSpinSite L → ℤ) : ℝ :=
  ∑' q : RotatorInternalBond L → ℤ,
    if ∀ v, rotatorCurrentDivergence q v = χ v then rotatorCurrentWeight (rotatorIReal b) q else 0

theorem rotatorCurrentWeight_nonneg {b : ℝ} (hb : 0 ≤ b) (q : RotatorInternalBond L → ℤ) :
    0 ≤ rotatorCurrentWeight (rotatorIReal b) q :=
  Finset.prod_nonneg fun e _ => rotatorIReal_nonneg hb (q e)

theorem summable_abs_rotatorCurrentWeight (b : ℝ) :
    Summable fun q : RotatorInternalBond L → ℤ => |rotatorCurrentWeight (rotatorIReal b) q| :=
  rotatorCurrentWeight_summable b (summable_rotatorI b)

theorem summable_currentTerm (b : ℝ) (χ : RotatorSpinSite L → ℤ) :
    Summable fun q : RotatorInternalBond L → ℤ =>
      if ∀ v, rotatorCurrentDivergence q v = χ v then rotatorCurrentWeight (rotatorIReal b) q
      else 0 := by
  refine Summable.of_norm_bounded (summable_abs_rotatorCurrentWeight b) fun q => ?_
  split_ifs
  · rw [Real.norm_eq_abs]
  · simp

theorem currentSum_nonneg {b : ℝ} (hb : 0 ≤ b) (χ : RotatorSpinSite L → ℤ) :
    0 ≤ currentSum L b χ :=
  tsum_nonneg fun q => by
    split_ifs
    exacts [rotatorCurrentWeight_nonneg hb q, le_rfl]

/-- The raw marked integral is `(2π)^{|V|}` times the current sum with the marked divergence. -/
theorem integral_density_mul_character (b : ℝ) (a x : RotatorSpinSite L) (ξ : ℤ) :
    ∫ θ : RotatorAngleConfiguration L,
        (rotatorSpinDensity L b θ : ℂ) * rotatorSpinCharacter L a x ξ θ
          ∂rotatorRawAngleMeasure (RotatorSpinSite L) =
      (2 * π : ℂ) ^ Fintype.card (RotatorSpinSite L) *
        (currentSum L b (rotatorTwoPointFrequency a x ξ) : ℂ) := by
  simp_rw [rotatorSpinDensity_mulCharacter_currentSeries_unconditional b a x ξ]
  rw [rotatorCurrentSeries_integral (rotatorFreeGraph L) (rotatorIReal b)
    (rotatorTwoPointFrequency a x ξ) (summable_abs_rotatorCurrentWeight b), mul_comm]
  congr 1
  rw [currentSum, Complex.ofReal_tsum]
  refine tsum_congr fun q => ?_
  have hiff : ((fun v => -currentDivergence (rotatorFreeGraph L) q v +
      rotatorTwoPointFrequency a x ξ v) = 0) ↔
      ∀ v, rotatorCurrentDivergence q v = rotatorTwoPointFrequency a x ξ v := by
    rw [funext_iff]
    refine forall_congr' fun v => ?_
    simp only [Pi.zero_apply, rotatorCurrentDivergence]
    omega
  by_cases h : ∀ v, rotatorCurrentDivergence q v = rotatorTwoPointFrequency a x ξ v
  · rw [ite_eq_left (hiff.mpr h), ite_eq_left h]
  · rw [ite_eq_right (fun h' => h (hiff.mp h')), ite_eq_right h, Complex.ofReal_zero]

theorem rotatorTwoPointFrequency_zero (a x : RotatorSpinSite L) :
    rotatorTwoPointFrequency a x 0 = fun _ => 0 := by
  funext v
  simp [rotatorTwoPointFrequency]

theorem rotatorTwoPointFrequency_self (a : RotatorSpinSite L) :
    rotatorTwoPointFrequency a a 1 = fun _ => 0 := by
  funext v
  simp only [rotatorTwoPointFrequency]
  split_ifs <;> simp

/-- The partition integral is `(2π)^{|V|}` times the neutral current sum. -/
theorem rotatorPartitionIntegralInternal_eq_currentSum (b : ℝ) :
    rotatorPartitionIntegralInternal L b =
      (2 * π) ^ Fintype.card (RotatorSpinSite L) * currentSum L b (fun _ => 0) := by
  have h := integral_density_mul_character (L := L) b (0, 0) (0, 0) 0
  rw [rotatorTwoPointFrequency_zero] at h
  have hchar : ∀ θ : RotatorAngleConfiguration L, rotatorSpinCharacter L (0, 0) (0, 0) 0 θ = 1 :=
    fun θ => by simp [rotatorSpinCharacter]
  simp_rw [hchar, mul_one, integral_complex_ofReal] at h
  exact_mod_cast h

theorem currentSum_zero_pos (b : ℝ) : 0 < currentSum L b (fun _ => 0) := by
  have h := rotatorPartitionIntegralInternal_pos L b
  rw [rotatorPartitionIntegralInternal_eq_currentSum] at h
  exact pos_of_mul_pos_right h (by positivity)

/-- The two-point function of the internal law is the ratio of current sums. -/
theorem integral_cos_rotatorMeasureInternal_eq_currentSum (b : ℝ) (a x : RotatorSpinSite L)
    (ξ : ℤ) :
    ∫ θ, Real.cos (ξ * (θ a - θ x)) ∂rotatorMeasureInternal L b =
      currentSum L b (rotatorTwoPointFrequency a x ξ) / currentSum L b (fun _ => 0) := by
  have h := integral_rotatorSpinCharacter L b a x ξ
  rw [rotatorMeasureInternal_character_integral] at h
  have hZ := rotatorPartitionIntegralInternal_pos L b
  have hsplit : ∀ θ : RotatorAngleConfiguration L,
      ((rotatorSpinDensity L b θ / rotatorPartitionIntegralInternal L b : ℝ) : ℂ) *
        rotatorSpinCharacter L a x ξ θ =
      ((rotatorPartitionIntegralInternal L b : ℝ) : ℂ)⁻¹ *
        ((rotatorSpinDensity L b θ : ℂ) * rotatorSpinCharacter L a x ξ θ) := fun θ => by
    push_cast
    ring
  simp_rw [hsplit] at h
  rw [integral_const_mul, integral_density_mul_character,
    rotatorPartitionIntegralInternal_eq_currentSum] at h
  have hS := currentSum_zero_pos (L := L) b
  apply Complex.ofReal_injective
  rw [← h]
  push_cast
  field_simp

/-! ### Peeling one unit of current -/

private theorem currentDivergence_single_aux (e : RotatorInternalBond L) (v : RotatorSpinSite L) :
    rotatorCurrentDivergence (Pi.single e 1) v =
      (if (rotatorFreeGraph L).src e = v then 1 else 0) -
        (if (rotatorFreeGraph L).tgt e = v then 1 else 0) := by
  classical
  simp only [rotatorCurrentDivergence, currentDivergence]
  congr 1
  · rw [Finset.sum_eq_single e (fun e' _ he' => by simp [he'])
      (fun h => absurd (Finset.mem_univ e) h)]
    simp
  · rw [Finset.sum_eq_single e (fun e' _ he' => by simp [he'])
      (fun h => absurd (Finset.mem_univ e) h)]
    simp

theorem currentDivergence_single (e : RotatorInternalBond L) (v : RotatorSpinSite L) :
    rotatorCurrentDivergence (Pi.single e 1) v =
      (if v = (rotatorFreeGraph L).src e then 1 else 0) -
        (if v = (rotatorFreeGraph L).tgt e then 1 else 0) := by
  rw [currentDivergence_single_aux]
  congr 1 <;> exact ite_congr (propext eq_comm) (fun _ => rfl) (fun _ => rfl)

theorem rotatorCurrentWeight_update (b : ℝ) (q : RotatorInternalBond L → ℤ)
    (e : RotatorInternalBond L) (m : ℤ) :
    rotatorCurrentWeight (rotatorIReal b) (Function.update q e m) =
      rotatorIReal b m * ∏ e' ∈ Finset.univ.erase e, rotatorIReal b (q e') := by
  classical
  rw [rotatorCurrentWeight, ← Finset.mul_prod_erase _ _ (Finset.mem_univ e),
    Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun e' he' => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase he')]

/-- Lowering a positive bond current by one costs at most `b/2`. -/
theorem rotatorCurrentWeight_le_sub_single {b : ℝ} (hb : 0 ≤ b) (q : RotatorInternalBond L → ℤ)
    (e : RotatorInternalBond L) (hq : 1 ≤ q e) :
    rotatorCurrentWeight (rotatorIReal b) q ≤
      b / 2 * rotatorCurrentWeight (rotatorIReal b) (q - Pi.single e 1) := by
  classical
  have h₁ : q = Function.update q e (q e) := (Function.update_eq_self e q).symm
  have h₂ : q - Pi.single e 1 = Function.update q e (q e - 1) := by
    funext e'
    by_cases he : e' = e
    · subst he
      simp
    · simp [he]
  rw [h₂, rotatorCurrentWeight_update]
  conv_lhs => rw [h₁, rotatorCurrentWeight_update]
  have hR : 0 ≤ ∏ e' ∈ Finset.univ.erase e, rotatorIReal b (q e') :=
    Finset.prod_nonneg fun e' _ => rotatorIReal_nonneg hb _
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right (rotatorIReal_le_of_pos hb hq) hR

/-- Raising a negative bond current by one costs at most `b/2`. -/
theorem rotatorCurrentWeight_le_add_single {b : ℝ} (hb : 0 ≤ b) (q : RotatorInternalBond L → ℤ)
    (e : RotatorInternalBond L) (hq : q e ≤ -1) :
    rotatorCurrentWeight (rotatorIReal b) q ≤
      b / 2 * rotatorCurrentWeight (rotatorIReal b) (q + Pi.single e 1) := by
  classical
  have h₁ : q = Function.update q e (q e) := (Function.update_eq_self e q).symm
  have h₂ : q + Pi.single e 1 = Function.update q e (q e + 1) := by
    funext e'
    by_cases he : e' = e
    · subst he
      simp
    · simp [he]
  rw [h₂, rotatorCurrentWeight_update]
  conv_lhs => rw [h₁, rotatorCurrentWeight_update]
  have hR : 0 ≤ ∏ e' ∈ Finset.univ.erase e, rotatorIReal b (q e') :=
    Finset.prod_nonneg fun e' _ => rotatorIReal_nonneg hb _
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right (rotatorIReal_le_of_neg hb hq) hR

/-- The current sum is invariant under translating all currents by a fixed current. -/
theorem tsum_comp_add (f : (RotatorInternalBond L → ℤ) → ℝ) (c : RotatorInternalBond L → ℤ) :
    ∑' q, f (q + c) = ∑' q, f q :=
  (Equiv.addRight c).tsum_eq f

/-- The current-sum summand of divergence `χ`. -/
def currentTerm (b : ℝ) (χ : RotatorSpinSite L → ℤ) (q : RotatorInternalBond L → ℤ) : ℝ :=
  if ∀ v, rotatorCurrentDivergence q v = χ v then rotatorCurrentWeight (rotatorIReal b) q else 0

theorem currentTerm_nonneg {b : ℝ} (hb : 0 ≤ b) (χ : RotatorSpinSite L → ℤ)
    (q : RotatorInternalBond L → ℤ) : 0 ≤ currentTerm b χ q := by
  unfold currentTerm
  split_ifs
  exacts [rotatorCurrentWeight_nonneg hb q, le_rfl]

theorem currentSum_eq_tsum_currentTerm (b : ℝ) (χ : RotatorSpinSite L → ℤ) :
    currentSum L b χ = ∑' q, currentTerm b χ q := rfl

/-- Peeling along a bond leaving `a`: the source moves to the target of the bond. -/
theorem tsum_peel_src_le {b : ℝ} (hb : 0 ≤ b) {a x : RotatorSpinSite L} (e : RotatorInternalBond L)
    (he : (rotatorFreeGraph L).src e = a) :
    ∑' q, (if (∀ v, rotatorCurrentDivergence q v = rotatorTwoPointFrequency a x 1 v) ∧ 1 ≤ q e
        then b / 2 * rotatorCurrentWeight (rotatorIReal b) (q - Pi.single e 1) else 0) ≤
      b / 2 * currentSum L b (rotatorTwoPointFrequency ((rotatorFreeGraph L).tgt e) x 1) := by
  classical
  set χ' := rotatorTwoPointFrequency ((rotatorFreeGraph L).tgt e) x 1
  have hpt : ∀ q : RotatorInternalBond L → ℤ,
      (if (∀ v, rotatorCurrentDivergence q v = rotatorTwoPointFrequency a x 1 v) ∧ 1 ≤ q e
        then b / 2 * rotatorCurrentWeight (rotatorIReal b) (q - Pi.single e 1) else 0) ≤
      b / 2 * currentTerm b χ' (q - Pi.single e 1) := fun q => by
    by_cases hq : (∀ v, rotatorCurrentDivergence q v = rotatorTwoPointFrequency a x 1 v) ∧ 1 ≤ q e
    · rw [ite_eq_left hq, currentTerm, ite_eq_left]
      intro v
      rw [rotatorCurrentDivergence, rotatorCurrentDivergence_sub, ← rotatorCurrentDivergence,
        hq.1 v, ← rotatorCurrentDivergence, currentDivergence_single, he]
      simp only [χ', rotatorTwoPointFrequency]
      split_ifs <;> omega
    · rw [ite_eq_right hq]
      exact mul_nonneg (by positivity) (currentTerm_nonneg hb _ _)
  have hsum : Summable fun q : RotatorInternalBond L → ℤ =>
      b / 2 * currentTerm b χ' (q - Pi.single e 1) :=
    ((Equiv.subRight (Pi.single e 1)).summable_iff.mpr (summable_currentTerm b χ')).mul_left _
  have hsum' : Summable fun q : RotatorInternalBond L → ℤ =>
      (if (∀ v, rotatorCurrentDivergence q v = rotatorTwoPointFrequency a x 1 v) ∧ 1 ≤ q e
        then b / 2 * rotatorCurrentWeight (rotatorIReal b) (q - Pi.single e 1) else 0) := by
    refine hsum.of_nonneg_of_le (fun q => ?_) hpt
    split_ifs
    exacts [mul_nonneg (by positivity) (rotatorCurrentWeight_nonneg hb _), le_rfl]
  calc _ ≤ ∑' q, b / 2 * currentTerm b χ' (q - Pi.single e 1) := hsum'.tsum_le_tsum hpt hsum
    _ = b / 2 * ∑' q, currentTerm b χ' (q - Pi.single e 1) := tsum_mul_left
    _ = b / 2 * currentSum L b χ' := by
      rw [currentSum_eq_tsum_currentTerm]
      congr 1
      exact (Equiv.subRight (Pi.single e 1)).tsum_eq (currentTerm b χ')

/-- Peeling along a bond entering `a`: the source moves to the source of the bond. -/
theorem tsum_peel_tgt_le {b : ℝ} (hb : 0 ≤ b) {a x : RotatorSpinSite L} (e : RotatorInternalBond L)
    (he : (rotatorFreeGraph L).tgt e = a) :
    ∑' q, (if (∀ v, rotatorCurrentDivergence q v = rotatorTwoPointFrequency a x 1 v) ∧ q e ≤ -1
        then b / 2 * rotatorCurrentWeight (rotatorIReal b) (q + Pi.single e 1) else 0) ≤
      b / 2 * currentSum L b (rotatorTwoPointFrequency ((rotatorFreeGraph L).src e) x 1) := by
  classical
  set χ' := rotatorTwoPointFrequency ((rotatorFreeGraph L).src e) x 1
  have hpt : ∀ q : RotatorInternalBond L → ℤ,
      (if (∀ v, rotatorCurrentDivergence q v = rotatorTwoPointFrequency a x 1 v) ∧ q e ≤ -1
        then b / 2 * rotatorCurrentWeight (rotatorIReal b) (q + Pi.single e 1) else 0) ≤
      b / 2 * currentTerm b χ' (q + Pi.single e 1) := fun q => by
    by_cases hq : (∀ v, rotatorCurrentDivergence q v = rotatorTwoPointFrequency a x 1 v) ∧
        q e ≤ -1
    · rw [ite_eq_left hq, currentTerm, ite_eq_left]
      intro v
      rw [rotatorCurrentDivergence, rotatorCurrentDivergence_add, ← rotatorCurrentDivergence,
        hq.1 v, ← rotatorCurrentDivergence, currentDivergence_single, he]
      simp only [χ', rotatorTwoPointFrequency]
      split_ifs <;> omega
    · rw [ite_eq_right hq]
      exact mul_nonneg (by positivity) (currentTerm_nonneg hb _ _)
  have hsum : Summable fun q : RotatorInternalBond L → ℤ =>
      b / 2 * currentTerm b χ' (q + Pi.single e 1) :=
    ((Equiv.addRight (Pi.single e 1)).summable_iff.mpr (summable_currentTerm b χ')).mul_left _
  have hsum' : Summable fun q : RotatorInternalBond L → ℤ =>
      (if (∀ v, rotatorCurrentDivergence q v = rotatorTwoPointFrequency a x 1 v) ∧ q e ≤ -1
        then b / 2 * rotatorCurrentWeight (rotatorIReal b) (q + Pi.single e 1) else 0) := by
    refine hsum.of_nonneg_of_le (fun q => ?_) hpt
    split_ifs
    exacts [mul_nonneg (by positivity) (rotatorCurrentWeight_nonneg hb _), le_rfl]
  calc _ ≤ ∑' q, b / 2 * currentTerm b χ' (q + Pi.single e 1) := hsum'.tsum_le_tsum hpt hsum
    _ = b / 2 * ∑' q, currentTerm b χ' (q + Pi.single e 1) := tsum_mul_left
    _ = b / 2 * currentSum L b χ' := by
      rw [currentSum_eq_tsum_currentTerm]
      congr 1
      exact (Equiv.addRight (Pi.single e 1)).tsum_eq (currentTerm b χ')

/-- **One peeling step.** If `a ≠ x`, the current sum of divergence `δ_a − δ_x` is at most `b/2`
times the sum, over the bonds at `a`, of the current sums with the source moved across the bond. -/
theorem currentSum_le_peel {b : ℝ} (hb : 0 ≤ b) {a x : RotatorSpinSite L} (hax : a ≠ x) :
    currentSum L b (rotatorTwoPointFrequency a x 1) ≤
      b / 2 * ((∑ e ∈ Finset.univ.filter fun e : RotatorInternalBond L =>
            (rotatorFreeGraph L).src e = a,
          currentSum L b (rotatorTwoPointFrequency ((rotatorFreeGraph L).tgt e) x 1)) +
        ∑ e ∈ Finset.univ.filter fun e : RotatorInternalBond L => (rotatorFreeGraph L).tgt e = a,
          currentSum L b (rotatorTwoPointFrequency ((rotatorFreeGraph L).src e) x 1)) := by
  classical
  set χ := rotatorTwoPointFrequency a x 1 with hχ
  set Fs := Finset.univ.filter fun e : RotatorInternalBond L => (rotatorFreeGraph L).src e = a
  set Ft := Finset.univ.filter fun e : RotatorInternalBond L => (rotatorFreeGraph L).tgt e = a
  let gs : RotatorInternalBond L → (RotatorInternalBond L → ℤ) → ℝ := fun e q =>
    if (∀ v, rotatorCurrentDivergence q v = χ v) ∧ 1 ≤ q e then
      b / 2 * rotatorCurrentWeight (rotatorIReal b) (q - Pi.single e 1) else 0
  let gt : RotatorInternalBond L → (RotatorInternalBond L → ℤ) → ℝ := fun e q =>
    if (∀ v, rotatorCurrentDivergence q v = χ v) ∧ q e ≤ -1 then
      b / 2 * rotatorCurrentWeight (rotatorIReal b) (q + Pi.single e 1) else 0
  have hgs0 : ∀ e q, 0 ≤ gs e q := fun e q => by
    simp only [gs]
    split_ifs
    exacts [mul_nonneg (by positivity) (rotatorCurrentWeight_nonneg hb _), le_rfl]
  have hgt0 : ∀ e q, 0 ≤ gt e q := fun e q => by
    simp only [gt]
    split_ifs
    exacts [mul_nonneg (by positivity) (rotatorCurrentWeight_nonneg hb _), le_rfl]
  have hχa : χ a = 1 := by
    simp [hχ, rotatorTwoPointFrequency, hax]
  -- the pointwise peeling bound
  have hpoint : ∀ q, currentTerm b χ q ≤ (∑ e ∈ Fs, gs e q) + ∑ e ∈ Ft, gt e q := fun q => by
    by_cases hq : ∀ v, rotatorCurrentDivergence q v = χ v
    · rw [currentTerm, ite_eq_left hq]
      have hdiv := hq a
      rw [hχa] at hdiv
      simp only [rotatorCurrentDivergence, currentDivergence] at hdiv
      by_contra hcon
      push Not at hcon
      have hs : ∀ e ∈ Fs, q e ≤ 0 := fun e he => by
        by_contra hpos
        push Not at hpos
        have h1 : rotatorCurrentWeight (rotatorIReal b) q ≤ gs e q := by
          simp only [gs, ite_eq_left (show _ ∧ 1 ≤ q e from ⟨hq, hpos⟩)]
          exact rotatorCurrentWeight_le_sub_single hb q e hpos
        have := Finset.single_le_sum (fun e _ => hgs0 e q) he
        have := Finset.sum_nonneg fun e (_ : e ∈ Ft) => hgt0 e q
        linarith
      have ht : ∀ e ∈ Ft, 0 ≤ q e := fun e he => by
        by_contra hneg
        push Not at hneg
        have h1 : rotatorCurrentWeight (rotatorIReal b) q ≤ gt e q := by
          simp only [gt, ite_eq_left (show _ ∧ q e ≤ -1 from ⟨hq, by omega⟩)]
          exact rotatorCurrentWeight_le_add_single hb q e (by omega)
        have := Finset.single_le_sum (fun e _ => hgt0 e q) he
        have := Finset.sum_nonneg fun e (_ : e ∈ Fs) => hgs0 e q
        linarith
      have h1 : (∑ e, if (rotatorFreeGraph L).src e = a then q e else 0) ≤ 0 := by
        rw [← Finset.sum_filter]
        exact Finset.sum_nonpos hs
      have h2 : 0 ≤ ∑ e, if (rotatorFreeGraph L).tgt e = a then q e else 0 := by
        rw [← Finset.sum_filter]
        exact Finset.sum_nonneg ht
      omega
    · rw [currentTerm, ite_eq_right hq]
      exact add_nonneg (Finset.sum_nonneg fun e _ => hgs0 e q)
        (Finset.sum_nonneg fun e _ => hgt0 e q)
  -- summability
  have hgs_sum : ∀ e, Summable (gs e) := fun e => by
    have h : Summable fun q : RotatorInternalBond L → ℤ =>
        b / 2 * |rotatorCurrentWeight (rotatorIReal b) (q - Pi.single e 1)| :=
      ((Equiv.subRight (Pi.single e 1)).summable_iff.mpr
        (summable_abs_rotatorCurrentWeight (L := L) b)).mul_left _
    refine h.of_nonneg_of_le (hgs0 e) fun q => ?_
    simp only [gs]
    split_ifs
    · exact mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)
    · exact mul_nonneg (by positivity) (abs_nonneg _)
  have hgt_sum : ∀ e, Summable (gt e) := fun e => by
    have h : Summable fun q : RotatorInternalBond L → ℤ =>
        b / 2 * |rotatorCurrentWeight (rotatorIReal b) (q + Pi.single e 1)| :=
      ((Equiv.addRight (Pi.single e 1)).summable_iff.mpr
        (summable_abs_rotatorCurrentWeight (L := L) b)).mul_left _
    refine h.of_nonneg_of_le (hgt0 e) fun q => ?_
    simp only [gt]
    split_ifs
    · exact mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)
    · exact mul_nonneg (by positivity) (abs_nonneg _)
  have hs_sum : Summable fun q => ∑ e ∈ Fs, gs e q := summable_sum fun e _ => hgs_sum e
  have ht_sum : Summable fun q => ∑ e ∈ Ft, gt e q := summable_sum fun e _ => hgt_sum e
  calc currentSum L b χ = ∑' q, currentTerm b χ q := rfl
    _ ≤ ∑' q, ((∑ e ∈ Fs, gs e q) + ∑ e ∈ Ft, gt e q) :=
        (summable_currentTerm b χ).tsum_le_tsum hpoint (hs_sum.add ht_sum)
    _ = (∑ e ∈ Fs, ∑' q, gs e q) + ∑ e ∈ Ft, ∑' q, gt e q := by
        rw [hs_sum.tsum_add ht_sum, Summable.tsum_finsetSum fun e _ => hgs_sum e,
          Summable.tsum_finsetSum fun e _ => hgt_sum e]
    _ ≤ (∑ e ∈ Fs, b / 2 * currentSum L b
            (rotatorTwoPointFrequency ((rotatorFreeGraph L).tgt e) x 1)) +
          ∑ e ∈ Ft, b / 2 * currentSum L b
            (rotatorTwoPointFrequency ((rotatorFreeGraph L).src e) x 1) := by
        gcongr with e he e he
        · exact tsum_peel_src_le hb e (Finset.mem_filter.mp he).2
        · exact tsum_peel_tgt_le hb e (Finset.mem_filter.mp he).2
    _ = _ := by rw [← Finset.mul_sum, ← Finset.mul_sum, mul_add]

/-- **High-temperature decay of the current sums.** -/
theorem currentSum_le_pow {b : ℝ} (hb : 0 ≤ b) (x : RotatorSpinSite L) :
    ∀ k : ℕ, ∀ a : RotatorSpinSite L, k ≤ boxDist a x →
      currentSum L b (rotatorTwoPointFrequency a x 1) ≤
        (2 * b) ^ k * currentSum L b (fun _ => 0) := by
  intro k
  induction k with
  | zero =>
      intro a _
      rw [pow_zero, one_mul]
      have h := integral_cos_rotatorMeasureInternal_eq_currentSum (L := L) b a x 1
      have hle : ∫ θ, Real.cos ((1 : ℤ) * (θ a - θ x)) ∂rotatorMeasureInternal L b ≤ 1 := by
        rw [rotatorMeasureInternal_eq_cosineGibbs]
        have := integral_cos_cosineGibbs_le_one (multigraphFrequency (rotatorFreeGraph L))
          (fun _ => b) (rotatorTwoPointFrequency a x 1)
        simpa only [phase_rotatorTwoPointFrequency] using this
      rw [h, div_le_one (currentSum_zero_pos b)] at hle
      exact hle
  | succ k ih =>
      intro a ha
      have hax : a ≠ x := fun h => by
        subst h
        rw [boxDist_self] at ha
        omega
      refine (currentSum_le_peel hb hax).trans ?_
      have hs : ∀ e ∈ Finset.univ.filter fun e : RotatorInternalBond L =>
          (rotatorFreeGraph L).src e = a,
          currentSum L b (rotatorTwoPointFrequency ((rotatorFreeGraph L).tgt e) x 1) ≤
            (2 * b) ^ k * currentSum L b (fun _ => 0) := fun e he => by
        refine ih _ ?_
        have := boxDist_src_le e x
        rw [(Finset.mem_filter.mp he).2] at this
        omega
      have ht : ∀ e ∈ Finset.univ.filter fun e : RotatorInternalBond L =>
          (rotatorFreeGraph L).tgt e = a,
          currentSum L b (rotatorTwoPointFrequency ((rotatorFreeGraph L).src e) x 1) ≤
            (2 * b) ^ k * currentSum L b (fun _ => 0) := fun e he => by
        refine ih _ ?_
        have := boxDist_tgt_le e x
        rw [(Finset.mem_filter.mp he).2] at this
        omega
      have hS0 := (currentSum_zero_pos (L := L) b).le
      have hpow : 0 ≤ (2 * b) ^ k * currentSum L b (fun _ => 0) := by positivity
      calc b / 2 * ((∑ e ∈ Finset.univ.filter fun e : RotatorInternalBond L =>
              (rotatorFreeGraph L).src e = a,
            currentSum L b (rotatorTwoPointFrequency ((rotatorFreeGraph L).tgt e) x 1)) +
          ∑ e ∈ Finset.univ.filter fun e : RotatorInternalBond L => (rotatorFreeGraph L).tgt e = a,
            currentSum L b (rotatorTwoPointFrequency ((rotatorFreeGraph L).src e) x 1))
          ≤ b / 2 * ((2 * ((2 * b) ^ k * currentSum L b (fun _ => 0))) +
              2 * ((2 * b) ^ k * currentSum L b (fun _ => 0))) := by
            gcongr
            · exact (Finset.sum_le_card_nsmul _ _ _ hs).trans (by
                rw [nsmul_eq_mul]
                exact mul_le_mul_of_nonneg_right (by exact_mod_cast card_filter_src_eq_le a) hpow)
            · exact (Finset.sum_le_card_nsmul _ _ _ ht).trans (by
                rw [nsmul_eq_mul]
                exact mul_le_mul_of_nonneg_right (by exact_mod_cast card_filter_tgt_eq_le a) hpow)
        _ = (2 * b) ^ (k + 1) * currentSum L b (fun _ => 0) := by ring

/-- **High-temperature decay on the free box.** For `b ≥ 0`,
`⟨cos(θ_a − θ_x)⟩ ≤ (2b)^{|a − x|₁}` under the internal free-box law. -/
theorem integral_cos_rotatorMeasureInternal_le_pow {b : ℝ} (hb : 0 ≤ b)
    (a x : RotatorSpinSite L) :
    ∫ θ, Real.cos ((1 : ℤ) * (θ a - θ x)) ∂rotatorMeasureInternal L b ≤ (2 * b) ^ boxDist a x := by
  rw [integral_cos_rotatorMeasureInternal_eq_currentSum, div_le_iff₀ (currentSum_zero_pos b)]
  exact currentSum_le_pow hb x _ a le_rfl

end FroehlichSpencer.BKT.Rotator.Transition

end
