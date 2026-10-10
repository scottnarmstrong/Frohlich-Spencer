/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Currents.CurrentComponents
public import FroehlichSpencer.FS82.Moment.Packing
public import Mathlib.Algebra.Order.Chebyshev

/-!
# Jensen error for disconnected currents

This module turns one disconnected current's Jensen error into a sum of
connected-component majorants. Each component keeps its own support length,
energy and local field maximum, so the resulting terms can enter the existing
length-and-plaquette packing buckets.
-/

public section

open scoped BigOperators

namespace FroehlichSpencer.FS82.Currents

open FroehlichSpencer.FS82.Moment.Packing
open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Gaussian
noncomputable section
open Classical

theorem component_count_le_exp_remaining_weight {ι : Type*}
    (S : Finset ι) (t : ι → ℝ) (a total : ℝ) (i : ι)
    (hi : i ∈ S) (ha : 1 ≤ a)
    (htotal : total = ∑ k ∈ S, t k)
    (htwo : ∀ k ∈ S, 2 ≤ t k) :
    (S.card : ℝ) ≤ Real.exp (a * (total - t i)) := by
  have hsplit : total = t i + ∑ k ∈ S.erase i, t k := by
    rw [htotal, Finset.add_sum_erase S t hi]
  have hdelta : total - t i = ∑ k ∈ S.erase i, t k := by
    rw [hsplit]
    ring
  have hcardErase : (S.erase i).card + 1 = S.card := by
    rw [Finset.card_erase_of_mem hi]
    exact Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr
      (Finset.card_ne_zero.mpr ⟨i, hi⟩))
  have hcardEraseR : ((S.erase i).card : ℝ) + 1 = (S.card : ℝ) := by
    exact_mod_cast hcardErase
  have hconst : ∑ k ∈ S.erase i, (2 : ℝ) =
      2 * ((S.erase i).card : ℝ) := by
    simp
    ring
  have hother : 2 * ((S.card : ℝ) - 1) ≤
      ∑ k ∈ S.erase i, t k := by
    calc
      2 * ((S.card : ℝ) - 1) =
          2 * ((S.erase i).card : ℝ) := by rw [← hcardEraseR]; ring
      _ = ∑ k ∈ S.erase i, (2 : ℝ) := hconst.symm
      _ ≤ ∑ k ∈ S.erase i, t k := by
        apply Finset.sum_le_sum
        intro k hk
        exact htwo k (Finset.mem_of_mem_erase hk)
  have hdeltaNonneg : 0 ≤ total - t i := by
    rw [hdelta]
    exact Finset.sum_nonneg fun k hk => le_trans (by norm_num)
      (htwo k (Finset.mem_of_mem_erase hk))
  by_cases hcardOne : S.card = 1
  · have hcard : (S.card : ℝ) = 1 := by exact_mod_cast hcardOne
    have harg : 0 ≤ a * (total - t i) := mul_nonneg (by linarith) hdeltaNonneg
    have hexp : 1 ≤ Real.exp (a * (total - t i)) := by
      have h := Real.add_one_le_exp (a * (total - t i))
      linarith
    rw [hcard]
    exact hexp
  · have hcardPos : 0 < S.card := Finset.card_pos.mpr ⟨i, hi⟩
    have hcardTwoNat : 2 ≤ S.card := by omega
    have hcardTwo : 2 ≤ (S.card : ℝ) := by exact_mod_cast hcardTwoNat
    have hcardLower : (S.card : ℝ) ≤ 2 * ((S.card : ℝ) - 1) := by
      nlinarith
    have hdeltaLower : 2 * ((S.card : ℝ) - 1) ≤ total - t i := by
      rw [hdelta]
      exact hother
    have hscale : total - t i ≤ a * (total - t i) := by
      have h := mul_le_mul_of_nonneg_right ha hdeltaNonneg
      simpa using h
    have harg : (S.card : ℝ) ≤ a * (total - t i) :=
      le_trans (le_trans hcardLower hdeltaLower) hscale
    have hcardExp : (S.card : ℝ) ≤ Real.exp (S.card : ℝ) := by
      have h := Real.add_one_le_exp (S.card : ℝ)
      linarith
    exact hcardExp.trans (Real.exp_le_exp.mpr harg)

theorem component_count_exp_factor_le {ι : Type*}
    (S : Finset ι) (t : ι → ℝ) (a total : ℝ) (i : ι)
    (hi : i ∈ S) (ha : 1 ≤ a)
    (htotal : total = ∑ k ∈ S, t k)
    (htwo : ∀ k ∈ S, 2 ≤ t k) :
    (S.card : ℝ) * Real.exp (-(a * total)) ≤
      Real.exp (-(a * t i)) := by
  have hcard := component_count_le_exp_remaining_weight S t a total i hi ha
    htotal htwo
  calc
    (S.card : ℝ) * Real.exp (-(a * total)) ≤
        Real.exp (a * (total - t i)) * Real.exp (-(a * total)) :=
      mul_le_mul_of_nonneg_right hcard (Real.exp_pos _).le
    _ = Real.exp (-(a * t i)) := by
      rw [← Real.exp_add]
      congr 1
      ring

theorem disconnected_jensen_error_le_component_exponentials {ι : Type*}
    (S : Finset ι) (a total theta gamma z : ℝ)
    (t phase : ι → ℝ)
    (htotal : total = ∑ i ∈ S, t i)
    (htheta : theta = ∑ i ∈ S, phase i)
    (ha : 1 ≤ a)
    (htwo : ∀ i ∈ S, 2 ≤ t i)
    (hgamma : gamma ≤ 5 * z)
    (hz : z ≤ Real.exp (-(a * total))) :
    gamma * theta^2 ≤
      5 * ∑ i ∈ S, Real.exp (-(a * t i)) * phase i^2 := by
  classical
  by_cases hS : S.Nonempty
  · have hCS : (∑ i ∈ S, phase i)^2 ≤
        (S.card : ℝ) * ∑ i ∈ S, phase i^2 :=
      sq_sum_le_card_mul_sum_sq
    have hfactor : ∀ i ∈ S,
        (S.card : ℝ) * Real.exp (-(a * total)) ≤
          Real.exp (-(a * t i)) := by
      intro i hi
      exact component_count_exp_factor_le S t a total i hi ha htotal htwo
    calc
      gamma * theta^2 ≤ 5 * z * theta^2 :=
        mul_le_mul_of_nonneg_right hgamma (sq_nonneg theta)
      _ ≤ 5 * Real.exp (-(a * total)) * theta^2 := by
        have hmul := mul_le_mul_of_nonneg_left hz
          (by positivity : 0 ≤ (5 : ℝ) * theta^2)
        nlinarith
      _ = 5 * Real.exp (-(a * total)) *
            (∑ i ∈ S, phase i)^2 := by rw [htheta]
      _ ≤ 5 * Real.exp (-(a * total)) * (S.card : ℝ) *
            ∑ i ∈ S, phase i^2 :=
          by
            simpa [mul_assoc] using
              mul_le_mul_of_nonneg_left hCS (by positivity)
      _ = ∑ i ∈ S,
            (5 * Real.exp (-(a * total)) * (S.card : ℝ)) * phase i^2 := by
          simp_rw [Finset.mul_sum]
      _ ≤ ∑ i ∈ S,
            (5 * Real.exp (-(a * t i))) * phase i^2 := by
          apply Finset.sum_le_sum
          intro i hi
          apply mul_le_mul_of_nonneg_right _ (sq_nonneg (phase i))
          have hf := hfactor i hi
          calc
            5 * Real.exp (-(a * total)) * (S.card : ℝ) =
                5 * ((S.card : ℝ) * Real.exp (-(a * total))) := by ring
            _ ≤ 5 * Real.exp (-(a * t i)) :=
              mul_le_mul_of_nonneg_left hf (by norm_num)
      _ = 5 * ∑ i ∈ S, Real.exp (-(a * t i)) * phase i^2 := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          ring
  · have hEmpty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    have hthetaZero : theta = 0 := by simpa [hEmpty] using htheta
    simp [hEmpty, hthetaZero]

theorem disconnected_jensen_error_le_connected_majorants {ι : Type*}
    (S : Finset ι) (a C total theta gamma z : ℝ)
    (x length phase localMax : ι → ℝ)
    (htotal : total = ∑ i ∈ S, (x i + length i))
    (htheta : theta = ∑ i ∈ S, phase i)
    (ha : 1 ≤ a) (hC : 0 ≤ C)
    (hx : ∀ i ∈ S, 0 ≤ x i)
    (hMax : ∀ i ∈ S, 0 ≤ localMax i)
    (hsmallComponent : ∀ i ∈ S, 2 ≤ x i + length i)
    (hgamma : gamma ≤ 5 * z)
    (hz : z ≤ Real.exp (-(a * total)))
    (hphase : ∀ i ∈ S,
      |phase i| ≤ C * localMax i * x i * length i^4) :
    gamma * theta^2 ≤
      ∑ i ∈ S,
        (20 * C^2 / a^2) * length i^8 *
          Real.exp (-(a * length i)) * localMax i^2 := by
  have hfirst := disconnected_jensen_error_le_component_exponentials
    S a total theta gamma z (fun i => x i + length i) phase htotal htheta
    ha hsmallComponent hgamma hz
  calc
    gamma * theta^2 ≤
        5 * ∑ i ∈ S, Real.exp (-(a * (x i + length i))) * phase i^2 := hfirst
    _ = ∑ i ∈ S,
          5 * Real.exp (-(a * (x i + length i))) * phase i^2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
    _ ≤ ∑ i ∈ S,
          (20 * C^2 / a^2) * length i^8 *
            Real.exp (-(a * length i)) * localMax i^2 := by
        apply Finset.sum_le_sum
        intro i hi
        have hconnected := per_current_activity_error
          a C (x i) (length i) (localMax i)
          (Real.exp (-(a * (x i + length i))))
          (5 * Real.exp (-(a * (x i + length i)))) (phase i)
          (by positivity) hC (hx i hi) (hMax i hi) (by rfl) (by rfl)
          (hphase i hi)
        simpa [mul_assoc] using hconnected

/-- Apply the disconnected-current estimate to a phase that is additive over
the support components. The output is exactly the sum needed to assign each
component independently to its own plaquette and length packing bucket. -/
theorem currentComponents_jensen_error_le_componentMajorants {B : Box 4}
    (j : IntegerCurrent B) (a C z gamma theta : ℝ)
    (componentPhase componentMax : CurrentComponentClass j → ℝ)
    (ha : 1 ≤ a) (hC : 0 ≤ C)
    (hMax : ∀ c ∈ currentComponents j, 0 ≤ componentMax c)
    (hThetaAdd : theta =
      ∑ c ∈ currentComponents j, componentPhase c)
    (hgamma : gamma ≤ 5 * z)
    (hz : z ≤ Real.exp (-(a * (currentEnergy j + currentLength j))))
    (hphase : ∀ c ∈ currentComponents j,
      |componentPhase c| ≤ C * componentMax c *
        currentEnergy (currentComponentCurrent j c) *
          ((currentComponentSupport j c).card : ℝ)^4) :
    gamma * theta^2 ≤
      ∑ c ∈ currentComponents j,
        (20 * C^2 / a^2) *
          ((currentComponentSupport j c).card : ℝ)^8 *
            Real.exp (- (a * ((currentComponentSupport j c).card : ℝ))) *
              componentMax c^2 := by
  let x : CurrentComponentClass j → ℝ := fun c =>
    currentEnergy (currentComponentCurrent j c)
  let length : CurrentComponentClass j → ℝ := fun c =>
    ((currentComponentSupport j c).card : ℝ)
  have htotal : currentEnergy j + currentLength j =
      ∑ c ∈ currentComponents j, (x c + length c) := by
    dsimp [x, length]
    rw [currentEnergy_additive, currentLength_additive, Finset.sum_add_distrib]
  have hx : ∀ c ∈ currentComponents j, 0 ≤ x c := by
    intro c hc
    exact currentEnergy_nonneg (currentComponentCurrent j c)
  have hsmall : ∀ c ∈ currentComponents j, 2 ≤ x c + length c := by
    intro c hc
    have hcSupport := currentComponentSupport_nonempty j hc
    have hlenNat : 0 < (currentComponentSupport j c).card := Finset.card_pos.mpr hcSupport
    have hlen : 1 ≤ length c := by
      dsimp [length]
      exact_mod_cast (Nat.succ_le_iff.mpr hlenNat)
    have henergy := currentComponentEnergy_ge_length j c
    dsimp [x, length] at henergy ⊢
    linarith
  have hphase' : ∀ c ∈ currentComponents j,
      |componentPhase c| ≤ C * componentMax c * x c * length c^4 := by
    intro c hc
    simpa [x, length] using hphase c hc
  have h := disconnected_jensen_error_le_connected_majorants
    (currentComponents j) a C (currentEnergy j + currentLength j) theta gamma z
    x length componentPhase componentMax htotal hThetaAdd ha hC hx
    hMax hsmall hgamma hz hphase'
  simpa [length] using h

theorem currentPhase_jensen_error_le_componentMajorants {B : Box 4}
    (j : IntegerCurrent B) (φ : Link B → ℝ) (a C z gamma : ℝ)
    (componentMax : CurrentComponentClass j → ℝ)
    (ha : 1 ≤ a) (hC : 0 ≤ C)
    (hMax : ∀ c ∈ currentComponents j, 0 ≤ componentMax c)
    (hgamma : gamma ≤ 5 * z)
    (hz : z ≤ Real.exp (-(a * (currentEnergy j + currentLength j))))
    (hphase : ∀ c ∈ currentComponents j,
      |currentPhase φ (currentComponentCurrent j c)| ≤ C * componentMax c *
        currentEnergy (currentComponentCurrent j c) *
          ((currentComponentSupport j c).card : ℝ)^4) :
    gamma * (currentPhase φ j)^2 ≤
      ∑ c ∈ currentComponents j,
        (20 * C^2 / a^2) *
          ((currentComponentSupport j c).card : ℝ)^8 *
            Real.exp (- (a * ((currentComponentSupport j c).card : ℝ))) *
              componentMax c^2 := by
  apply currentComponents_jensen_error_le_componentMajorants
    j a C z gamma (currentPhase φ j)
    (fun c => currentPhase φ (currentComponentCurrent j c)) componentMax
    ha hC hMax ?_ hgamma hz hphase
  exact currentPhase_eq_sum_components φ j


end
end FroehlichSpencer.FS82.Currents

end
