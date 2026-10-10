/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.XY.CoerciveD
public import FroehlichSpencer.FS82.XY.PhaseD

/-!
# the activity envelope in every dimension

The three inputs of the envelope `amp ≤ exp(−a (‖ϱ‖² + L))` of FS82 (4.37), for the dual complex
of a box of dimension `d ≥ 3`.

* `card_cellBaseNear_le`, `card_activityNeighborhood_le`: for a collision relation contained in
  `cellBaseNear`, the conflict neighbourhood of a set `P` of cells has at most `6 ^ d · |P|`
  cells.

So the factor `3 ^ N₁` of the expansion is at most `3 ^ (6 ^ d · L)`.
* `family_gain_le`: for co-closed integer currents with pairwise disjoint supports and real
  coefficients `s_i`, `∑ s_i² ‖J_i‖² ≤ 4 d² · ⟨∑ s_i J_i, (d₁† d₁)⁻¹ ∑ s_i J_i⟩`.

This is the
  hypothesis under which the gains `g_i ∝ ‖J_i‖²` can be subtracted from the covariance of the
  phases (the renormalization (4.30)–(4.33)).
* `prod_activity_le`, `activity_envelope`: if the bare activities obey `z(n) ≤ exp(c₀ n²)`, the
  expansion coefficient is at most `3 ^ N · ∏ z(|J_e|)` with `N ≤ 6 ^ d · L`, and the gain is at
  least `κ ‖J‖²`, then the renormalized amplitude is at most `exp(−a (‖J‖² + L))` whenever
  `2a + c₀ + 6 ^ d · log 3 ≤ κ`.
-/

open scoped BigOperators

@[expose] public section

namespace FroehlichSpencer.FS82.XY.DualD

open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Gaussian
open FroehlichSpencer.FS82.Currents

variable {d : ℕ} {B : Box d}

/-! ## The conflict neighbourhood -/

open Classical in
/-- A dual cell has at most `6 ^ d` base-near cells of a given degree. -/
theorem card_cellBaseNear_le {n : ℕ} (e : DualDForm B n) :
    (Finset.univ.filter fun f : DualDForm B n => cellBaseNear f.1 e.1).card ≤ 6 ^ d := by
  have h := card_window_le (fun f : DualDForm B n => f.1) Subtype.val_injective
    (fun k => cellBase e.1 k) 1 1
  have h6 : 2 ^ d * (1 + 1 + 1) ^ d = 6 ^ d := by
    rw [← mul_pow]
    norm_num
  rw [← h6]
  refine le_trans (Finset.card_le_card ?_) h
  intro f hf
  have hfn : cellBaseNear f.1 e.1 := (Finset.mem_filter.mp hf).2
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact fun k => ⟨(hfn k).2, (hfn k).1⟩

/-- **The conflict neighbourhood of a set of cells has at most `6 ^ d` times its size.** -/
theorem card_activityNeighborhood_le {n : ℕ} (near : DualDForm B n → DualDForm B n → Prop)
    (hnear : ∀ a b, near a b → cellBaseNear a.1 b.1) (P : Finset (DualDForm B n)) :
    (ActivityLineage.activityNeighborhood Finset.univ P near).card ≤ 6 ^ d * P.card := by
  classical
  have hsub : ActivityLineage.activityNeighborhood Finset.univ P near ⊆
      P.biUnion fun p => Finset.univ.filter fun f : DualDForm B n => cellBaseNear f.1 p.1 := by
    intro q hq
    simp only [ActivityLineage.activityNeighborhood, Finset.mem_filter, Finset.mem_univ,
      true_and] at hq
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hq with hq | ⟨p, hp, hqp⟩
    · exact ⟨q, hq, cellBaseNear_refl q.1⟩
    · exact ⟨p, hp, hnear q p hqp⟩
  calc (ActivityLineage.activityNeighborhood Finset.univ P near).card
      ≤ (P.biUnion fun p => Finset.univ.filter fun f : DualDForm B n =>
          cellBaseNear f.1 p.1).card := Finset.card_le_card hsub
    _ ≤ ∑ p ∈ P, (Finset.univ.filter fun f : DualDForm B n => cellBaseNear f.1 p.1).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ P, 6 ^ d := Finset.sum_le_sum fun p _ => card_cellBaseNear_le p
    _ = 6 ^ d * P.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

/-! ## The gain of a family of separated currents -/

section Gain

variable {ι : Type*} [Fintype ι]

theorem currentVector_inner_self {E : Type*} [Fintype E] (J : E → ℤ) :
    inner ℝ (currentVector J) (currentVector J) = currentEnergy J := by
  rw [euclidean_inner_self_eq_sum_sq]
  rfl

/-- The squared norm of a combination of currents with disjoint supports. -/
theorem inner_self_sum_smul_currentVector {E : Type*} [Fintype E] (J : ι → E → ℤ)
    (hdisj : ∀ i j, i ≠ j → ∀ e, J i e ≠ 0 → J j e = 0) (s : ι → ℝ) :
    inner ℝ (∑ i, s i • currentVector (J i)) (∑ i, s i • currentVector (J i)) =
      ∑ i, s i ^ 2 * currentEnergy (J i) := by
  classical
  rw [euclidean_inner_self_eq_sum_sq]
  have hcoord : ∀ e : E, (∑ i, s i • currentVector (J i)) e = ∑ i, s i * (J i e : ℝ) := by
    intro e
    rw [WithLp.ofLp_sum, Finset.sum_apply]
    exact Finset.sum_congr rfl fun i _ => by simp [currentVector_apply]
  have hsq : ∀ e : E, (∑ i, s i * (J i e : ℝ)) ^ 2 = ∑ i, (s i * (J i e : ℝ)) ^ 2 := by
    intro e
    by_cases hex : ∃ i₀, J i₀ e ≠ 0
    · obtain ⟨i₀, hi₀⟩ := hex
      have hz : ∀ i, i ≠ i₀ → s i * (J i e : ℝ) = 0 := by
        intro i hi
        have h0 : J i e = 0 := hdisj i₀ i (Ne.symm hi) e hi₀
        simp [h0]
      rw [Finset.sum_eq_single i₀ (fun i _ hi => hz i hi)
          (fun h => absurd (Finset.mem_univ i₀) h),
        Finset.sum_eq_single i₀ (fun i _ hi => by rw [hz i hi]; ring)
          (fun h => absurd (Finset.mem_univ i₀) h)]
    · push Not at hex
      simp [hex]
  simp_rw [hcoord, hsq]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold currentEnergy
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun e _ => by ring

/-- **The gain of a family of separated co-closed currents.** -/
theorem family_gain_le (hd : 3 ≤ d) (J : ι → DualDForm B (d - 2) → ℤ)
    (hco : ∀ i, currentVector (J i) ∈ coClosed (dualDExactOneComplex hd B))
    (hdisj : ∀ i j, i ≠ j → ∀ e, J i e ≠ 0 → J j e = 0) (s : ι → ℝ) :
    ∑ i, s i ^ 2 * currentEnergy (J i) ≤
      4 * (d : ℝ) ^ 2 * quotientCovarianceQuadratic (dualDExactOneComplex hd B)
        ⟨∑ i, s i • currentVector (J i),
          Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hco i)⟩ := by
  rw [← inner_self_sum_smul_currentVector J hdisj s]
  exact dualD_normSq_le_quotientCovarianceQuadratic hd
    ⟨∑ i, s i • currentVector (J i),
      Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hco i)⟩

end Gain

/-! ## The envelope -/

/-- The product of the bare activities over the support of a current. -/
theorem prod_activity_le {E : Type*} [Fintype E] [DecidableEq E] (J : E → ℤ) (z : ℤ → ℝ)
    (c₀ : ℝ) (hz0 : ∀ n, 0 ≤ z n)
    (hz : ∀ n : ℤ, n ≠ 0 → z |n| ≤ Real.exp (c₀ * ((n : ℝ)) ^ 2)) :
    ∏ e ∈ currentSupport J, z |J e| ≤ Real.exp (c₀ * currentEnergy J) := by
  have hE : currentEnergy J = ∑ e ∈ currentSupport J, ((J e : ℤ) : ℝ) ^ 2 := by
    unfold currentEnergy
    symm
    refine Finset.sum_subset (Finset.subset_univ _) fun e _ he => ?_
    have h0 : J e = 0 := by
      by_contra hne
      exact he (mem_currentSupport_iff.mpr hne)
    simp [h0]
  rw [hE, Finset.mul_sum, Real.exp_sum]
  exact Finset.prod_le_prod₀ (fun e _ => hz0 |J e|)
    fun e he => hz (J e) (mem_currentSupport_iff.mp he)

/-- **The activity envelope.** -/
theorem activity_envelope {K gain E c₀ κ a : ℝ} {N L D : ℕ}
    (hK : K ≤ (3 : ℝ) ^ N * Real.exp (c₀ * E)) (hN : N ≤ D * L) (hLE : (L : ℝ) ≤ E)
    (hgain : κ * E ≤ gain / 2) (ha0 : 0 ≤ a)
    (ha : 2 * a + c₀ + (D : ℝ) * Real.log 3 ≤ κ) :
    K * Real.exp (-(gain / 2)) ≤ Real.exp (-(a * (E + (L : ℝ)))) := by
  have hL0 : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L
  have hE0 : 0 ≤ E := hL0.trans hLE
  have hlog : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have h3 : (3 : ℝ) ^ N = Real.exp ((N : ℝ) * Real.log 3) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num)]
    congr 1
    ring
  have hNle : (N : ℝ) * Real.log 3 ≤ (D : ℝ) * Real.log 3 * E := by
    have h1 : (N : ℝ) ≤ (D : ℝ) * (L : ℝ) := by exact_mod_cast hN
    have h2 : (D : ℝ) * (L : ℝ) ≤ (D : ℝ) * E :=
      mul_le_mul_of_nonneg_left hLE (Nat.cast_nonneg D)
    nlinarith
  calc K * Real.exp (-(gain / 2))
      ≤ ((3 : ℝ) ^ N * Real.exp (c₀ * E)) * Real.exp (-(gain / 2)) :=
        mul_le_mul_of_nonneg_right hK (Real.exp_pos _).le
    _ = Real.exp ((N : ℝ) * Real.log 3 + c₀ * E + -(gain / 2)) := by
        rw [h3, ← Real.exp_add, ← Real.exp_add]
    _ ≤ Real.exp (-(a * (E + (L : ℝ)))) := by
        apply Real.exp_le_exp.mpr
        have hκ : (2 * a + c₀ + (D : ℝ) * Real.log 3) * E ≤ κ * E :=
          mul_le_mul_of_nonneg_right ha hE0
        nlinarith [mul_nonneg ha0 (sub_nonneg.mpr hLE)]

end FroehlichSpencer.FS82.XY.DualD

end
