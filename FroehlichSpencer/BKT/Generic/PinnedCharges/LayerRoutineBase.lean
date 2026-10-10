/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Generic.PinnedCharges.LayerRoutineLocal

/-!
For a wired density `ϱ`, the base pieces are `2 sgn ϱ(x) δ_x` at the charged bounded faces `x` of
the heavier parity class (`baseSites`).

On `squareZero` (not bipartite: the root has charge
`−Σρ`) single-colour bumps carry only `≥ ¼` of the neutralized mass; doubling the bumps restores
`½‖ϱ‖₁ ≤ Σ charges` (`half_mass_le_base`) at the price of gradient `2` and energy `16 ≤ 4·charge²`.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Generic.PinnedCharges.Layer

open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Rotator
open FroehlichSpencer.BKT.Generic.SpinWave

variable {L : ℕ}

/-- The doubled sign bump at the bounded face `x`. -/
def basePiece (ϱ : RotatorDualFace L → ℤ) (x : Site L) : RotatorDualFace L → ℝ :=
  fun j => if j = some x then 2 * signUnit (ϱ (some x)) else 0

/-- The mass of one parity class of bounded faces. -/
def parityMass (ϱ : RotatorDualFace L → ℤ) (b : ℕ) : ℝ :=
  ∑ x : Site L, if (x.1.val + x.2.val) % 2 = b then |(ϱ (some x) : ℝ)| else 0

/-- The heavier parity class. -/
def baseParity (ϱ : RotatorDualFace L → ℤ) : ℕ :=
  if parityMass ϱ 1 ≤ parityMass ϱ 0 then 0 else 1

/-- The charged bounded faces of the heavier parity class. -/
def baseSites (ϱ : RotatorDualFace L → ℤ) : Finset (Site L) := by
  classical
  exact Finset.univ.filter fun x => ϱ (some x) ≠ 0 ∧ (x.1.val + x.2.val) % 2 = baseParity ϱ

theorem abs_signUnit_le (q : ℤ) : |signUnit q| ≤ 1 := by
  unfold signUnit
  split_ifs <;> simp

theorem pairing_basePiece (ϱ ϱ' : RotatorDualFace L → ℤ) (x : Site L) :
    ∑ j, basePiece ϱ x j * (ϱ' j : ℝ) = 2 * signUnit (ϱ (some x)) * ϱ' (some x) := by
  classical
  rw [Finset.sum_eq_single (some x) (fun j _ hj => by simp [basePiece, hj]) (by simp)]
  simp [basePiece]

theorem pairing_basePiece_self (ϱ : RotatorDualFace L → ℤ) {x : Site L} (hx : ϱ (some x) ≠ 0) :
    Multigraph.pairing (basePiece ϱ x) (fun j => (ϱ j : ℝ)) = 2 * |(ϱ (some x) : ℝ)| := by
  unfold Multigraph.pairing
  rw [pairing_basePiece, mul_assoc, signUnit_mul_cast _ hx]

theorem grad_basePiece_incident {ϱ : RotatorDualFace L → ℤ} {x : Site L} {e : SquareZeroBond L}
    (h : (squareZero L).grad (basePiece ϱ x) e ≠ 0) :
    (squareZero L).src e = some x ∨ (squareZero L).tgt e = some x := by
  by_contra hne
  push Not at hne
  apply h
  simp [Multigraph.grad, basePiece, hne.1, hne.2]

theorem abs_grad_basePiece_le (ϱ : RotatorDualFace L → ℤ) (x : Site L) (e : SquareZeroBond L) :
    |(squareZero L).grad (basePiece ϱ x) e| ≤ 2 := by
  have hs := abs_signUnit_le (ϱ (some x))
  unfold Multigraph.grad basePiece
  by_cases h1 : (squareZero L).src e = some x <;> by_cases h2 : (squareZero L).tgt e = some x
  · exact absurd (h1.trans h2.symm) ((squareZero L).src_ne_tgt e)
  · simp only [h1, h2, ite_true, ite_false, sub_zero, abs_mul]
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  · simp only [h1, h2, ite_true, ite_false, zero_sub, abs_neg, abs_mul]
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  · simp [h1, h2]

theorem edgeCount_basePiece_le (ϱ : RotatorDualFace L → ℤ) (x : Site L) :
    ((Finset.univ.filter fun e => (squareZero L).grad (basePiece ϱ x) e ≠ 0).card : ℝ) ≤ 4 := by
  have hsub : (Finset.univ.filter fun e => (squareZero L).grad (basePiece ϱ x) e ≠ 0) ⊆
      Finset.univ.filter fun e : SquareZeroBond L =>
        (squareZero L).src e = some x ∨ (squareZero L).tgt e = some x :=
    fun e he => Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      grad_basePiece_incident (Finset.mem_filter.mp he).2⟩
  exact_mod_cast (Finset.card_le_card hsub).trans (card_incident_le_four x)

theorem energy_basePiece_le (ϱ : RotatorDualFace L → ℤ) (x : Site L) :
    (squareZero L).energy (basePiece ϱ x) ≤ 16 := by
  classical
  unfold Multigraph.energy
  have hfilter : ∑ e, (squareZero L).grad (basePiece ϱ x) e ^ 2 =
      ∑ e ∈ Finset.univ.filter fun e => (squareZero L).grad (basePiece ϱ x) e ≠ 0,
        (squareZero L).grad (basePiece ϱ x) e ^ 2 := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun e _ => ?_
    split_ifs with h
    · rfl
    · push Not at h; rw [h]; ring
  rw [hfilter]
  calc _ ≤ ∑ _e ∈ Finset.univ.filter fun e => (squareZero L).grad (basePiece ϱ x) e ≠ 0,
        (4 : ℝ) := Finset.sum_le_sum fun e _ => by
          have := abs_grad_basePiece_le ϱ x e
          nlinarith [abs_nonneg ((squareZero L).grad (basePiece ϱ x) e),
            sq_abs ((squareZero L).grad (basePiece ϱ x) e)]
    _ ≤ 16 := by
        rw [Finset.sum_const, nsmul_eq_mul]
        have := edgeCount_basePiece_le ϱ x
        nlinarith

/-- Two bumps at distinct faces with a common gradient edge sit at adjacent faces. -/
theorem l1_eq_one_of_grad_basePiece {ϱ ϱ' : RotatorDualFace L → ℤ} {x x' : Site L}
    (hne : x ≠ x') {e : SquareZeroBond L} (h : (squareZero L).grad (basePiece ϱ x) e ≠ 0)
    (h' : (squareZero L).grad (basePiece ϱ' x') e ≠ 0) : l1 x x' = 1 := by
  have h1 := siteDist_le_one_of_endpoints (grad_basePiece_incident h) (grad_basePiece_incident h')
  have h2 : l1 x x' ≠ 0 := by
    intro h0
    apply hne
    unfold l1 at h0
    exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))
  have : l1 x x' ≤ 1 := by exact_mod_cast h1
  omega

/-- **Half mass.** For a neutral wired density the doubled bumps on the heavier parity class carry
at least half of `‖ϱ‖₁`. -/
theorem half_mass_le_base (ϱ : RotatorDualFace L → ℤ) (hsum : ∑ j, ϱ j = 0) :
    (1 / 2 : ℝ) * ∑ j, |(ϱ j : ℝ)| ≤ ∑ x ∈ baseSites ϱ, 2 * |(ϱ (some x) : ℝ)| := by
  classical
  have hroot : ϱ none = -∑ x : Site L, ϱ (some x) := by
    rw [Fintype.sum_option] at hsum
    linarith
  have hsplit : ∑ j, |(ϱ j : ℝ)| = |(ϱ none : ℝ)| + ∑ x : Site L, |(ϱ (some x) : ℝ)| :=
    Fintype.sum_option _
  have hnone : |(ϱ none : ℝ)| ≤ ∑ x : Site L, |(ϱ (some x) : ℝ)| := by
    rw [hroot]
    push_cast
    rw [abs_neg]
    exact Finset.abs_sum_le_sum_abs _ _
  have hpar : ∑ x : Site L, |(ϱ (some x) : ℝ)| = parityMass ϱ 0 + parityMass ϱ 1 := by
    unfold parityMass
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rcases Nat.mod_two_eq_zero_or_one (x.1.val + x.2.val) with h | h <;> simp [h]
  have hbase : ∑ x ∈ baseSites ϱ, |(ϱ (some x) : ℝ)| = parityMass ϱ (baseParity ϱ) := by
    unfold baseSites parityMass
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hx : ϱ (some x) = 0
    · simp [hx]
    · simp [hx]
  have hmax : parityMass ϱ 0 + parityMass ϱ 1 ≤ 2 * parityMass ϱ (baseParity ϱ) := by
    unfold baseParity
    split_ifs with h <;> linarith
  rw [← Finset.mul_sum, hbase]
  linarith

/-- The bumps lie in the density domain around the routing center. -/
theorem support_basePiece_subset (hL : 1 < L) {ϱ : RotatorDualFace L → ℤ} (hϱ : ϱ ≠ 0)
    (hsum : ∑ j, ϱ j = 0) {x : Site L} (hx : ϱ (some x) ≠ 0) :
    Function.support (basePiece ϱ x) ⊆ (squareZero L).densityDomain ϱ (routineCenter ϱ) := by
  classical
  intro v hv
  have hvx : v = some x := by
    by_contra h
    exact hv (by simp [basePiece, h])
  subst hvx
  have hne : (chargeSupport (siteRestrict ϱ)).Nonempty :=
    ⟨x, by unfold chargeSupport; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩⟩
  obtain ⟨j, hj, hc, -⟩ := routineCenter_spec' ϱ hne
  have hj' : ϱ (some j) ≠ 0 := by unfold chargeSupport at hj; exact (Finset.mem_filter.mp hj).2
  have hd := (squareZero L).one_le_densityDiameter_of_neutral (squareZero_connected L hL) ϱ hϱ hsum
  have hle : (squareZero L).toSimpleGraph.dist (some x) (some j) ≤ (squareZero L).densityDiameter ϱ := by
    unfold Multigraph.densityDiameter
    exact Finset.le_sup (f := fun p : RotatorDualFace L × RotatorDualFace L =>
      (squareZero L).toSimpleGraph.dist p.1 p.2) (b := (some x, some j))
      (Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj'⟩⟩)
  show (squareZero L).toSimpleGraph.dist (some x) (routineCenter ϱ) <
    2 * (squareZero L).densityDiameter ϱ
  rw [hc]
  omega

end FroehlichSpencer.BKT.Generic.PinnedCharges.Layer

end
