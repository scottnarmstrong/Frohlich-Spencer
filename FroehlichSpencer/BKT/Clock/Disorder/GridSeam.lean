/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Clock.Disorder.SeamTwistExpansion
public import FroehlichSpencer.BKT.Bridge.SquareCarriers
import Mathlib.Tactic

/-!
# The grid seam profile on the free square

Three inputs for the grid case `ξ = k/N` of FS81's (7.5).

* **A box-uniform seam constant.** `exists_auxiliarySeamProfile` states its constant after fixing
  `L` and `r`.

The constant it uses comes from `exists_harmonicField`, which is uniform in the box.

`exists_uniform_clockDisorderSeamProfile` restates the decomposition with one constant `C₀` for
  every box, every seam length, every `N` and every `ξ`:
  `twist = ∇σ + θ` with `∑ θ² ≤ N² ξ² C₀ (1 + log(1 + r))`.
* **Transport to the free square.** The Fejér ratio lives on `squareFree (2L+1)`, while the
  seam decomposition lives on `rotatorFreeGraph (2L)`.

Their edges correspond under
  `squareFreeSourceGraphIsomorphism`, up to orientation signs.

`gridTransport θ` carries a bond
  offset across with those signs.

The compact bond product and `∑ θ²` are unchanged.
* **The grid packing loss.** When `Nξ ∈ ℤ` the twist lies in `2πℤ` on every bond.

Then the reduced
  gradient of `−σ` on the free square is controlled by the transported residual:
  `[∇(−σ)]²_{2π} ≤ θ²`.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Clock.Disorder

open FroehlichSpencer.BKT
open FroehlichSpencer.BKT.Rotator
open FroehlichSpencer.BKT.Rotator.TheoremC
open FroehlichSpencer.BKT.Villain
open FroehlichSpencer.BKT.Duality

/-! ### A box-uniform seam constant -/

theorem gridCurrentDivergence_sub {V E : Type*} [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : Multigraph V E) (q j : E → ℤ) (v : V) :
    currentDivergence G (q - j) v = currentDivergence G q v - currentDivergence G j v := by
  unfold currentDivergence
  have hsrc : (∑ e, if G.src e = v then (q e - j e) else 0) =
      (∑ e, if G.src e = v then q e else 0) -
        (∑ e, if G.src e = v then j e else 0) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun e _ => ?_
    split_ifs <;> simp
  have htgt : (∑ e, if G.tgt e = v then (q e - j e) else 0) =
      (∑ e, if G.tgt e = v then q e else 0) -
        (∑ e, if G.tgt e = v then j e else 0) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun e _ => ?_
    split_ifs <;> simp
  change ((∑ e, if G.src e = v then (q e - j e) else 0) -
      (∑ e, if G.tgt e = v then (q e - j e) else 0)) = _
  rw [hsrc, htgt]
  ring

/-- `exists_scaled_vortex_decomposition` with its constant chosen before the box. -/
theorem exists_uniform_vortex_decomposition :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (L : ℕ) (a x : RotatorSpinSite L),
      siteL1 a x + 1 ≤ (a.1 : ℕ) → (a.1 : ℕ) + siteL1 a x + 1 ≤ L →
      siteL1 a x + 1 ≤ (a.2 : ℕ) → (a.2 : ℕ) + siteL1 a x + 1 ≤ L →
      siteL1 a x + 1 ≤ (x.1 : ℕ) → (x.1 : ℕ) + siteL1 a x + 1 ≤ L →
      siteL1 a x + 1 ≤ (x.2 : ℕ) → (x.2 : ℕ) + siteL1 a x + 1 ≤ L →
      ∀ (ξ : ℝ) (q : RotatorInternalBond L → ℤ),
        (∀ v, rotatorCurrentDivergence q v = rotatorTwoPointFrequency a x 1 v) →
        ∃ (ψ : RotatorDualFace L → ℝ) (θ : RotatorInternalBond L → ℝ),
          (∀ e, 2 * Real.pi * ξ * (q e : ℝ) =
            (rotatorDualGraph L).grad ψ e + θ e) ∧
          (∑ e, θ e ^ 2) ≤ ξ ^ 2 * C₀ *
            (1 + Real.log (1 + (siteL1 a x : ℝ))) := by
  obtain ⟨C₀, hC₀, hfield⟩ := exists_harmonicField
  refine ⟨C₀, hC₀, ?_⟩
  intro L a x h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ ξ q hq
  obtain ⟨j, σ, hj, -, henergy⟩ := hfield L a x h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈
  have hneutral : ∀ v, rotatorCurrentDivergence (q - j) v = 0 := by
    intro v
    have hlinear : rotatorCurrentDivergence (q - j) v =
        rotatorCurrentDivergence q v - rotatorCurrentDivergence j v :=
      gridCurrentDivergence_sub (rotatorFreeGraph L) q j v
    rw [hlinear, hq v, hj v]
    ring
  let h : RotatorFaceHeight L := rotatorHeightFromCurrent (q - j)
  have hcurrent : rotatorFaceHeightCurrent h = q - j :=
    rotatorHeightFromCurrent_current (q - j) hneutral
  let ψ : RotatorDualFace L → ℝ := fun f =>
    ξ * (2 * Real.pi * (h.1 f : ℝ) - σ f)
  let θ : RotatorInternalBond L → ℝ := fun e =>
    ξ * (2 * Real.pi * (j e : ℝ) + (rotatorDualGraph L).grad σ e)
  refine ⟨ψ, θ, ?_, ?_⟩
  · intro e
    rw [Multigraph.grad]
    simp only [ψ, θ]
    have hce := congrFun hcurrent e
    simp only [rotatorFaceHeightCurrent] at hce
    have hcast : ((q e - j e : ℤ) : ℝ) =
        (h.1 ((rotatorDualGraph L).src e) : ℝ) -
          (h.1 ((rotatorDualGraph L).tgt e) : ℝ) := by exact_mod_cast hce.symm
    have hqeq : (q e : ℝ) = (j e : ℝ) + ((q e - j e : ℤ) : ℝ) := by
      push_cast
      ring
    rw [hqeq, hcast]
    rw [Multigraph.grad]
    ring
  · calc
      ∑ e, θ e ^ 2 = ξ ^ 2 * ∑ e, (2 * Real.pi * (j e : ℝ) +
          (rotatorDualGraph L).grad σ e) ^ 2 := by
        simp only [θ]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro e _
        ring
      _ ≤ ξ ^ 2 * (C₀ * (1 + Real.log (1 + (siteL1 a x : ℝ)))) :=
        mul_le_mul_of_nonneg_left henergy (sq_nonneg ξ)
      _ = ξ ^ 2 * C₀ * (1 + Real.log (1 + (siteL1 a x : ℝ))) := by ring

/-- `exists_auxiliarySeamProfile` with its constant chosen before the box and the seam. -/
theorem exists_uniform_auxiliarySeamProfile :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (L r : ℕ) (hbuf : 2 * r + 1 ≤ L) (hL : 0 < L) (ξ : ℝ),
      ∃ (σ : RotatorSpinSite (2 * L) → ℝ) (θ : RotatorInternalBond (2 * L) → ℝ),
        (∀ e, 2 * Real.pi * ξ *
          (if ∃ i : Fin r,
            e = .inr (verticalDualEdgeData ⟨L + i.val + 1, by omega⟩ ⟨L, by omega⟩)
            then (1 : ℤ) else 0 : ℝ) =
          (rotatorFreeGraph (2 * L)).grad σ e + θ e) ∧
        (∑ e, θ e ^ 2) ≤ ξ ^ 2 * C₀ * (1 + Real.log (1 + (r : ℝ))) := by
  obtain ⟨C₀, hC₀, hprofile⟩ := exists_uniform_vortex_decomposition
  refine ⟨C₀, hC₀, ?_⟩
  intro L r hbuf hL ξ
  let a := auxiliarySeamStart (L := L) hL
  let x := auxiliarySeamFinish (L := L) (r := r) hL (by omega)
  have hdist : siteL1 a x = r := by
    dsimp [siteL1, a, x, auxiliarySeamStart, auxiliarySeamFinish, siteAt]
    have hcoord : (L : ℤ) + 1 - ((L : ℤ) + (r : ℤ) + 1) = -(r : ℤ) := by ring
    rw [hcoord]
    simp
  have ha1 : a.1.val = L + 1 := by simp [a, auxiliarySeamStart, siteAt]
  have ha2 : a.2.val = L := by simp [a, auxiliarySeamStart, siteAt]
  have hx1 : x.1.val = L + r + 1 := by simp [x, auxiliarySeamFinish, siteAt]
  have hx2 : x.2.val = L := by simp [x, auxiliarySeamFinish, siteAt]
  have h₁ : siteL1 a x + 1 ≤ a.1.val := by rw [hdist, ha1]; omega
  have h₂ : a.1.val + siteL1 a x + 1 ≤ 2 * L + 1 := by rw [hdist, ha1]; omega
  have h₃ : siteL1 a x + 1 ≤ a.2.val := by rw [hdist, ha2]; omega
  have h₄ : a.2.val + siteL1 a x + 1 ≤ 2 * L + 1 := by rw [hdist, ha2]; omega
  have h₅ : siteL1 a x + 1 ≤ x.1.val := by rw [hdist, hx1]; omega
  have h₆ : x.1.val + siteL1 a x + 1 ≤ 2 * L + 1 := by rw [hdist, hx1]; omega
  have h₇ : siteL1 a x + 1 ≤ x.2.val := by rw [hdist, hx2]; omega
  have h₈ : x.2.val + siteL1 a x + 1 ≤ 2 * L + 1 := by rw [hdist, hx2]; omega
  have hdiv : ∀ v, rotatorCurrentDivergence (auxiliarySeamCurrent (L := L) (r := r)) v =
      rotatorTwoPointFrequency a x 1 v := by
    simpa only [a, x] using auxiliarySeamCurrent_divergence hbuf hL
  obtain ⟨ψ, θaux, heq, henergy⟩ :=
    hprofile (2 * L + 1) a x h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ ξ auxiliarySeamCurrent hdiv
  let σ : RotatorSpinSite (2 * L) → ℝ := auxFaceShift ψ
  let θ : RotatorInternalBond (2 * L) → ℝ := fun e => θaux (auxEdgeMap e)
  refine ⟨σ, θ, ?_, ?_⟩
  · intro e
    have hq := originalSeamPullback_indicator hbuf e
    have hlocal := heq (auxEdgeMap e)
    change 2 * Real.pi * ξ * (originalSeamPullback e : ℝ) =
      (rotatorDualGraph (2 * L + 1)).grad ψ (auxEdgeMap e) + θaux (auxEdgeMap e) at hlocal
    rw [hq] at hlocal
    rw [auxFaceShift_grad_eq] at hlocal
    simpa [σ, θ, Int.cast_ite] using hlocal
  · calc
      (∑ e, θ e ^ 2) ≤ ∑ e : RotatorInternalBond (2 * L + 1), θaux e ^ 2 :=
        auxEdgeMap_energy_le θaux
      _ ≤ ξ ^ 2 * C₀ * (1 + Real.log (1 + (siteL1 a x : ℝ))) := henergy
      _ = ξ ^ 2 * C₀ * (1 + Real.log (1 + (r : ℝ))) := by rw [hdist]

/-- **The box-uniform seam decomposition** (`exists_clockDisorderSeamProfile` with one constant
for every box, seam length, clock order and twist). -/
theorem exists_uniform_clockDisorderSeamProfile :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (L r : ℕ) (hbuf : 2 * r + 1 ≤ L) (hL : 0 < L) (N : ℕ) (ξ : ℝ),
      ∃ σ : RotatorSpinSite (2 * L) → ℝ,
        ∃ θ : RotatorInternalBond (2 * L) → ℝ,
          (∀ e, clockDisorderSeamTwist (r := r) hL (show r ≤ L by omega) N ξ e =
            (rotatorFreeGraph (2 * L)).grad σ e + θ e) ∧
          (∑ e, θ e ^ 2) ≤ (N : ℝ) ^ 2 * ξ ^ 2 * C₀ *
            (1 + Real.log (1 + (r : ℝ))) := by
  obtain ⟨C₀, hC₀, hprofile⟩ := exists_uniform_auxiliarySeamProfile
  refine ⟨C₀, hC₀, ?_⟩
  intro L r hbuf hL N ξ
  have hr : r ≤ L := by omega
  obtain ⟨σ, θ, hdecomp, henergy⟩ := hprofile L r hbuf hL (-(N : ℝ) * ξ)
  refine ⟨σ, θ, ?_, ?_⟩
  · intro e
    rw [clockDisorderSeamTwist_eq_indicator hL hr N ξ e]
    exact hdecomp e
  · calc
      (∑ e, θ e ^ 2) ≤ (-(N : ℝ) * ξ) ^ 2 * C₀ *
          (1 + Real.log (1 + (r : ℝ))) := henergy
      _ = (N : ℝ) ^ 2 * ξ ^ 2 * C₀ *
          (1 + Real.log (1 + (r : ℝ))) := by ring

/-!
### Transport to the free square
-/

/--
The orientation sign of a  free-square edge relative to its positive-step image.
-/
def gridSign (L : ℕ) (e : SquareFreeEdge L) : ℝ :=
  if (Lattice2D.squareFreeGraph L).src ((squareFreeSourceGraphIsomorphism L).edges e) =
      (squareFree L).src e then 1 else -1

theorem gridSign_sq (L : ℕ) (e : SquareFreeEdge L) : gridSign L e ^ 2 = 1 := by
  unfold gridSign
  split_ifs <;> norm_num

theorem gridSign_eq (L : ℕ) (e : SquareFreeEdge L) : gridSign L e = 1 ∨ gridSign L e = -1 := by
  unfold gridSign
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

/--
The free-square gradient is the signed positive-step gradient.
-/
theorem squareFree_grad_eq_gridSign (L : ℕ) (f : Fin L × Fin L → ℝ) (e : SquareFreeEdge L) :
    (squareFree L).grad f e =
      gridSign L e * (Lattice2D.squareFreeGraph L).grad f ((squareFreeSourceGraphIsomorphism L).edges e) := by
  set I := squareFreeSourceGraphIsomorphism L
  have hv : ∀ v, I.vertices v = v := fun v => rfl
  unfold gridSign
  rw [Multigraph.grad, Multigraph.grad]
  rcases I.endpoints e with ⟨hs, ht⟩ | ⟨hs, ht⟩
  · rw [hv] at hs ht
    split_ifs with h
    · rw [hs, ht]
      ring
    · exact absurd hs h
  · rw [hv] at hs ht
    split_ifs with h
    · exact absurd (hs.symm.trans h).symm ((squareFree L).src_ne_tgt e)
    · rw [hs, ht]
      ring

/--
A positive-step bond field carried to the free square with orientation signs.
-/
def gridTransport (L : ℕ) (θ : Lattice2D.SquareFreeEdge L → ℝ) : SquareFreeEdge L → ℝ :=
  fun e => gridSign L e * θ ((squareFreeSourceGraphIsomorphism L).edges e)

theorem gridTransport_zero (L : ℕ) : gridTransport L 0 = 0 := by
  funext e
  simp [gridTransport]

/-- The compact bond product is unchanged by the transport. -/
theorem compactClockBondProduct_gridTransport (L : ℕ) (β n : ℝ) (φ : Fin L × Fin L → ℝ)
    (θ : Lattice2D.SquareFreeEdge L → ℝ) :
    compactClockBondProduct (squareFree L) β n φ (gridTransport L θ) =
      compactClockBondProduct (Lattice2D.squareFreeGraph L) β n φ θ := by
  unfold compactClockBondProduct
  refine Fintype.prod_equiv (squareFreeSourceGraphIsomorphism L).edges _ _ fun e => ?_
  rw [squareFree_grad_eq_gridSign, gridTransport]
  rcases gridSign_eq L e with h | h
  · rw [h, one_mul, one_mul]
  · rw [h, show ∀ a b : ℝ, (-1 * a + -1 * b) / n = -((a + b) / n) from fun a b => by ring,
      Real.cos_neg]

/-- The residual energy is unchanged by the transport. -/
theorem sum_sq_gridTransport (L : ℕ) (θ : Lattice2D.SquareFreeEdge L → ℝ) :
    ∑ e, gridTransport L θ e ^ 2 = ∑ e, θ e ^ 2 :=
  Fintype.sum_equiv (squareFreeSourceGraphIsomorphism L).edges _ _ fun e => by
    rw [gridTransport, mul_pow, gridSign_sq, one_mul]

/-! ### The grid packing loss -/

/-- Reduction into `[−π, π)` does not increase the square. -/
theorem sq_toIcoMod_le (x : ℝ) : toIcoMod Real.two_pi_pos (-Real.pi) x ^ 2 ≤ x ^ 2 := by
  have hm := toIcoMod_mem_Ico Real.two_pi_pos (-Real.pi) x
  by_cases hx : x ∈ Set.Ico (-Real.pi) (-Real.pi + 2 * Real.pi)
  · rw [(toIcoMod_eq_self Real.two_pi_pos).2 hx]
  · rw [Set.mem_Ico, not_and_or, not_le, not_lt] at hx
    have hπ := Real.pi_pos
    apply sq_le_sq.mpr
    have h1 : |toIcoMod Real.two_pi_pos (-Real.pi) x| ≤ Real.pi :=
      abs_le.mpr ⟨hm.1, by linarith [hm.2]⟩
    have h2 : Real.pi ≤ |x| := by
      rcases hx with hx | hx
      · exact le_abs.mpr (Or.inr (by linarith))
      · exact le_abs.mpr (Or.inl (by linarith))
    linarith

/--
**The grid packing loss.** If the twist `t = ∇σ + θ` takes values in `2πℤ`, the reduced
-square gradient of `−σ` is bounded by the transported residual.
-/
theorem sq_toIcoMod_grad_neg_le {L : ℕ} (σ : Fin L × Fin L → ℝ)
    (θ t : Lattice2D.SquareFreeEdge L → ℝ)
    (ht : ∀ e, t e = (Lattice2D.squareFreeGraph L).grad σ e + θ e)
    (hint : ∀ e, ∃ m : ℤ, t e = 2 * Real.pi * m) (e : SquareFreeEdge L) :
    toIcoMod Real.two_pi_pos (-Real.pi) ((squareFree L).grad (-σ) e) ^ 2 ≤
      gridTransport L θ e ^ 2 := by
  set I := squareFreeSourceGraphIsomorphism L
  obtain ⟨m, hm⟩ := hint (I.edges e)
  have hneg : (Lattice2D.squareFreeGraph L).grad (-σ) (I.edges e) =
      -(Lattice2D.squareFreeGraph L).grad σ (I.edges e) := by
    simp only [Multigraph.grad, Pi.neg_apply]
    ring
  obtain ⟨m', hm'⟩ : ∃ m' : ℤ, gridSign L e * t (I.edges e) = m' • (2 * Real.pi) := by
    rcases gridSign_eq L e with h | h
    · exact ⟨m, by rw [h, hm, zsmul_eq_mul]; ring⟩
    · exact ⟨-m, by rw [h, hm, zsmul_eq_mul]; push_cast; ring⟩
  have hgrad : (squareFree L).grad (-σ) e = gridTransport L θ e - m' • (2 * Real.pi) := by
    rw [squareFree_grad_eq_gridSign, hneg, ← hm', ht, gridTransport]
    ring
  rw [hgrad, toIcoMod_sub_zsmul]
  exact sq_toIcoMod_le _

end FroehlichSpencer.BKT.Clock.Disorder

end
