/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Clock.Compact.FejerLimit
public import FroehlichSpencer.BKT.Ginibre.Models
public import FroehlichSpencer.BKT.Rotator.Ginibre.SquareBox
public import FroehlichSpencer.BKT.Bridge.SquareCarriers
import Mathlib.Tactic

/-!
# The clock two-point function as a Fejér limit

* **`clockModel_twoPoint_squareBox`**: the free-boundary clock two-point function of the Ginibre
  `clockModel` on `{0, …, L}²` (FS81 (7.1)) as a ratio of finite sums over the clock
  configurations of the free spin box.
* `sum_cos_squareFree_eq`: the and positive-step square carriers have the same cosine edge
  sums.
* **`tendsto_clockFejerRatio`**: under the compact clock law on the KP square of side `L + 1`,
  the Fejér-weighted ratio of `cos((ξ/N)(φ_o − φ_x))` tends to the clock two-point function.

The cell centers `c_a/N = 2πa/N + π(1 − N)/N` are a rotated clock grid, and all functions
  involved depend only on differences of angles.
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.Clock.Compact

open MeasureTheory Filter Topology
open FroehlichSpencer.BKT.Ginibre
open FroehlichSpencer.BKT.Rotator FroehlichSpencer.BKT.Rotator.Ginibre
open FroehlichSpencer.BKT.Clock.Periodic

/-! ### The clock two-point function on a square as a ratio of finite sums -/

/-- The clock angles of a configuration `k` of the `ℤ_N` clock: `θ_p = 2π k_p / N`. -/
def clockAngles {W : Type*} (N : ℕ) (k : W → Fin N) : W → ℝ :=
  fun p => 2 * Real.pi * (k p : ℝ) / N

/-- The clock Boltzmann weight of a configuration on the free spin box `{0, …, L}²`:
`exp(β ∑_e cos(θ_src − θ_tgt))` over its internal bonds. -/
def clockBoxWeight (N L : ℕ) (β : ℝ) (k : RotatorSpinSite L → Fin N) : ℝ :=
  Real.exp (∑ e : RotatorInternalBond L, β * Real.cos
    (clockAngles N k ((rotatorFreeGraph L).src e) - clockAngles N k ((rotatorFreeGraph L).tgt e)))

theorem clockModel_pairWeight_squareBox (N L : ℕ) (hN : 0 < N) {β : ℝ} (hβ : 0 ≤ β)
    (θ : squareBoxZ L → ℝ) :
    pairWeight (bondFrequency (squareBoxZ L)) ((clockModel N hN β hβ).bondWeight (squareBoxZ L)) θ =
      Real.exp (∑ e : RotatorInternalBond L, β * Real.cos
        (θ (squareBoxEquiv L ((rotatorFreeGraph L).src e)) -
          θ (squareBoxEquiv L ((rotatorFreeGraph L).tgt e)))) := by
  classical
  have hsum := sum_rotatorInternalBond_eq_sum_latticeStep L
    (fun y z => β * Real.cos (latticeAngle θ y - latticeAngle θ z))
  simp only [latticeAngle_siteToZ] at hsum
  rw [hsum, Real.exp_sum, pairWeight]
  refine Fintype.prod_congr _ _ fun c => ?_
  rw [FreeModel.bondWeight, phase_bondFrequency, latticeAngle_coe, latticeAngle_coe]
  split_ifs
  · rfl
  · simp

/-- **The `ℤ_N` clock two-point function on the square `{0, …, L}²`** (FS81 (7.1), the Ginibre
`clockModel`) as a ratio of finite sums over the clock configurations of the free spin box. -/
theorem clockModel_twoPoint_squareBox (N L : ℕ) (hN : 0 < N) {β : ℝ} (hβ : 0 ≤ β) (ξ : ℤ)
    (a b : RotatorSpinSite L) :
    (clockModel N hN β hβ).twoPoint ξ (squareBoxZ L) (siteToZ a) (siteToZ b) =
      (∑ k : RotatorSpinSite L → Fin N,
          Real.cos (ξ * (clockAngles N k a - clockAngles N k b)) * clockBoxWeight N L β k) /
        ∑ k : RotatorSpinSite L → Fin N, clockBoxWeight N L β k := by
  classical
  have hν : (clockModel N hN β hβ).ν = clockMeasure N := rfl
  rw [FreeModel.twoPoint, FreeModel.gibbs, integral_pairGibbs (clockModel N hN β hβ).mass_ne_zero
    ((clockModel N hN β hβ).isBondWeight_bondWeight (squareBoxZ L)), pairPartition, hν,
    integral_siteProduct_clockMeasure, integral_siteProduct_clockMeasure]
  have he' : ∀ (k : squareBoxZ L → Fin N) (p : RotatorSpinSite L),
      (Equiv.arrowCongr (squareBoxEquiv L).symm (Equiv.refl (Fin N))) k p =
        k (squareBoxEquiv L p) := fun k p => rfl
  congr 1
  · refine Fintype.sum_equiv (Equiv.arrowCongr (squareBoxEquiv L).symm (Equiv.refl (Fin N)))
      _ _ fun k => ?_
    rw [clockModel_pairWeight_squareBox]
    simp only [latticeAngle_siteToZ, clockBoxWeight, clockAngles, he']
  · refine Fintype.sum_equiv (Equiv.arrowCongr (squareBoxEquiv L).symm (Equiv.refl (Fin N)))
      _ _ fun k => ?_
    rw [clockModel_pairWeight_squareBox]
    simp only [clockBoxWeight, clockAngles, he']

/-! ### The Fejér ratio of the compact clock law on the KP square -/

/-- The two carriers of the free square have the same cosine edge sums. -/
theorem sum_cos_squareFree_eq (L : ℕ) (f : Fin L × Fin L → ℝ) :
    ∑ e, Real.cos (f ((squareFree L).src e) - f ((squareFree L).tgt e)) =
      ∑ e, Real.cos (f ((Lattice2D.squareFreeGraph L).src e) -
        f ((Lattice2D.squareFreeGraph L).tgt e)) := by
  set I := squareFreeSourceGraphIsomorphism L
  have hv : ∀ v, I.vertices v = v := fun v => rfl
  rw [← I.edges.sum_comp]
  refine Finset.sum_congr rfl fun e _ => ?_
  rcases I.endpoints e with ⟨hsrc, htgt⟩ | ⟨hsrc, htgt⟩
  · rw [hsrc, htgt, hv, hv]
  · rw [hsrc, htgt, hv, hv, ← Real.cos_neg]
    ring_nf

theorem cellCenter_sub (N a b : ℕ) (hN : 0 < N) :
    (cellCenter N a - cellCenter N b) / N =
      2 * Real.pi * (a : ℝ) / N - 2 * Real.pi * (b : ℝ) / N := by
  unfold cellCenter
  field_simp
  ring

/-- The cell-center values of the compact clock density are the clock Boltzmann weights. -/
theorem clockDensity_cellCenter (N L : ℕ) (hN : 0 < N) (β : ℝ) (k : RotatorSpinSite L → Fin N) :
    clockDensity β N (squareFree (L + 1)) (fun v => cellCenter N (k v)) =
      clockBoxWeight N L β k := by
  unfold clockDensity clockBoxWeight
  rw [← Real.exp_sum]
  congr 1
  have h1 : ∀ e, β * Real.cos ((squareFree (L + 1)).grad (fun v => cellCenter N (k v)) e / N) =
      β * Real.cos (clockAngles N k ((squareFree (L + 1)).src e) -
        clockAngles N k ((squareFree (L + 1)).tgt e)) := by
    intro e
    rw [Multigraph.grad, cellCenter_sub N _ _ hN]
    rfl
  simp_rw [h1, ← Finset.mul_sum]
  congr 1
  exact sum_cos_squareFree_eq (L + 1) (clockAngles N k)

/-- **The Fejér ratio converges to the clock two-point function**: under the compact clock law on
the KP free square of side `L + 1`, the ratio of the Fejér-weighted integrals of
`cos((ξ/N)(φ_o − φ_x))` and of `1` tends to the clock two-point function of `{0, …, L}²`
(`clockModel_twoPoint_squareBox`). -/
theorem tendsto_clockFejerRatio (N L : ℕ) (hN : 0 < N) {β : ℝ} (hβ : 0 ≤ β) (ξ : ℕ)
    (o x : RotatorSpinSite L) :
    Tendsto (fun M : ℕ =>
      (∫ φ, Real.cos ((ξ : ℝ) / N * (φ o - φ x)) * ∏ v, fejerPolynomial M (φ v - clockOffset N)
          ∂clockLaw β N (squareFree (L + 1))) /
        ∫ φ, ∏ v, fejerPolynomial M (φ v - clockOffset N) ∂clockLaw β N (squareFree (L + 1)))
      atTop
        (𝓝 ((clockModel N hN β hβ).twoPoint (ξ : ℤ) (squareBoxZ L) (siteToZ o) (siteToZ x))) := by
  classical
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  set G := squareFree (L + 1)
  set m := ((clockBoxMass β N (relabelGraph G (siteEquiv (RotatorSpinSite L))))⁻¹).toReal
  have hm : 0 < m := by
    have h0 := clockBoxMass_pos (relabelGraph G (siteEquiv (RotatorSpinSite L))) hβ hN'
    have h1 := clockBoxMass_ne_top (n := (N : ℝ))
      (relabelGraph G (siteEquiv (RotatorSpinSite L))) hβ
    exact ENNReal.toReal_pos (ENNReal.inv_ne_zero.2 h1) (ENNReal.inv_ne_top.2 h0.ne')
  have hnum := tendsto_integral_clockLaw_fejer hβ (n := N) G
    (fun φ => Real.cos ((ξ : ℝ) / N * (φ o - φ x))) (by fun_prop) (C := 1)
    (fun φ => Real.abs_cos_le_one _)
  have hden := tendsto_integral_clockLaw_fejer hβ (n := N) G (fun _ => (1 : ℝ)) continuous_const
    (C := 1) (fun _ => by simp)
  simp only [one_mul, mul_one] at hden
  have hS0 : 0 < ∑ k : RotatorSpinSite L → Fin N,
      clockDensity β N G (fun v => cellCenter N (k v)) :=
    Finset.sum_pos (fun k _ => clockDensity_pos β N G _) ⟨fun _ => ⟨0, hN⟩, Finset.mem_univ _⟩
  have hA : 0 < m * (2 * Real.pi) ^ Fintype.card (RotatorSpinSite L) :=
    mul_pos hm (pow_pos (by positivity) _)
  have hlim := hnum.div hden (by rw [← mul_assoc]; exact (mul_pos hA hS0).ne')
  rw [clockModel_twoPoint_squareBox N L hN hβ (ξ : ℤ) o x]
  convert hlim using 2
  rw [← mul_assoc, ← mul_assoc, mul_div_mul_left _ _ hA.ne']
  congr 1
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [clockDensity_cellCenter N L hN β k, mul_comm]
    congr 1
    rw [show ((ξ : ℤ) : ℝ) = (ξ : ℝ) by push_cast; rfl, mul_sub, mul_sub]
    unfold clockAngles cellCenter
    field_simp
    ring_nf
  · exact Finset.sum_congr rfl fun k _ => (clockDensity_cellCenter N L hN β k).symm

end FroehlichSpencer.BKT.Clock.Compact

end
