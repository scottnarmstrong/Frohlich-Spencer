/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.PrimalInterface.NormalizedLaw
public import FroehlichSpencer.FS82.PrimalInterface.LatticeBridge

/-!
# the literal primal Villain law and Wilson expectation
-/

@[expose] public section

namespace FroehlichSpencer.FS82.PrimalInterface

open MeasureTheory
open FroehlichSpencer.FS82.Cubical


/-- The periodized Gaussian is invariant under shifts by integer multiples of `2π`. -/
theorem villainWeight_sub_two_pi_mul_int (β x : ℝ) (k : ℤ) :
    Wilson.villainWeight β (x - 2 * Real.pi * k) = Wilson.villainWeight β x := by
  unfold Wilson.villainWeight
  rw [← (Equiv.addRight k).tsum_eq fun m : ℤ => Real.exp (-(β / 2) * (x - 2 * Real.pi * m) ^ 2)]
  refine tsum_congr fun n => ?_
  simp only [Equiv.coe_addRight, Int.cast_add]
  congr 1
  ring

/-- The internal circle weight at the point of angle `x` is the periodized Gaussian at `x`. -/
theorem villainWeight_circleRepresentative (β x : ℝ) :
    Wilson.villainWeight β (2 * Real.pi * Wilson.circleRepresentative (angleToCircle x)) =
      Wilson.villainWeight β x := by
  have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hcoe : ((Wilson.circleRepresentative (angleToCircle x) : ℝ) : UnitAddCircle) =
      ((x / (2 * Real.pi) : ℝ) : UnitAddCircle) := Wilson.circleRepresentative_coe _
  obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp (QuotientAddGroup.eq.mp hcoe)
  have hrep : 2 * Real.pi * Wilson.circleRepresentative (angleToCircle x) =
      x - 2 * Real.pi * k := by
    have hk' : (k : ℝ) = -Wilson.circleRepresentative (angleToCircle x) + x / (2 * Real.pi) := by
      simpa using hk
    rw [hk']
    field_simp
    ring
  rw [hrep, villainWeight_sub_two_pi_mul_int]

/-- The literal series of FS82 (2.2) is the internal periodized Gaussian. -/
theorem tsum_ofReal_villain (β x : ℝ) (hβ : 0 < β) :
    ∑' n : ℤ, ENNReal.ofReal (Real.exp (-(β / 2) * (x + 2 * Real.pi * n) ^ 2)) =
      ENNReal.ofReal (Wilson.villainWeight β x) := by
  have hterm : ∀ n : ℤ, Real.exp (-(β / 2) * (x + 2 * Real.pi * n) ^ 2) =
      (fun m : ℤ => Real.exp (-(β / 2) * (x - 2 * Real.pi * m) ^ 2)) (Equiv.neg ℤ n) := by
    intro n
    simp only [Equiv.neg_apply, Int.cast_neg]
    congr 1
    ring
  have hsum : Summable fun n : ℤ => Real.exp (-(β / 2) * (x + 2 * Real.pi * n) ^ 2) := by
    have h := (Wilson.villainWeight_summable β x hβ).comp_injective (Equiv.neg ℤ).injective
    exact h.congr fun n => (hterm n).symm
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => (Real.exp_pos _).le) hsum]
  congr 1
  unfold Wilson.villainWeight
  rw [← (Equiv.neg ℤ).tsum_eq fun m : ℤ => Real.exp (-(β / 2) * (x - 2 * Real.pi * m) ^ 2)]
  exact tsum_congr hterm

variable (R : Surface.RectBox4)

/-- The internal circle configuration of a literal real configuration. -/
noncomputable abbrev toCircleConfig (θ : Surface.PrimalLinks R → ℝ) :
    Wilson.PrimalAngleConfig R.side :=
  circleConfig (linkEquiv R) θ

/-- Integer combinations of the link variables over the internal links. -/
theorem sum_links_toCircleConfig (a : Cell 4 R.side → ℤ) (θ : Surface.PrimalLinks R → ℝ) :
    ∑ j : Wilson.PrimalLinks R.side, a j.1 • toCircleConfig R θ j =
      angleToCircle (∑ ℓ : Surface.PrimalLinks R, (a ℓ.1 : ℝ) * θ ℓ) := by
  have h := angleToCircle_sum (Finset.univ : Finset (Wilson.PrimalLinks R.side))
    (fun j => a j.1) (fun j => θ ((linkEquiv R).symm j))
  rw [← Equiv.sum_comp (linkEquiv R)
    (fun j : Wilson.PrimalLinks R.side => (a j.1 : ℝ) * θ ((linkEquiv R).symm j))] at h
  exact h

/-- The internal plaquette flux of the circle configuration is the literal `dθ_p`. -/
theorem primalPlaquetteFlux_toCircleConfig (θ : Surface.PrimalLinks R → ℝ)
    (p : Surface.PrimalPlaquettes R) :
    Wilson.primalPlaquetteFlux (toCircleConfig R θ) (plaquetteEquiv R p) =
      angleToCircle (Surface.primalPlaquetteCurl R θ p) := by
  unfold Wilson.primalPlaquetteFlux
  have hb : boundary (Finsupp.single (plaquetteEquiv R p).1 (1 : ℤ)) =
      boundaryBasis (B := R.side) p.1 := boundary_basis (B := R.side) p.1
  rw [hb, circleChainPairing_primalCircleCochain, sum_links_toCircleConfig]
  congr 1
  unfold Surface.primalPlaquetteCurl
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [literal_boundaryBasis_apply]

/-- The literal density is the internal density at the circle configuration. -/
theorem literal_density_eq (β : ℝ) (hβ : 0 < β) (θ : Surface.PrimalLinks R → ℝ) :
    (∏ p : Surface.PrimalPlaquettes R,
        ∑' n : ℤ, ENNReal.ofReal
          (Real.exp (-(β / 2) * (Surface.primalPlaquetteCurl R θ p + 2 * Real.pi * n) ^ 2))) =
      ENNReal.ofReal (Wilson.primalVillainDensity (B := R.side) β (toCircleConfig R θ)) := by
  unfold Wilson.primalVillainDensity
  rw [ENNReal.ofReal_prod_of_nonneg
    (fun p _ => (Wilson.villainCircleWeight_pos β _ hβ).le),
    ← Equiv.prod_comp (plaquetteEquiv R)]
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [tsum_ofReal_villain β _ hβ, primalPlaquetteFlux_toCircleConfig,
    Wilson.villainCircleWeight_eq_periodized β _ hβ, villainWeight_circleRepresentative]

/-- The literal law in its circle form. -/
theorem primalVillainLaw_eq (β : ℝ) (hβ : 0 < β) :
    Surface.primalVillainLaw R β hβ =
      (((angleBase (Surface.PrimalLinks R)).withDensity fun θ =>
          ENNReal.ofReal (Wilson.primalVillainDensity (B := R.side) β
            (circleConfig (linkEquiv R) θ))) Set.univ)⁻¹ •
        ((angleBase (Surface.PrimalLinks R)).withDensity fun θ =>
          ENNReal.ofReal (Wilson.primalVillainDensity (B := R.side) β
            (circleConfig (linkEquiv R) θ))) := by
  have hρ : (fun θ : Surface.PrimalLinks R → ℝ =>
      ∏ p : Surface.PrimalPlaquettes R,
        ∑' n : ℤ, ENNReal.ofReal
          (Real.exp (-(β / 2) * (Surface.primalPlaquetteCurl R θ p + 2 * Real.pi * n) ^ 2))) =
      fun θ => ENNReal.ofReal (Wilson.primalVillainDensity (B := R.side) β
        (circleConfig (linkEquiv R) θ)) := funext fun θ => literal_density_eq R β hβ θ
  unfold Surface.primalVillainLaw
  simp only [hρ]

/-- The internal partition function as a Haar integral over the torus. -/
theorem primalVillainPartition_eq (β : ℝ) :
    Wilson.primalVillainPartition (B := R.side) β =
      ∫ z, Wilson.primalVillainDensity (B := R.side) β z ∂torusHaar (Wilson.PrimalLinks R.side) :=
  rfl

/-- **Gate.** The literal primal Villain law is a probability measure. -/
theorem primalVillainLaw_isProbabilityMeasure (β : ℝ) (hβ : 0 < β) :
    IsProbabilityMeasure (Surface.primalVillainLaw R β hβ) := by
  rw [primalVillainLaw_eq]
  refine isProbabilityMeasure_normalized (linkEquiv R) _
    (Wilson.primalVillainDensity_continuous (B := R.side) β)
    (fun z => (Wilson.primalVillainDensity_pos β z hβ).le) ?_
  rw [← primalVillainPartition_eq]
  exact Wilson.primalVillainPartition_pos β hβ

/-- The literal Wilson observable is the internal one at the circle configuration, for a lattice
chain that agrees on the box with the boundary of the internal sheet. -/
theorem wilsonLoopObservable_eq (loop : Surface.LatticeChain) (S : Chain 4 R.side)
    (hS : ∀ c : Cell 4 R.side, loop (boxCellEmbedding R.origin c) = boundary S c)
    (θ : Surface.PrimalLinks R → ℝ) :
    Surface.wilsonLoopObservable R loop θ =
      Wilson.primalWilsonObservable (toCircleConfig R θ) S := by
  unfold Wilson.primalWilsonObservable Surface.wilsonLoopObservable
  rw [circleChainPairing_primalCircleCochain, sum_links_toCircleConfig, fourier_one_angleToCircle,
    ← Complex.exp_sum]
  congr 1
  rw [Complex.ofReal_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [primalCellEmbedding_eq, hS]

/-- **The expectation bridge.** -/
theorem wilsonLoopExpectation_eq (β : ℝ) (hβ : 0 < β) (loop : Surface.LatticeChain)
    (S : Chain 4 R.side)
    (hS : ∀ c : Cell 4 R.side, loop (boxCellEmbedding R.origin c) = boundary S c) :
    Surface.wilsonLoopExpectation R β hβ loop =
      Wilson.primalWilsonExpectation (B := R.side) β S := by
  have hobs : (fun θ : Surface.PrimalLinks R → ℝ => Surface.wilsonLoopObservable R loop θ) =
      fun θ => (fun z : Wilson.PrimalAngleConfig R.side => Wilson.primalWilsonObservable z S)
        (circleConfig (linkEquiv R) θ) := funext fun θ => wilsonLoopObservable_eq R loop S hS θ
  have hZ : 0 < ∫ z, Wilson.primalVillainDensity (B := R.side) β z
      ∂torusHaar (Wilson.PrimalLinks R.side) := by
    rw [← primalVillainPartition_eq]
    exact Wilson.primalVillainPartition_pos β hβ
  unfold Surface.wilsonLoopExpectation
  rw [primalVillainLaw_eq, hobs,
    integral_normalized (linkEquiv R) _ (Wilson.primalVillainDensity_continuous (B := R.side) β)
      (fun z => (Wilson.primalVillainDensity_pos β z hβ).le) hZ _
      (Wilson.continuous_primalWilsonObservable S)]
  rfl

end FroehlichSpencer.FS82.PrimalInterface

end
