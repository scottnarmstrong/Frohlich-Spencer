/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Rotator.Ginibre.FreeLimit
public import FroehlichSpencer.BKT.Rotator.Ginibre.SquareBoxSum
public import FroehlichSpencer.BKT.Rotator.InternalLaw

/-!
# Ginibre's inequalities for the internal free-box plane-rotator law

The internal law `rotatorMeasureInternal L β` on the free spin box `{0, …, L}²`  is the
cosine Gibbs measure of the oriented edge frequencies of `rotatorFreeGraph L` with constant coupling
`β`; this gives Ginibre's inequalities for it directly. Its two-point function equals the
free-boundary two-point function of the square `squareBoxZ L` of `ℤ²`. Recentering the box
`{0, …, 2L}²` at `(L, L)` identifies it with the centered square `[-L, L]²`, so the marked
two-point expectation `⟨exp(iξ(θ_u - θ_v))⟩`, which is real by the reflection symmetry (FS81 (1.29),
J p. 533), converges to `freeTwoPointLimit` as `L → ∞`.
-/

@[expose] public section

open MeasureTheory Filter Topology

noncomputable section

namespace FroehlichSpencer.BKT.Rotator.Ginibre

variable {V E : Type*} [Fintype V] [DecidableEq V]

/-- The frequency `δ_{src e} - δ_{tgt e}` of an oriented edge of a multigraph. -/
def multigraphFrequency (G : Multigraph V E) (e : E) : Frequency V :=
  fun x => (if x = G.src e then 1 else 0) - (if x = G.tgt e then 1 else 0)

theorem phase_multigraphFrequency (G : Multigraph V E) (e : E) (θ : V → ℝ) :
    phase (multigraphFrequency G e) θ = θ (G.src e) - θ (G.tgt e) := by
  simp only [phase, multigraphFrequency, Int.cast_sub, Int.cast_ite, Int.cast_one, Int.cast_zero,
    sub_mul, ite_mul, one_mul, zero_mul, Finset.sum_sub_distrib, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]

variable (L : ℕ)

theorem rotatorSpinDensity_eq_cosineWeight (β : ℝ) :
    rotatorSpinDensity L β =
      cosineWeight (multigraphFrequency (rotatorFreeGraph L)) (fun _ => β) := by
  funext θ
  rw [rotatorSpinDensity, cosineWeight, cosineEnergy, Real.exp_sum]
  refine Finset.prod_congr rfl fun e _ => ?_
  rw [rotatorBondDensity, phase_multigraphFrequency]

/-- The internal free-box plane-rotator law is the cosine Gibbs measure of the oriented edges of the
free box with constant coupling `β`. -/
theorem rotatorMeasureInternal_eq_cosineGibbs (β : ℝ) :
    rotatorMeasureInternal L β =
      cosineGibbs (multigraphFrequency (rotatorFreeGraph L)) (fun _ => β) := by
  rw [rotatorMeasureInternal, cosineGibbs, rotatorPartitionIntegralInternal, cosinePartition,
    rotatorSpinDensity_eq_cosineWeight]

/-- Ginibre I for the internal law. -/
theorem integral_cos_rotatorMeasureInternal_nonneg {β : ℝ} (hβ : 0 ≤ β)
    (n : Frequency (RotatorSpinSite L)) :
    0 ≤ ∫ θ, Real.cos (phase n θ) ∂rotatorMeasureInternal L β := by
  rw [rotatorMeasureInternal_eq_cosineGibbs]
  exact integral_cos_cosineGibbs_nonneg _ (fun _ => hβ) n

/-- Ginibre II for the internal law. -/
theorem integral_cos_mul_cos_rotatorMeasureInternal_ge {β : ℝ} (hβ : 0 ≤ β)
    (n m : Frequency (RotatorSpinSite L)) :
    (∫ θ, Real.cos (phase n θ) ∂rotatorMeasureInternal L β) *
        (∫ θ, Real.cos (phase m θ) ∂rotatorMeasureInternal L β) ≤
      ∫ θ, Real.cos (phase n θ) * Real.cos (phase m θ) ∂rotatorMeasureInternal L β := by
  rw [rotatorMeasureInternal_eq_cosineGibbs]
  exact integral_cos_mul_cos_cosineGibbs_ge _ (fun _ => hβ) n m

/-- Monotonicity in `β` for the internal law. -/
theorem integral_cos_rotatorMeasureInternal_mono {β β' : ℝ} (hβ : 0 ≤ β) (hββ' : β ≤ β')
    (n : Frequency (RotatorSpinSite L)) :
    ∫ θ, Real.cos (phase n θ) ∂rotatorMeasureInternal L β ≤
      ∫ θ, Real.cos (phase n θ) ∂rotatorMeasureInternal L β' := by
  rw [rotatorMeasureInternal_eq_cosineGibbs, rotatorMeasureInternal_eq_cosineGibbs]
  exact integral_cos_cosineGibbs_mono _ (fun _ => hβ) (fun _ => hββ') n

/-- The reflection symmetry `⟨sin(n·θ)⟩ = 0` for the internal law. -/
theorem integral_sin_rotatorMeasureInternal (β : ℝ) (n : Frequency (RotatorSpinSite L)) :
    ∫ θ, Real.sin (phase n θ) ∂rotatorMeasureInternal L β = 0 := by
  rw [rotatorMeasureInternal_eq_cosineGibbs]
  exact integral_sin_cosineGibbs _ _ n

theorem phase_rotatorTwoPointFrequency {W : Type*} [Fintype W] [DecidableEq W] (a x : W)
    (ξ : ℤ) (θ : W → ℝ) :
    phase (rotatorTwoPointFrequency a x ξ) θ = ξ * (θ a - θ x) := by
  simp only [phase, rotatorTwoPointFrequency, Int.cast_add, Int.cast_ite, Int.cast_neg,
    Int.cast_zero, add_mul, ite_mul, neg_mul, zero_mul, Finset.sum_add_distrib,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

/-- **FS81 (1.29)** in finite volume: the marked two-point expectation `⟨exp(iξ(θ_a - θ_x))⟩`
under the internal law is the real number `⟨cos(ξ(θ_a - θ_x))⟩`. -/
theorem integral_rotatorSpinCharacter (β : ℝ) (a x : RotatorSpinSite L) (ξ : ℤ) :
    ∫ θ, rotatorSpinCharacter L a x ξ θ ∂rotatorMeasureInternal L β =
      ((∫ θ, Real.cos (ξ * (θ a - θ x)) ∂rotatorMeasureInternal L β : ℝ) : ℂ) := by
  have hchar (θ : RotatorAngleConfiguration L) : rotatorSpinCharacter L a x ξ θ =
      (Real.cos (ξ * (θ a - θ x)) : ℂ) + (Real.sin (ξ * (θ a - θ x)) : ℂ) * Complex.I := by
    rw [rotatorSpinCharacter, Complex.ofReal_cos, Complex.ofReal_sin, ← Complex.exp_mul_I]
    congr 1
    push_cast
    ring
  have hcont : Continuous fun θ : RotatorAngleConfiguration L => ξ * (θ a - θ x) := by fun_prop
  have hc : Integrable (fun θ : RotatorAngleConfiguration L => Real.cos (ξ * (θ a - θ x)))
      (rotatorMeasureInternal L β) :=
    Integrable.of_bound (Real.continuous_cos.comp hcont).aestronglyMeasurable 1
      (ae_of_all _ fun θ => by rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)
  have hs : Integrable (fun θ : RotatorAngleConfiguration L => Real.sin (ξ * (θ a - θ x)))
      (rotatorMeasureInternal L β) :=
    Integrable.of_bound (Real.continuous_sin.comp hcont).aestronglyMeasurable 1
      (ae_of_all _ fun θ => by rw [Real.norm_eq_abs]; exact Real.abs_sin_le_one _)
  have hsin : ∫ θ, Real.sin (ξ * (θ a - θ x)) ∂rotatorMeasureInternal L β = 0 := by
    have h := integral_sin_rotatorMeasureInternal L β (rotatorTwoPointFrequency a x ξ)
    simpa only [phase_rotatorTwoPointFrequency] using h
  simp_rw [hchar]
  rw [integral_add hc.ofReal (hs.ofReal.mul_const _), integral_mul_const, integral_complex_ofReal,
    integral_complex_ofReal, hsin]
  simp

theorem latticeAngle_coe {Λ : Finset (ℤ × ℤ)} (θ : Λ → ℝ) (x : Λ) :
    latticeAngle θ (x : ℤ × ℤ) = θ x := by
  rw [latticeAngle, dite_eq_left x.2]

theorem latticeAngle_siteToZ (θ : squareBoxZ L → ℝ) (p : RotatorSpinSite L) :
    latticeAngle θ (siteToZ p) = θ (squareBoxEquiv L p) := by
  rw [← squareBoxEquiv_apply_coe, latticeAngle_coe]

/-- The two-point function of the internal law is the free-boundary two-point function of the
square `{0, …, L}²` of `ℤ²`. -/
theorem integral_cos_rotatorMeasureInternal_eq_freeTwoPoint (β : ℝ) (ξ : ℤ)
    (a b : RotatorSpinSite L) :
    ∫ θ, Real.cos (ξ * (θ a - θ b)) ∂rotatorMeasureInternal L β =
      freeTwoPoint β ξ (squareBoxZ L) (siteToZ a) (siteToZ b) := by
  rw [rotatorMeasureInternal_eq_cosineGibbs, freeTwoPoint, freeRotatorMeasure]
  have h := integral_comp_cosineGibbs (multigraphFrequency (rotatorFreeGraph L)) (fun _ => β)
    (bondFrequency (squareBoxZ L)) (freeCoupling β (squareBoxZ L)) (squareBoxEquiv L).injective
    (fun θ' => ?_) (f := fun θ => Real.cos (ξ * (θ a - θ b))) (by fun_prop)
  · rw [← h]
    simp only [Function.comp_apply, latticeAngle_siteToZ]
  · simp only [cosineEnergy, phase_multigraphFrequency, phase_bondFrequency, Function.comp_apply,
      ← latticeAngle_siteToZ]
    rw [sum_rotatorInternalBond_eq_sum_latticeStep L
      (fun y z => β * Real.cos (latticeAngle θ' y - latticeAngle θ' z))]
    refine Fintype.sum_congr _ _ fun c => ?_
    rw [freeCoupling, latticeAngle_coe, latticeAngle_coe]
    split_ifs <;> simp

/-- The site of the free spin box `{0, …, 2L}²` at position `z` relative to the center `(L, L)`
(meaningful when `|z|∞ ≤ L`). -/
def boxSite (L : ℕ) (z : ℤ × ℤ) : RotatorSpinSite (2 * L) :=
  (Fin.ofNat (2 * L + 1) (z.1 + L).toNat, Fin.ofNat (2 * L + 1) (z.2 + L).toNat)

theorem siteToZ_boxSite {L : ℕ} {z : ℤ × ℤ} (h : boxRadius z ≤ L) :
    siteToZ (boxSite L z) = z + ((L : ℤ), (L : ℤ)) := by
  have h₁ : z.1.natAbs ≤ L := (le_max_left _ _).trans h
  have h₂ : z.2.natAbs ≤ L := (le_max_right _ _).trans h
  have k₁ : (z.1 + L).toNat < 2 * L + 1 := by omega
  have k₂ : (z.2 + L).toNat < 2 * L + 1 := by omega
  refine Prod.ext ?_ ?_ <;>
    simp only [siteToZ, boxSite, Fin.val_ofNat, Nat.mod_eq_of_lt k₁, Nat.mod_eq_of_lt k₂,
      Prod.fst_add, Prod.snd_add] <;> omega

theorem freeBox_eq_translateDomain (L : ℕ) :
    freeBox L = translateDomain (squareBoxZ (2 * L)) (-(L : ℤ), -(L : ℤ)) := by
  ext z
  rw [mem_freeBox, mem_translateDomain]
  simp only [squareBoxZ, Finset.mem_product, Finset.mem_Icc, Prod.fst_sub, Prod.snd_sub]
  push_cast
  omega

/-- The two-point function of the internal law on `{0, …, 2L}²` between the sites at relative
positions `u, v` is the free-boundary two-point function of the centered square `[-L, L]²`. -/
theorem integral_cos_rotatorMeasureInternal_boxSite (β : ℝ) (ξ : ℤ) {u v : ℤ × ℤ}
    (hu : boxRadius u ≤ L) (hv : boxRadius v ≤ L) :
    ∫ θ, Real.cos (ξ * (θ (boxSite L u) - θ (boxSite L v))) ∂rotatorMeasureInternal (2 * L) β =
      freeTwoPoint β ξ (freeBox L) u v := by
  rw [integral_cos_rotatorMeasureInternal_eq_freeTwoPoint, siteToZ_boxSite hu, siteToZ_boxSite hv,
    freeBox_eq_translateDomain, ← freeTwoPoint_translate β ξ (squareBoxZ (2 * L))
      (u + ((L : ℤ), (L : ℤ))) (v + ((L : ℤ), (L : ℤ))) (-(L : ℤ), -(L : ℤ))]
  congr 1 <;> ext <;> simp

/-- **Free thermodynamic limit of the internal law.** For `β ≥ 0` the marked two-point expectation
`⟨exp(iξ(θ_u - θ_v))⟩` of the free spin box `{0, …, 2L}²`, at the sites `u, v` relative to its
center, converges to the infinite-volume two-point function as `L → ∞`. -/
theorem tendsto_integral_rotatorSpinCharacter {β : ℝ} (hβ : 0 ≤ β) (ξ : ℤ) (u v : ℤ × ℤ) :
    Tendsto (fun L : ℕ => ∫ θ, rotatorSpinCharacter (2 * L) (boxSite L u) (boxSite L v) ξ θ
      ∂rotatorMeasureInternal (2 * L) β) atTop (𝓝 (freeTwoPointLimit β hβ ξ u v : ℂ)) := by
  refine ((Complex.continuous_ofReal.tendsto _).comp (tendsto_freeTwoPointLimit hβ ξ u v)).congr'
    ?_
  filter_upwards [eventually_ge_atTop (max (boxRadius u) (boxRadius v))] with L hL
  rw [Function.comp_apply, integral_rotatorSpinCharacter,
    integral_cos_rotatorMeasureInternal_boxSite L β ξ ((le_max_left _ _).trans hL)
      ((le_max_right _ _).trans hL)]

end FroehlichSpencer.BKT.Rotator.Ginibre

end
