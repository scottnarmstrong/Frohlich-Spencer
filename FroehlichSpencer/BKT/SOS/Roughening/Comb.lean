/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.SOS.Roughening.Schwartz
public import FroehlichSpencer.BKT.SOS.Roughening.SchwartzFamily
public import FroehlichSpencer.BKT.SOS.Tilt.Law
public import FroehlichSpencer.BKT.Rotator.TheoremC.PinnedAdapter
public import FroehlichSpencer.BKT.Rotator.PinnedDensityCombLimit
public import FroehlichSpencer.BKT.Rotator.PoissonMultiSchwartz
public import FroehlichSpencer.BKT.Rotator.LatticeSchwartzSummability
public import FroehlichSpencer.BKT.Surface.SquareZeroConnected

/-!
# The pinned SOS model and its comb identification (the dipole tilt construction: FS81 §7.2, (7.16))

FS81 §7.2 builds the SOS state from the zero-exterior measures
`dμ_{I_β,Ω} = N_Ω⁻¹ ∏_{|i−j|=1, i∈Ω} I_β(φ(i) − φ(j)) ∏_{k∈Ω} dφ(k)` (`φ = 0` off `Ω`) by inserting
the comb `∏_j [1 + 2∑_q cos(2πqφ(j))]`. On the box `Ω = {0,…,L−1}²` the bonds `|i − j| = 1` with
`i ∈ Ω` are the edges of `squareZero L` (a boundary face has `4 − deg` parallel bonds to the
wired exterior `none`), and the comb makes the heights integers: the pinned SOS weight is
`∏_e e^{−β|∇n(e)|}` (`sosHeightWeight`), FS81's Dirichlet SOS model on the box.

* `pinnedField`, `pinnedGrad`: the zero-exterior field of bounded-face coordinates and its
  gradient on `squareZero L` (injective for `L > 1`, `pinnedGrad_injective`);
* `sosDensityCoords L β c`: the tilted interpolated density `∏_e e^{c(e)∇y(e)} I_β(∇y(e))` in
  height coordinates, Schwartz for `|c| ≤ β/2` (`exists_sosDensityCoords_schwartz`);
* `faceCombCutoffPairing_tendsto_latticeSum`: for a Schwartz density the box-comb pairings
  converge to the lattice sum (Fourier summability, the comb cutoff limit and multidimensional
  Poisson summation);
* `sosDensityCoords_intCast`: at integer heights the density is `e^{⟨c, ∇n⟩} ∏_e e^{−β|∇n(e)|}`;
* `integral_tiltDensity_pinnedComb`: the tilted rooted law of the angle variable `ψ = 2πh` with
  the root-relative comb is `(2π)^{L²+1}` times the comb pairing of the tilted density
  (the shear of the root phase, the root integral `2π` and the rescaling by `2π`, as
  `Rotator.TheoremC.integral_offsetEdgeDensity_pinnedComb`).
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.SOS.Roughening

open MeasureTheory Filter Topology Complex
open scoped SchwartzMap
open FroehlichSpencer.BKT.Generic
open FroehlichSpencer.BKT.Generic.PinnedCharges (SquareZeroBond Site)
open FroehlichSpencer.BKT.Rotator
open FroehlichSpencer.BKT.Rotator.TheoremC
open FroehlichSpencer.BKT.SOS.Tilt

variable {L : ℕ}

/-! ## Pinned fields on the wired box -/

/-- The zero-exterior field of bounded-face coordinates. -/
def pinnedField (y : Site L → ℝ) : RotatorDualFace L → ℝ := fun k => k.elim 0 y

/-- The gradient of the zero-exterior field on `squareZero L`. -/
def pinnedGrad (L : ℕ) : (Site L → ℝ) →ₗ[ℝ] (SquareZeroBond L → ℝ) where
  toFun y e := (squareZero L).grad (pinnedField y) e
  map_add' y z := by
    funext e
    have h : ∀ k, pinnedField (y + z) k = pinnedField y k + pinnedField z k := fun k => by
      cases k <;> simp [pinnedField]
    simp only [Multigraph.grad, h, Pi.add_apply]
    ring
  map_smul' a y := by
    funext e
    have h : ∀ k, pinnedField (a • y) k = a * pinnedField y k := fun k => by
      cases k <;> simp [pinnedField]
    simp only [Multigraph.grad, h, Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    ring

theorem pinnedGrad_apply (y : Site L → ℝ) (e : SquareZeroBond L) :
    pinnedGrad L y e = (squareZero L).grad (pinnedField y) e := rfl

/-- The pinned gradient is injective: a zero gradient makes the zero-exterior field constant on
the connected carrier. -/
theorem pinnedGrad_injective (hL : 1 < L) : Function.Injective (pinnedGrad L) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro y hy
  have hgrad : ∀ e, (squareZero L).grad (pinnedField y) e = 0 := fun e => congrFun hy e
  have henergy : (squareZero L).energy (pinnedField y) = 0 := by
    unfold Multigraph.energy
    exact Finset.sum_eq_zero fun e _ => by rw [hgrad e]; ring
  obtain ⟨a, ha⟩ := ((squareZero L).energy_eq_zero_iff_exists_const
    (squareZero_connected L hL) (pinnedField y)).mp henergy
  have ha0 : a = 0 := by
    have h := congrFun ha none
    simpa [pinnedField] using h.symm
  funext x
  have h := congrFun ha (some x)
  simpa [pinnedField, ha0] using h

/-! ## The tilted density and its Schwartz representative -/

/-- The tilted interpolated SOS density in height coordinates:
`∏_e e^{c(e) ∇y(e)} I_β(∇y(e))`. -/
def sosDensityCoords (L : ℕ) (β : ℝ) (c : SquareZeroBond L → ℝ) (y : Site L → ℝ) : ℂ :=
  ∏ e, sosTiltFactor β (c e) (pinnedGrad L y e)

/-- **The tilted density is Schwartz** for `0 < β ≤ 1`, `|c| ≤ β/2`, `L > 1`. -/
theorem exists_sosDensityCoords_schwartz (hL : 1 < L) {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1)
    {c : SquareZeroBond L → ℝ} (hc : ∀ e, |c e| ≤ β / 2) :
    ∃ f : 𝓢(Site L → ℝ, ℂ), ∀ y, f y = sosDensityCoords L β c y := by
  classical
  choose fe hfe using fun e => exists_sosTiltFactor_schwartz hβ hβ1 (hc e)
  obtain ⟨edgeProduct, hedgeProduct⟩ := exists_schwartz_pi_product_family fe
  let grad : (Site L → ℝ) →L[ℝ] (SquareZeroBond L → ℝ) := (pinnedGrad L).toContinuousLinearMap
  obtain ⟨K, -, hanti⟩ :=
    (pinnedGrad L).injective_iff_antilipschitz.mp (pinnedGrad_injective hL)
  have hanti' : AntilipschitzWith K grad := hanti
  refine ⟨(SchwartzMap.compCLMOfAntilipschitz ℂ grad.hasTemperateGrowth hanti') edgeProduct,
    fun y => ?_⟩
  rw [SchwartzMap.compCLMOfAntilipschitz_apply, Function.comp_apply, hedgeProduct]
  exact Finset.prod_congr rfl fun e _ => hfe e _

/-! ## The comb limit -/

/-- **The box-comb pairings of a Schwartz density converge to its lattice sum.** -/
theorem faceCombCutoffPairing_tendsto_latticeSum {ι : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace (UnitAddTorus ι)] [BorelSpace (UnitAddTorus ι)] (f : 𝓢(ι → ℝ, ℂ)) :
    Tendsto (fun N : ℕ => ∫ x : ι → ℝ, faceCombCutoff (ι := ι) N x * f x) atTop
      (𝓝 (∑' z : ι → ℤ, f (fun i => (z i : ℝ)))) := by
  have hcut := faceCombCutoffPairing_tendsto_fourier (f := (f : (ι → ℝ) → ℂ)) f.integrable
    (summable_faceFourierCoefficient_of_schwartz f)
  have hsum : ∑' q : FaceFrequency ι, faceFourierCoefficient (f : (ι → ℝ) → ℂ) q =
      ∑' z : ι → ℤ, f (fun i => (z i : ℝ)) := by
    calc ∑' q : FaceFrequency ι, faceFourierCoefficient (f : (ι → ℝ) → ℂ) q
        = ∑' q : FaceFrequency ι,
            multiEuclideanFourierCoefficient f (faceFrequencyEquiv ι q) :=
          tsum_congr fun q => faceFourierCoefficient_eq_multiEuclideanFourierCoefficient f q
      _ = ∑' q : ι → ℤ, multiEuclideanFourierCoefficient f q :=
          (faceFrequencyEquiv ι).tsum_eq (multiEuclideanFourierCoefficient f)
      _ = ∑' z : ι → ℤ, f (fun i => (z i : ℝ)) := poissonSummation_schwartz_pi_unconditional f
  rw [hsum] at hcut
  exact hcut

/-- **The comb limit of the tilted SOS density**: the pairings converge to the tilted height sum,
which is summable. -/
theorem sosCombPairing_tendsto (hL : 1 < L) {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1)
    {c : SquareZeroBond L → ℝ} (hc : ∀ e, |c e| ≤ β / 2) :
    Tendsto (fun N : ℕ => ∫ y, faceCombCutoff (ι := Site L) N y * sosDensityCoords L β c y)
      atTop (𝓝 (∑' n : Site L → ℤ, sosDensityCoords L β c (fun x => (n x : ℝ)))) ∧
      Summable (fun n : Site L → ℤ => sosDensityCoords L β c (fun x => (n x : ℝ))) := by
  classical
  obtain ⟨f, hf⟩ := exists_sosDensityCoords_schwartz hL hβ hβ1 hc
  have hfun : (f : (Site L → ℝ) → ℂ) = sosDensityCoords L β c := funext hf
  have h := faceCombCutoffPairing_tendsto_latticeSum f
  have hs := schwartz_pi_lattice_samples_summable f
  rw [hfun] at h hs
  exact ⟨h, hs⟩

/-! ## Integer heights -/

/-- The pinned gradient of integer heights is an integer. -/
theorem exists_pinnedGrad_intCast (n : Site L → ℤ) (e : SquareZeroBond L) :
    ∃ m : ℤ, pinnedGrad L (fun x => (n x : ℝ)) e = m := by
  refine ⟨(squareZero L).grad (fun k => k.elim (0 : ℤ) n) e, ?_⟩
  rw [pinnedGrad_apply]
  simp only [Multigraph.grad, Int.cast_sub]
  congr 1
  · cases (squareZero L).src e <;> simp [pinnedField]
  · cases (squareZero L).tgt e <;> simp [pinnedField]

/-- **The pinned SOS weight** `∏_e e^{−β|∇n(e)|}` of integer heights with zero exterior (FS81
§7.2: the bonds `|i − j| = 1`, `i ∈ Ω`, of the box, with `n = 0` off the box). -/
def sosHeightWeight (L : ℕ) (β : ℝ) (n : Site L → ℤ) : ℝ :=
  ∏ e, Real.exp (-(β * |pinnedGrad L (fun x => (n x : ℝ)) e|))

theorem sosHeightWeight_pos (L : ℕ) (β : ℝ) (n : Site L → ℤ) : 0 < sosHeightWeight L β n :=
  Finset.prod_pos fun _ _ => Real.exp_pos _

/-- At integer heights the tilted density is `e^{⟨c, ∇n⟩} ∏_e e^{−β|∇n(e)|}`. -/
theorem sosDensityCoords_intCast {β : ℝ} (hβ : 0 ≤ β) (c : SquareZeroBond L → ℝ)
    (n : Site L → ℤ) :
    sosDensityCoords L β c (fun x => (n x : ℝ)) =
      ((Real.exp (∑ e, c e * pinnedGrad L (fun x => (n x : ℝ)) e) *
        sosHeightWeight L β n : ℝ) : ℂ) := by
  unfold sosDensityCoords sosHeightWeight sosTiltFactor
  rw [Real.exp_sum, ← Finset.prod_mul_distrib, Complex.ofReal_prod]
  refine Finset.prod_congr rfl fun e _ => ?_
  obtain ⟨m, hm⟩ := exists_pinnedGrad_intCast n e
  rw [hm]
  have hI : Interp.sosInterp β ((m : ℝ) : ℂ) = ((Real.exp (-(β * |(m : ℝ)|)) : ℝ) : ℂ) := by
    rw [← Interp.sosInterp_intCast hβ m]
    norm_cast
  rw [hI, Complex.ofReal_mul, Complex.ofReal_exp]
  push_cast
  ring_nf

/-! ## The rooted comb integral -/

theorem shear_root_apply (φ : RotatorDualFace L → ℝ) (k : RotatorDualFace L) :
    Generic.shear none (rootShearVector L) φ k = pinnedField (fun x => φ (some x)) k + φ none := by
  rw [Generic.shear_apply_apply]
  cases k with
  | none => simp [rootShearVector, pinnedField]
  | some x => simp [rootShearVector, pinnedField]

/-- The bounded-coordinate integrand of the tilted rooted comb integral. -/
def sosCombIntegrand (L N : ℕ) (β : ℝ) (bt : SquareZeroBond L → ℝ) (y : Site L → ℝ) : ℝ :=
  Real.exp (tiltExponent (gradLinear (squareZero L)) bt (pinnedField y)) *
    (∏ e, (sosWeightψ β (((squareZero L).grad (pinnedField y) e : ℝ) : ℂ)).re) *
      ∏ x, dirichletComb N (y x)

theorem tiltDensity_pinnedComb_shear (L N : ℕ) (β : ℝ) (bt : SquareZeroBond L → ℝ)
    (φ : RotatorDualFace L → ℝ) :
    (fun ψ : RotatorDualFace L → ℝ => tiltDensity (squareZero L) (sosWeightψ β) 0 bt none ψ *
        ∏ k, pinnedCombLam L N k (ψ k - ψ none)) (Generic.shear none (rootShearVector L) φ) =
      (Set.Ico (-Real.pi) Real.pi).indicator 1 (φ none) *
        sosCombIntegrand L N β bt (fun x => φ (some x)) := by
  simp only
  have hψ := shear_root_apply φ
  have hnone : Generic.shear none (rootShearVector L) φ none = φ none := by
    rw [hψ]; simp [pinnedField]
  have hgrad : ∀ e, (squareZero L).grad (Generic.shear none (rootShearVector L) φ) e =
      (squareZero L).grad (pinnedField (fun x => φ (some x))) e := by
    intro e
    simp only [Multigraph.grad, hψ]
    ring
  have htilt : tiltExponent (gradLinear (squareZero L)) bt
      (Generic.shear none (rootShearVector L) φ) =
      tiltExponent (gradLinear (squareZero L)) bt (pinnedField (fun x => φ (some x))) := by
    unfold tiltExponent
    simp only [gradLinear_apply, hgrad]
  have hcomb : ∏ k, pinnedCombLam L N k (Generic.shear none (rootShearVector L) φ k -
      Generic.shear none (rootShearVector L) φ none) = ∏ x, dirichletComb N (φ (some x)) := by
    rw [Fintype.prod_option]
    simp only [pinnedCombLam, Option.elim, one_mul, hψ]
    refine Finset.prod_congr rfl fun x _ => ?_
    simp [pinnedField]
  unfold tiltDensity offsetEdgeDensity sosCombIntegrand
  rw [hcomb, hnone, htilt]
  simp_rw [hgrad]
  simp only [Pi.zero_apply, add_zero]
  ring

theorem pinnedField_smul (R : ℝ) (y : Site L → ℝ) (k : RotatorDualFace L) :
    pinnedField (R • y) k = R * pinnedField y k := by
  cases k <;> simp [pinnedField]

theorem sosWeightψ_two_pi_mul (β a : ℝ) :
    sosWeightψ β ((2 * Real.pi * a : ℝ) : ℂ) = Interp.sosInterp β (a : ℂ) := by
  unfold sosWeightψ
  congr 1
  have h2πc : (2 * (Real.pi : ℂ)) ≠ 0 := by
    have : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    exact_mod_cast this
  push_cast
  exact mul_div_cancel_left₀ _ h2πc

theorem sosCombIntegrand_smul (L N : ℕ) {β : ℝ} (hβ : 0 ≤ β) (bt : SquareZeroBond L → ℝ)
    (y : Site L → ℝ) :
    ((sosCombIntegrand L N β bt ((2 * Real.pi) • y) : ℝ) : ℂ) =
      faceCombCutoff (ι := Site L) N y *
        sosDensityCoords L β (fun e => 2 * Real.pi * bt e) y := by
  have hreal : ∀ a : ℝ, (((Interp.sosInterp β (a : ℂ)).re : ℝ) : ℂ) =
      Interp.sosInterp β (a : ℂ) :=
    fun a => Complex.ext rfl (by simp [(Interp.sosInterp_ofReal_im_eq_zero_and_re_pos hβ a).1])
  have hgrad2 : ∀ e, (squareZero L).grad (pinnedField ((2 * Real.pi) • y)) e =
      2 * Real.pi * pinnedGrad L y e := fun e => by
    rw [pinnedGrad_apply]
    simp only [Multigraph.grad, pinnedField_smul]
    ring
  have hedge : ∀ e, (sosWeightψ β (((squareZero L).grad (pinnedField ((2 * Real.pi) • y)) e :
      ℝ) : ℂ)).re = (Interp.sosInterp β (pinnedGrad L y e : ℂ)).re := fun e => by
    rw [hgrad2, sosWeightψ_two_pi_mul]
  have htilt : tiltExponent (gradLinear (squareZero L)) bt (pinnedField ((2 * Real.pi) • y)) =
      ∑ e, 2 * Real.pi * bt e * pinnedGrad L y e := by
    unfold tiltExponent
    simp only [gradLinear_apply, hgrad2]
    exact Finset.sum_congr rfl fun e _ => by ring
  have hD : sosDensityCoords L β (fun e => 2 * Real.pi * bt e) y =
      ((Real.exp (∑ e, 2 * Real.pi * bt e * pinnedGrad L y e) *
        ∏ e, (Interp.sosInterp β (pinnedGrad L y e : ℂ)).re : ℝ) : ℂ) := by
    unfold sosDensityCoords sosTiltFactor
    rw [Real.exp_sum, ← Finset.prod_mul_distrib, Complex.ofReal_prod]
    refine Finset.prod_congr rfl fun e _ => ?_
    rw [Complex.ofReal_mul (Real.exp _), hreal, Complex.ofReal_exp]
    push_cast
    ring_nf
  rw [faceCombCutoff_eq_prod, hD, ← Complex.ofReal_mul]
  congr 1
  unfold sosCombIntegrand
  simp_rw [hedge, htilt]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- **The tilted rooted comb integral is the comb pairing of the tilted density** (angle variable
`ψ = 2πh`; the tilt `b` of the angle variable is the tilt `2πb` of the heights). -/
theorem integral_tiltDensity_pinnedComb (N : ℕ) {β : ℝ} (hβ : 0 ≤ β)
    (bt : SquareZeroBond L → ℝ) :
    ∫ φ : RotatorDualFace L → ℝ,
        tiltDensity (squareZero L) (sosWeightψ β) 0 bt none φ *
          ∏ k, pinnedCombLam L N k (φ k - φ none) =
      (2 * Real.pi) ^ (Fintype.card (Site L) + 1) *
        (∫ y, faceCombCutoff (ι := Site L) N y *
          sosDensityCoords L β (fun e => 2 * Real.pi * bt e) y).re := by
  have hu : rootShearVector L none = 0 := rfl
  rw [← Generic.integral_comp_shear hu]
  simp_rw [tiltDensity_pinnedComb_shear]
  rw [integral_option_mul (Site L) _ (sosCombIntegrand L N β bt), integral_indicator_Ico_pi]
  have h2π : (0 : ℝ) < 2 * Real.pi := by positivity
  have hsmul := Measure.integral_comp_smul (volume : Measure (Site L → ℝ))
    (sosCombIntegrand L N β bt) (2 * Real.pi)
  rw [Module.finrank_fintype_fun_eq_card, abs_of_pos (inv_pos.mpr (pow_pos h2π _)),
    smul_eq_mul] at hsmul
  have hscale : ∫ y, sosCombIntegrand L N β bt y =
      (2 * Real.pi) ^ Fintype.card (Site L) *
        ∫ y, sosCombIntegrand L N β bt ((2 * Real.pi) • y) := by
    rw [hsmul, ← mul_assoc, mul_inv_cancel₀ (pow_pos h2π _).ne', one_mul]
  have hpair : (∫ y, faceCombCutoff (ι := Site L) N y *
      sosDensityCoords L β (fun e => 2 * Real.pi * bt e) y).re =
      ∫ y, sosCombIntegrand L N β bt ((2 * Real.pi) • y) := by
    simp_rw [← sosCombIntegrand_smul L N hβ bt]
    rw [integral_complex_ofReal, Complex.ofReal_re]
  rw [hscale, hpair, pow_succ]
  ring

end FroehlichSpencer.BKT.SOS.Roughening

end
