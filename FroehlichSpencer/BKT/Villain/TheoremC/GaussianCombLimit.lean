/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Rotator.PoissonMultiSchwartz
public import FroehlichSpencer.BKT.Rotator.TheoremC.Defs
public import FroehlichSpencer.BKT.Rotator.TheoremC.PinnedAdapter
public import FroehlichSpencer.BKT.Rotator.PinnedDensityCombLimit
public import FroehlichSpencer.BKT.Rotator.PinnedDensityPoissonLimit
public import FroehlichSpencer.BKT.Rotator.PinnedDensitySchwartz
public import FroehlichSpencer.BKT.Villain.TheoremC.CurrentHeight
public import FroehlichSpencer.BKT.Generic.StripWeightScaling
public import Mathlib.Analysis.Complex.Liouville

/-! # Poisson limits for pinned Gaussian Villain heights -/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped SchwartzMap FourierTransform
open FroehlichSpencer.BKT.Rotator
open FroehlichSpencer.BKT.Rotator.TheoremC
open FroehlichSpencer.BKT.Villain
open FroehlichSpencer.BKT.Villain.TheoremC
open FroehlichSpencer.BKT.Generic
open FroehlichSpencer.BKT.Lattice2D

noncomputable section

namespace FroehlichSpencer.BKT.Villain.TheoremC

private theorem gaussianWeight_diffOn (b : ℝ) :
    DifferentiableOn ℂ (gaussianWeight b) Set.univ := by
  intro z hz
  unfold gaussianWeight
  fun_prop

private theorem gaussianWeight_iteratedDiffOn (b : ℝ) (n : ℕ) :
    DifferentiableOn ℂ (iteratedDeriv n (gaussianWeight b)) Set.univ := by
  induction n with
  | zero => simpa [iteratedDeriv_zero] using gaussianWeight_diffOn b
  | succ n ih =>
    rw [iteratedDeriv_succ]
    exact ih.deriv isOpen_univ

private theorem iteratedDeriv_gaussianWeight_real_eq_complex {b : ℝ} (n : ℕ) :
    iteratedDeriv n (fun x : ℝ => gaussianWeight b x) =
      fun x : ℝ => iteratedDeriv n (gaussianWeight b) (x : ℂ) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    have hd : DifferentiableAt ℂ (iteratedDeriv n (gaussianWeight b)) (x : ℂ) :=
      (gaussianWeight_iteratedDiffOn b n).differentiableAt
        (isOpen_univ.mem_nhds (Set.mem_univ _))
    have hreal := hd.hasDerivAt.comp_ofReal
    rw [iteratedDeriv_succ]
    exact hreal.deriv

private theorem gaussianWeight_deriv_decay {b : ℝ} (hb : 0 < b) (n k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ,
      |x| ^ k * ‖iteratedDeriv n (fun y : ℝ => gaussianWeight b y) x‖ ≤ C := by
  let C := (n.factorial : ℝ) * Real.exp (3 * b / 2 + (k : ℝ) ^ 2 / b)
  refine ⟨C, by positivity, fun x => ?_⟩
  let r : ℝ := 1
  have hr : 0 < r := by norm_num [r]
  have hclosed : DifferentiableOn ℂ (gaussianWeight b) (closedBall (x : ℂ) r) := by
    apply (gaussianWeight_diffOn b).mono
    intro z hz
    simp
  have hbound : ∀ z ∈ sphere (x : ℂ) r,
      ‖gaussianWeight b z‖ ≤ Real.exp (3 * b / 2) * Real.exp (-(b / 4) * x ^ 2) := by
    intro z hz
    have hdist : ‖z - (x : ℂ)‖ = r := (mem_sphere_iff_norm).mp hz
    have him : |z.im| ≤ r := by
      have h := Complex.abs_im_le_norm (z - (x : ℂ))
      rw [Complex.sub_im, Complex.ofReal_im, sub_zero, hdist] at h
      exact h
    have hre : |z.re - x| ≤ r := by
      have h := Complex.abs_re_le_norm (z - (x : ℂ))
      rw [hdist] at h
      exact h
    have hrepr : z = (z.re : ℂ) + z.im * Complex.I := by
      apply Complex.ext <;> simp [mul_comm]
    rw [hrepr, norm_gaussianWeight]
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hre2 : x ^ 2 - 2 * |x| ≤ z.re ^ 2 := by
      have hsq := sq_nonneg (z.re - x)
      have hcross : -2 * |x| ≤ 2 * x * (z.re - x) := by
        have hmul : |x * (z.re - x)| ≤ |x| * r := by
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left hre (abs_nonneg x)
        have hlow : -|x * (z.re - x)| ≤ x * (z.re - x) := neg_abs_le _
        nlinarith
      nlinarith [sq_nonneg (z.re - x)]
    have him' : |z.im| ≤ 1 := by simpa [r] using him
    have him2 : z.im ^ 2 ≤ 1 := by
      calc
        z.im ^ 2 = |z.im| ^ 2 := (sq_abs _).symm
        _ ≤ 1 := by
          have hmul := mul_le_mul_of_nonneg_right him' (abs_nonneg z.im)
          nlinarith
    have hquad : x ^ 2 - 2 * |x| - 1 ≤ z.re ^ 2 - z.im ^ 2 := by linarith
    have habs : |x| ≤ x ^ 2 / 4 + 1 := by
      nlinarith [sq_nonneg (|x| - 2), sq_abs x]
    have hcoeff : 0 ≤ b / 2 := by positivity
    have hexp : -(b / 2) * (z.re ^ 2 - z.im ^ 2) ≤
        3 * b / 2 - (b / 4) * x ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hquad hcoeff,
        mul_le_mul_of_nonneg_left habs (by positivity : 0 ≤ b)]
    linarith [hexp]
  have hderiv := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hr
    ((hclosed.mono closure_ball_subset_closedBall).diffContOnCl) hbound
  have hderiv' : ‖iteratedDeriv n (gaussianWeight b) (x : ℂ)‖ ≤
      (n.factorial : ℝ) * Real.exp (3 * b / 2) * Real.exp (-(b / 4) * x ^ 2) := by
    simpa [r, mul_assoc, mul_left_comm, mul_comm] using hderiv
  have hderivReal : ‖iteratedDeriv n (fun y : ℝ => gaussianWeight b y) x‖ ≤
      (n.factorial : ℝ) * Real.exp (3 * b / 2) * Real.exp (-(b / 4) * x ^ 2) := by
    rw [iteratedDeriv_gaussianWeight_real_eq_complex n]
    exact hderiv'
  have hpow : |x| ^ k ≤ Real.exp ((k : ℝ) * |x|) := by
    have hex : |x| ≤ Real.exp |x| := by
      have h := Real.add_one_le_exp |x|
      linarith
    calc
      |x| ^ k ≤ (Real.exp |x|) ^ k := by gcongr
      _ = Real.exp ((k : ℝ) * |x|) := by rw [← Real.exp_nat_mul]
  have hpar : (k : ℝ) * |x| - (b / 4) * x ^ 2 ≤ (k : ℝ) ^ 2 / b := by
    have hid : (k : ℝ) ^ 2 -
        (((k : ℝ) * |x| - (b / 4) * x ^ 2) * b) =
        ((k : ℝ) - b * |x| / 2) ^ 2 := by
      rw [← sq_abs x]
      ring
    rw [le_div_iff₀ hb]
    nlinarith [hid, sq_nonneg ((k : ℝ) - b * |x| / 2)]
  have hgauss : |x| ^ k * Real.exp (-(b / 4) * x ^ 2) ≤
      Real.exp ((k : ℝ) ^ 2 / b) := by
    calc
      |x| ^ k * Real.exp (-(b / 4) * x ^ 2) ≤
          Real.exp ((k : ℝ) * |x|) * Real.exp (-(b / 4) * x ^ 2) :=
        mul_le_mul_of_nonneg_right hpow (Real.exp_nonneg _)
      _ = Real.exp ((k : ℝ) * |x| - (b / 4) * x ^ 2) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp ((k : ℝ) ^ 2 / b) := Real.exp_le_exp.mpr hpar
  calc
    |x| ^ k * ‖iteratedDeriv n (fun y : ℝ => gaussianWeight b y) x‖ ≤
        |x| ^ k * ((n.factorial : ℝ) * Real.exp (3 * b / 2) *
          Real.exp (-(b / 4) * x ^ 2)) :=
          mul_le_mul_of_nonneg_left hderivReal (by positivity)
    _ = (n.factorial : ℝ) * Real.exp (3 * b / 2) *
        (|x| ^ k * Real.exp (-(b / 4) * x ^ 2)) := by ring
    _ ≤ (n.factorial : ℝ) * Real.exp (3 * b / 2) *
        Real.exp ((k : ℝ) ^ 2 / b) :=
          mul_le_mul_of_nonneg_left hgauss (by positivity)
    _ = (n.factorial : ℝ) * Real.exp (3 * b / 2 + (k : ℝ) ^ 2 / b) := by
      calc
        _ = (n.factorial : ℝ) *
            (Real.exp (3 * b / 2) * Real.exp ((k : ℝ) ^ 2 / b)) := by ring
        _ = _ := by rw [← Real.exp_add]

/-- The real Gaussian weight is a Schwartz function. -/
def gaussianWeightRealSchwartz (b : ℝ) (hb : 0 < b) : 𝓢(ℝ, ℂ) where
  toFun := fun x => gaussianWeight b x
  smooth' := by
    unfold gaussianWeight
    have hcast : ContDiff ℝ ⊤ (fun x : ℝ => (x : ℂ)) := Complex.ofRealCLM.contDiff
    have harg : ContDiff ℝ ⊤
        (fun x : ℝ => -((b / 2 : ℝ) : ℂ) * (x : ℂ) ^ 2) :=
      contDiff_const.mul (hcast.pow 2)
    have harg' : ContDiff ℝ (↑(⊤ : ℕ∞))
        (fun x : ℝ => -((b / 2 : ℝ) : ℂ) * (x : ℂ) ^ 2) :=
      harg.of_le (by simp)
    exact Complex.contDiff_exp.comp harg'
  decay' k n := by
    obtain ⟨C, hC, hbound⟩ := gaussianWeight_deriv_decay hb n k
    refine ⟨C, fun x => ?_⟩
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
    exact hbound x

/-- The marked real Gaussian density in the pinned dual-face coordinates. -/
def villainPinnedGaussianDensityCoords (L : ℕ) (β : ℝ)
    (j : RotatorInternalBond L → ℤ) (x : SquareFreeVertex L → ℝ) : ℂ :=
  ∏ e : RotatorInternalBond L,
    gaussianWeight β⁻¹
      (((rotatorCoordsGradientLinearMap L x e + (j e : ℝ) : ℝ) : ℂ))

/-- The box-comb pairing of the marked pinned Gaussian density. -/
def villainPinnedGaussianCombCutoffPairing (L : ℕ) (β : ℝ)
    (j : RotatorInternalBond L → ℤ) (N : ℕ) : ℂ :=
  ∫ x : SquareFreeVertex L → ℝ,
    faceCombCutoff (ι := SquareFreeVertex L) N x *
      villainPinnedGaussianDensityCoords L β j x

/-- The pinned Gaussian density with an arbitrary integer source current is Schwartz. -/
theorem exists_villainPinnedGaussianDensityCoords_schwartz {L : ℕ} {β : ℝ}
    (hβ : 0 < β) (j : RotatorInternalBond L → ℤ) :
    ∃ f : 𝓢(SquareFreeVertex L → ℝ, ℂ),
      ∀ x, f x = villainPinnedGaussianDensityCoords L β j x := by
  classical
  let scalar := gaussianWeightRealSchwartz β⁻¹ (inv_pos.mpr hβ)
  obtain ⟨edgeProduct, hedgeProduct⟩ :=
    exists_schwartz_pi_product (ι := RotatorInternalBond L) scalar
  let jR : RotatorInternalBond L → ℝ := fun e => (j e : ℝ)
  let shifted : 𝓢(RotatorInternalBond L → ℝ, ℂ) :=
    SchwartzMap.compSubConstCLM ℂ (-jR) edgeProduct
  let grad : (SquareFreeVertex L → ℝ) →L[ℝ] (RotatorInternalBond L → ℝ) :=
    (rotatorCoordsGradientLinearMap L).toContinuousLinearMap
  obtain ⟨K, -, hanti⟩ :=
    (rotatorCoordsGradientLinearMap L).injective_iff_antilipschitz.mp
      (rotatorCoordsGradientLinearMap_injective L)
  have hanti' : AntilipschitzWith K grad := by
    change AntilipschitzWith K (rotatorCoordsGradientLinearMap L)
    exact hanti
  let f : 𝓢(SquareFreeVertex L → ℝ, ℂ) :=
    (SchwartzMap.compCLMOfAntilipschitz ℂ grad.hasTemperateGrowth hanti') shifted
  refine ⟨f, fun x => ?_⟩
  have hcomp : f x = shifted (grad x) := by
    change ((SchwartzMap.compCLMOfAntilipschitz ℂ grad.hasTemperateGrowth hanti')
      shifted) x = shifted (grad x)
    simp only [SchwartzMap.compCLMOfAntilipschitz_apply, Function.comp_apply]
  have hshift : shifted (grad x) = edgeProduct (grad x - -jR) :=
    SchwartzMap.compSubConstCLM_apply edgeProduct (-jR) (grad x)
  rw [hcomp, hshift, hedgeProduct]
  unfold villainPinnedGaussianDensityCoords
  refine Finset.prod_congr rfl fun e _ => ?_
  change gaussianWeight β⁻¹ (((grad x - -jR) e : ℝ) : ℂ) = _
  rw [Pi.sub_apply, Pi.neg_apply, sub_neg_eq_add]
  rfl

/-- The pinned Gaussian density is integrable in every finite box. -/
theorem integrable_villainPinnedGaussianDensityCoords {L : ℕ} {β : ℝ}
    (hβ : 0 < β) (j : RotatorInternalBond L → ℤ) :
    Integrable (villainPinnedGaussianDensityCoords L β j) := by
  obtain ⟨f, hf⟩ := exists_villainPinnedGaussianDensityCoords_schwartz hβ j
  refine (integrable_schwartz_pi f).congr ?_
  filter_upwards [] with x
  exact hf x

/-- The Fourier coefficients of the marked pinned Gaussian density are summable. -/
theorem summable_villainPinnedGaussianDensityCoords_fourier {L : ℕ} {β : ℝ}
    (hβ : 0 < β) (j : RotatorInternalBond L → ℤ) :
    Summable (faceFourierCoefficient (villainPinnedGaussianDensityCoords L β j)) := by
  classical
  obtain ⟨f, hf⟩ := exists_villainPinnedGaussianDensityCoords_schwartz hβ j
  refine (summable_faceFourierCoefficient_of_schwartz f).congr fun q => ?_
  unfold faceFourierCoefficient
  apply integral_congr_ae
  filter_upwards [] with x
  rw [hf]

/-- At integer coordinates the Gaussian density is the marked Villain height weight. -/
theorem villainPinnedGaussianDensityCoords_height {L : ℕ} {β : ℝ} (hβ : 0 < β)
    (j : RotatorInternalBond L → ℤ) (h : RotatorFaceHeight L) :
    villainPinnedGaussianDensityCoords L β j
        (fun v => (rotatorFaceHeightCoords h v : ℝ)) =
      gaussianVillainMarkedHeightWeight L β j h := by
  have hfield (p : RotatorDualFace L) :
      rotatorPinnedCoordsField (fun v => (rotatorFaceHeightCoords h v : ℝ)) p =
        (h.1 p : ℝ) := by
    cases p with
    | none => simp [rotatorPinnedCoordsField, rotatorFaceHeightCoords, h.2]
    | some v => rfl
  unfold villainPinnedGaussianDensityCoords gaussianVillainMarkedHeightWeight

  simp only [rotatorCoordsGradientLinearMap, LinearMap.coe_mk, AddHom.coe_mk]
  simp_rw [hfield]
  have hprod : ∏ e : RotatorInternalBond L,
      gaussianWeight β⁻¹
        (((h.1 ((rotatorDualGraph L).src e) : ℝ) -
          (h.1 ((rotatorDualGraph L).tgt e) : ℝ) + (j e : ℝ) : ℝ) : ℂ) =
      ((currentGaussianWeight β (fun e => rotatorFaceHeightCurrent h e + j e) : ℝ) : ℂ) := by
    unfold currentGaussianWeight
    rw [Complex.ofReal_prod]
    apply Finset.prod_congr rfl
    intro e he
    rw [gaussianWeight_ofReal]
    have hcurrent : (rotatorFaceHeightCurrent h e : ℝ) =
        (h.1 ((rotatorDualGraph L).src e) : ℝ) -
          (h.1 ((rotatorDualGraph L).tgt e) : ℝ) := by
      simp [rotatorFaceHeightCurrent, Int.cast_sub]
    have hInv : β⁻¹ / 2 = 1 / (2 * β) := by field_simp
    have hExp : -(β⁻¹ / 2) *
          ((h.1 ((rotatorDualGraph L).src e) : ℝ) -
            (h.1 ((rotatorDualGraph L).tgt e) : ℝ) + (j e : ℝ)) ^ 2 =
        -((rotatorFaceHeightCurrent h e + j e : ℤ) : ℝ) ^ 2 / (2 * β) := by
      rw [← hcurrent, hInv]
      push_cast
      ring
    exact congrArg Complex.ofReal (congrArg Real.exp hExp)
  exact hprod

/-- Multidimensional Poisson summation identifies the Fourier-coefficient sum with the marked
zero-exterior Gaussian height partition sum. -/
theorem villainPinnedGaussianDensityCoords_fourierSum_eq_heightMarkedFactor
    {L : ℕ} {β : ℝ} (hβ : 0 < β) (j : RotatorInternalBond L → ℤ) :
    (∑' q : FaceFrequency (SquareFreeVertex L),
      faceFourierCoefficient (villainPinnedGaussianDensityCoords L β j) q) =
      ∑' h : RotatorFaceHeight L, (gaussianVillainMarkedHeightWeight L β j h : ℂ) := by
  classical
  let ι := SquareFreeVertex L
  obtain ⟨f, hf⟩ := exists_villainPinnedGaussianDensityCoords_schwartz hβ j
  have hcoeff (q : FaceFrequency ι) :
      faceFourierCoefficient (villainPinnedGaussianDensityCoords L β j) q =
        multiEuclideanFourierCoefficient f (faceFrequencyEquiv ι q) := by
    rw [faceFourierCoefficient_eq_multiEuclideanFourierCoefficient
      (villainPinnedGaussianDensityCoords L β j) q]
    rw [show faceFrequencyEquiv ι q = (fun i => q i (Finset.mem_univ i)) by rfl]
    unfold multiEuclideanFourierCoefficient
    apply integral_congr_ae
    filter_upwards [] with x
    rw [hf]
  have hcoeffSum :
      (∑' q : FaceFrequency ι,
        faceFourierCoefficient (villainPinnedGaussianDensityCoords L β j) q) =
        ∑' q : ι → ℤ, multiEuclideanFourierCoefficient f q := by
    calc
      _ = ∑' q : FaceFrequency ι,
            multiEuclideanFourierCoefficient f (faceFrequencyEquiv ι q) := by
          apply tsum_congr
          exact hcoeff
      _ = ∑' q : ι → ℤ, multiEuclideanFourierCoefficient f q :=
        (faceFrequencyEquiv ι).tsum_eq (multiEuclideanFourierCoefficient f)
  have hpoisson := poissonSummation_schwartz_pi_unconditional f
  have hsample :
      (∑' z : ι → ℤ,
        villainPinnedGaussianDensityCoords L β j (fun i => (z i : ℝ))) =
        ∑' h : RotatorFaceHeight L, (gaussianVillainMarkedHeightWeight L β j h : ℂ) := by
    calc
      _ = ∑' h : RotatorFaceHeight L,
            villainPinnedGaussianDensityCoords L β j
              (fun v => (rotatorFaceHeightCoords h v : ℝ)) := by
          symm
          exact (rotatorFaceHeightCoordsEquiv (L := L)).tsum_eq
            (fun q : SquareFreeVertex L → ℤ =>
              villainPinnedGaussianDensityCoords L β j (fun v => (q v : ℝ)))
      _ = _ := by
        apply tsum_congr
        intro h
        exact villainPinnedGaussianDensityCoords_height hβ j h
  calc
    _ = ∑' q : ι → ℤ, multiEuclideanFourierCoefficient f q := hcoeffSum
    _ = ∑' z : ι → ℤ, f (fun i => (z i : ℝ)) := hpoisson
    _ = ∑' z : ι → ℤ,
          villainPinnedGaussianDensityCoords L β j (fun i => (z i : ℝ)) := by
          apply tsum_congr
          intro z
          exact hf (fun i => (z i : ℝ))
    _ = ∑' h : RotatorFaceHeight L,
          (gaussianVillainMarkedHeightWeight L β j h : ℂ) := hsample

/-- The marked Dirichlet-comb pairings converge to the marked pinned Gaussian height sum. -/
theorem villainPinnedGaussianCombCutoffPairing_tendsto {L : ℕ} {β : ℝ}
    (hβ : 0 < β) (j : RotatorInternalBond L → ℤ) :
    Tendsto (fun N : ℕ => villainPinnedGaussianCombCutoffPairing L β j N) atTop
      (𝓝 (∑' h : RotatorFaceHeight L, (gaussianVillainMarkedHeightWeight L β j h : ℂ))) := by
  have hcut := faceCombCutoffPairing_tendsto_fourier
    (integrable_villainPinnedGaussianDensityCoords hβ j)
    (summable_villainPinnedGaussianDensityCoords_fourier hβ j)
  rw [villainPinnedGaussianDensityCoords_fourierSum_eq_heightMarkedFactor hβ j] at hcut
  exact hcut

/-- The unmarked Gaussian Dirichlet-comb pairings converge to the pinned Gaussian partition sum. -/
  theorem villainPinnedGaussianCombCutoffPairing_tendsto_unmarked {L : ℕ} {β : ℝ}
    (hβ : 0 < β) :
    Tendsto (fun N : ℕ => villainPinnedGaussianCombCutoffPairing L β (fun _ => 0) N) atTop
      (𝓝 (∑' h : RotatorFaceHeight L, (gaussianVillainHeightWeight L β h : ℂ))) := by
  have hsum : (∑' h : RotatorFaceHeight L,
        (gaussianVillainHeightWeight L β h : ℂ)) =
      ∑' h : RotatorFaceHeight L,
        (gaussianVillainMarkedHeightWeight L β (fun _ => 0) h : ℂ) := by
    apply tsum_congr
    intro h
    simp [gaussianVillainMarkedHeightWeight, gaussianVillainHeightWeight,
      currentGaussianWeight]
  rw [hsum]
  exact villainPinnedGaussianCombCutoffPairing_tendsto hβ (fun _ => 0)

end FroehlichSpencer.BKT.Villain.TheoremC

end
