/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.SOS.Roughening.Weight
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

/-!
# The tilted SOS edge factor is Schwartz (the dipole tilt construction)

The comb identification of the tilted SOS sums (FS81 (7.16), (7.20)) goes through the Poisson
summation of a Schwartz density. Its edge factors are the tilted Appendix C weights
`x ↦ e^{cx} I_β(x)` (`sosTiltFactor`), `|c| ≤ β/2`.

* `exists_schwartz_of_strip`: a function holomorphic on an open strip `|Im z| < R₀` and bounded by
  `K e^{−η|Re z|}` on a closed substrip `|Im z| ≤ r` restricts to a Schwartz function on the real
  line (Cauchy's estimate on circles of radius `r`, as `Rotator.besselInterpRealSchwartz`);
* `exists_sosTiltFactor_schwartz`: `e^{cx} I_β(x)` is Schwartz for `0 < β ≤ 1`, `|c| ≤ β/2`, since
  `I_β` is holomorphic on `|Im z| < β^{−1/3}` and `|I_β(t + iu)| ≤ K e^{−β|t|}` on FS81's strip
  (`exists_norm_sosInterp_strip_le_exp`).
-/

@[expose] public section

noncomputable section

namespace FroehlichSpencer.BKT.SOS.Roughening

open Complex Metric Set Filter Topology
open scoped Real SchwartzMap ContDiff

/-- `|x|^k e^{−η|x|} ≤ η^{−k}(k+1)^k`. -/
theorem abs_pow_mul_exp_neg_mul_abs_le (k : ℕ) {η : ℝ} (hη : 0 < η) (x : ℝ) :
    |x| ^ k * Real.exp (-(η * |x|)) ≤ (η ^ k)⁻¹ * ((k : ℝ) + 1) ^ k := by
  set y := η * |x| with hy
  have hy0 : 0 ≤ y := by positivity
  have hxy : |x| = y / η := by rw [hy]; field_simp
  have hbase : y ^ k * Real.exp (-y) ≤ ((k : ℝ) + 1) ^ k := by
    set K := (k : ℝ) + 1
    have hK : 0 < K := by positivity
    by_cases hsmall : y ≤ K
    · calc y ^ k * Real.exp (-y) ≤ K ^ k * 1 := by
            apply mul_le_mul (pow_le_pow_left₀ hy0 hsmall _)
              (by simpa using Real.exp_le_exp.mpr (neg_nonpos.mpr hy0)) (by positivity)
              (by positivity)
        _ = K ^ k := mul_one _
    · have hlarge : K ≤ y := le_of_not_ge hsmall
      set s := y / K with hs
      have hs1 : 1 ≤ s := (one_le_div hK).2 hlarge
      have hsexp : s ≤ Real.exp s := by linarith [Real.add_one_le_exp s]
      have hyEq : y = K * s := by rw [hs]; field_simp
      have hexpEq : Real.exp y = Real.exp s ^ (k + 1) := by
        rw [hyEq, show K = ((k + 1 : ℕ) : ℝ) by simp [K]]
        exact Real.exp_nat_mul s (k + 1)
      have hsk : s ^ k ≤ Real.exp s ^ (k + 1) := by
        calc s ^ k ≤ s ^ (k + 1) := by
              rw [pow_succ]; exact le_mul_of_one_le_right (by positivity) hs1
          _ ≤ Real.exp s ^ (k + 1) := pow_le_pow_left₀ (by positivity) hsexp _
      have hb : y ^ k ≤ K ^ k * Real.exp y := by
        calc y ^ k = K ^ k * s ^ k := by rw [hyEq, mul_pow]
          _ ≤ K ^ k * Real.exp s ^ (k + 1) := mul_le_mul_of_nonneg_left hsk (by positivity)
          _ = K ^ k * Real.exp y := by rw [hexpEq]
      rw [Real.exp_neg, ← div_eq_mul_inv]
      exact (div_le_iff₀ (Real.exp_pos _)).2 hb
  rw [hxy, div_pow, div_eq_mul_inv, mul_comm (y ^ k), mul_assoc]
  exact mul_le_mul_of_nonneg_left hbase (by positivity)

/-- **Strip-holomorphic functions with exponential decay are Schwartz on the real line.** -/
theorem exists_schwartz_of_strip {F : ℂ → ℂ} {R₀ r η K : ℝ} (hr : 0 < r) (hrR : r < R₀)
    (hη : 0 < η) (hd : ∀ z : ℂ, |z.im| < R₀ → DifferentiableAt ℂ F z)
    (hb : ∀ t u : ℝ, |u| ≤ r → ‖F ((t : ℂ) + (u : ℂ) * I)‖ ≤ K * Real.exp (-(η * |t|))) :
    ∃ f : 𝓢(ℝ, ℂ), ∀ x : ℝ, f x = F x := by
  set U : Set ℂ := {z : ℂ | |z.im| < R₀} with hU
  have hUopen : IsOpen U := isOpen_lt (continuous_abs.comp continuous_im) continuous_const
  have hdiffU : DifferentiableOn ℂ F U := fun z hz => (hd z hz).differentiableWithinAt
  have hiterU : ∀ n : ℕ, DifferentiableOn ℂ (iteratedDeriv n F) U := by
    intro n
    induction n with
    | zero => simpa [iteratedDeriv_zero] using hdiffU
    | succ n ih =>
      rw [iteratedDeriv_succ]
      exact ih.deriv hUopen
  have hmemU : ∀ x : ℝ, (x : ℂ) ∈ U := fun x => by
    simp only [hU, Set.mem_ofPred_eq, ofReal_im, abs_zero]; linarith
  have hreal : ∀ n : ℕ, iteratedDeriv n (fun x : ℝ => F x) = fun x : ℝ => iteratedDeriv n F x := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [iteratedDeriv_succ, ih]
      funext x
      have hdx : DifferentiableAt ℂ (iteratedDeriv n F) (x : ℂ) :=
        (hiterU n).differentiableAt (hUopen.mem_nhds (hmemU x))
      rw [iteratedDeriv_succ]
      exact hdx.hasDerivAt.comp_ofReal.deriv
  -- the Cauchy estimate
  have hK0 : 0 ≤ K := by
    have h := hb 0 0 (by rw [abs_zero]; exact hr.le)
    have h1 : 0 ≤ K * Real.exp (-(η * |(0 : ℝ)|)) := (norm_nonneg _).trans h
    simpa using h1
  have hcauchy : ∀ (n : ℕ) (x : ℝ), ‖iteratedDeriv n F (x : ℂ)‖ ≤
      n.factorial * (K * Real.exp (η * r) * Real.exp (-(η * |x|))) / r ^ n := by
    intro n x
    have hclosed : DifferentiableOn ℂ F (closedBall (x : ℂ) r) := by
      refine hdiffU.mono fun z hz => ?_
      have him : |z.im| ≤ r := by
        have hnorm := Complex.abs_im_le_norm (z - (x : ℂ))
        have hdist : ‖z - (x : ℂ)‖ ≤ r := by
          simpa [mem_closedBall, dist_eq_norm] using hz
        rw [Complex.sub_im, Complex.ofReal_im, sub_zero] at hnorm
        exact hnorm.trans hdist
      show |z.im| < R₀
      linarith
    have hbound : ∀ z ∈ sphere (x : ℂ) r,
        ‖F z‖ ≤ K * Real.exp (η * r) * Real.exp (-(η * |x|)) := by
      intro z hz
      have hzdist : ‖z - (x : ℂ)‖ = r := (mem_sphere_iff_norm).mp hz
      have him : |z.im| ≤ r := by
        have hnorm := Complex.abs_im_le_norm (z - (x : ℂ))
        rw [Complex.sub_im, Complex.ofReal_im, sub_zero, hzdist] at hnorm
        exact hnorm
      have hre : |z.re - x| ≤ r := by
        have hnorm := Complex.abs_re_le_norm (z - (x : ℂ))
        rw [hzdist] at hnorm
        simpa using hnorm
      have hrepr : z = (z.re : ℂ) + (z.im : ℂ) * I := (Complex.re_add_im z).symm
      rw [hrepr]
      calc ‖F ((z.re : ℂ) + (z.im : ℂ) * I)‖ ≤ K * Real.exp (-(η * |z.re|)) := hb _ _ him
        _ ≤ K * (Real.exp (η * r) * Real.exp (-(η * |x|))) := by
          apply mul_le_mul_of_nonneg_left _ hK0
          rw [← Real.exp_add]
          apply Real.exp_le_exp.mpr
          have hx' : |x| ≤ |z.re| + r := by
            calc |x| = |(x - z.re) + z.re| := by congr 1; ring
              _ ≤ |x - z.re| + |z.re| := abs_add_le _ _
              _ = |z.re - x| + |z.re| := by rw [abs_sub_comm]
              _ ≤ r + |z.re| := add_le_add hre le_rfl
              _ = |z.re| + r := by ring
          nlinarith
        _ = K * Real.exp (η * r) * Real.exp (-(η * |x|)) := by ring
    exact Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hr
      ((hclosed.mono closure_ball_subset_closedBall).diffContOnCl) hbound
  refine ⟨{
    toFun := fun x : ℝ => F x
    smooth' := ?_
    decay' := ?_ }, fun x => rfl⟩
  · apply contDiff_iff_contDiffAt.mpr
    intro x
    have hanalytic : AnalyticAt ℂ F (x : ℂ) :=
      hdiffU.analyticAt (hUopen.mem_nhds (hmemU x))
    have hcomplex : ContDiffAt ℝ ⊤ F (x : ℂ) := hanalytic.contDiffAt.restrict_scalars ℝ
    have hreal' := hcomplex.comp x Complex.ofRealCLM.contDiff.contDiffAt
    change ContDiffAt ℝ ∞ (F ∘ Complex.ofReal) x
    exact hreal'.of_le le_top
  · intro k n
    set D : ℝ := n.factorial * (K * Real.exp (η * r)) / r ^ n with hD
    have hD0 : 0 ≤ D := by rw [hD]; positivity
    refine ⟨D * ((η ^ k)⁻¹ * ((k : ℝ) + 1) ^ k), fun x => ?_⟩
    have hderiv : ‖iteratedDeriv n (fun x : ℝ => F x) x‖ ≤ D * Real.exp (-(η * |x|)) := by
      rw [hreal n]
      calc ‖iteratedDeriv n F (x : ℂ)‖
          ≤ n.factorial * (K * Real.exp (η * r) * Real.exp (-(η * |x|))) / r ^ n := hcauchy n x
        _ = D * Real.exp (-(η * |x|)) := by rw [hD]; ring
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
    calc |x| ^ k * ‖iteratedDeriv n (fun x : ℝ => F x) x‖
        ≤ |x| ^ k * (D * Real.exp (-(η * |x|))) :=
          mul_le_mul_of_nonneg_left hderiv (by positivity)
      _ = D * (|x| ^ k * Real.exp (-(η * |x|))) := by ring
      _ ≤ D * ((η ^ k)⁻¹ * ((k : ℝ) + 1) ^ k) :=
          mul_le_mul_of_nonneg_left (abs_pow_mul_exp_neg_mul_abs_le k hη x) hD0

/-! ## The tilted SOS edge factor -/

/-- The tilted Appendix C weight `z ↦ e^{cz} I_β(z)`. -/
def sosTiltFactor (β c : ℝ) (z : ℂ) : ℂ := Complex.exp ((c : ℂ) * z) * Interp.sosInterp β z

/-- **The tilted SOS edge factor is Schwartz** for `0 < β ≤ 1` and `|c| ≤ β/2`. -/
theorem exists_sosTiltFactor_schwartz {β c : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) (hc : |c| ≤ β / 2) :
    ∃ f : 𝓢(ℝ, ℂ), ∀ x : ℝ, f x = sosTiltFactor β c x := by
  obtain ⟨K, hK0, hK⟩ := exists_norm_sosInterp_strip_le_exp hβ hβ1
  have hp : 0 < β ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hβ _
  have hR₀ : 0 < β ^ (-(1 / 3 : ℝ)) := Real.rpow_pos_of_pos hβ _
  have hcancel : β ^ (1 / 3 : ℝ) * β ^ (-(1 / 3 : ℝ)) = 1 := by
    rw [Real.rpow_neg hβ.le]
    exact mul_inv_cancel₀ hp.ne'
  refine exists_schwartz_of_strip (R₀ := β ^ (-(1 / 3 : ℝ))) (r := (1 / 2 : ℝ) * β ^ (-(1 / 3 : ℝ)))
    (η := β / 2) (K := K) (by positivity) (by linarith) (by positivity) (fun z hz => ?_)
    (fun t u hu => ?_)
  · have hz' : β ^ (1 / 3 : ℝ) * |z.im| < 1 := by
      calc β ^ (1 / 3 : ℝ) * |z.im| < β ^ (1 / 3 : ℝ) * β ^ (-(1 / 3 : ℝ)) :=
            mul_lt_mul_of_pos_left hz hp
        _ = 1 := hcancel
    exact ((Complex.differentiable_exp.comp (differentiable_id.const_mul (c : ℂ))).differentiableAt).mul
      (Interp.hasDerivAt_sosInterp hβ.le hz').differentiableAt
  · unfold sosTiltFactor
    rw [norm_mul, Complex.norm_exp]
    have hre : ((c : ℂ) * ((t : ℂ) + (u : ℂ) * I)).re = c * t := by
      simp only [mul_re, ofReal_re, ofReal_im, add_re, add_im, mul_im, I_re, I_im]
      ring
    rw [hre]
    have hct : c * t ≤ β / 2 * |t| :=
      (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_mul_of_nonneg_right hc (abs_nonneg _))
    calc Real.exp (c * t) * ‖Interp.sosInterp β ((t : ℂ) + (u : ℂ) * I)‖
        ≤ Real.exp (β / 2 * |t|) * (K * Real.exp (-(β * |t|))) :=
          mul_le_mul (Real.exp_le_exp.mpr hct) (hK t u hu) (norm_nonneg _) (Real.exp_pos _).le
      _ = K * Real.exp (-(β / 2 * |t|)) := by
          rw [mul_left_comm, ← Real.exp_add]
          congr 2
          ring

end FroehlichSpencer.BKT.SOS.Roughening

end
