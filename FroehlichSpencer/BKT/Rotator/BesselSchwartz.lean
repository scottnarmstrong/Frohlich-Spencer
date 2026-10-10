/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.BKT.Rotator.Contour.StripBounds
public import FroehlichSpencer.BKT.Rotator.IntegerComb
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

/-!
# Schwartz decay of the interpolated Bessel weight

The uniform strip estimate from `Contour.StripBounds` and Cauchy's derivative estimate show that
all real derivatives of `besselInterp β` decay exponentially. Exponential decay absorbs every
polynomial weight, producing an actual Schwartz representative on the real axis.
-/

@[expose] public section

noncomputable section

open Complex Metric Set Filter Topology
open scoped Real SchwartzMap ContDiff
open FroehlichSpencer.BKT.Rotator.BesselInterp

namespace FroehlichSpencer.BKT.Rotator

/-- Restriction of the Appendix-B interpolation to the real axis. -/
def besselInterpReal (β : ℝ) (x : ℝ) : ℂ := besselInterp β x

private lemma besselInterp_diffOn_strip {β : ℝ} (hβ : 0 < β) :
    DifferentiableOn ℂ (besselInterp β) {z : ℂ | |z.im| < β} := by
  intro z hz
  exact (Contour.differentiableAt_besselInterp hβ hz).differentiableWithinAt

private lemma besselInterp_iteratedDiffOn_strip {β : ℝ} (hβ : 0 < β) (n : ℕ) :
    DifferentiableOn ℂ (iteratedDeriv n (besselInterp β)) {z : ℂ | |z.im| < β} := by
  induction n with
  | zero => simpa [iteratedDeriv_zero] using besselInterp_diffOn_strip hβ
  | succ n ih =>
    rw [iteratedDeriv_succ]
    exact ih.deriv (BesselInterp.isOpen_strip β)

private theorem iteratedDeriv_real_eq_complex {β : ℝ} (hβ : 0 < β) (n : ℕ) :
    iteratedDeriv n (besselInterpReal β) = fun x : ℝ => iteratedDeriv n (besselInterp β) x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    have hx : |((x : ℂ)).im| < β := by simpa using hβ
    have hd : DifferentiableAt ℂ (iteratedDeriv n (besselInterp β)) (x : ℂ) :=
      (besselInterp_iteratedDiffOn_strip hβ n).differentiableAt
        ((BesselInterp.isOpen_strip β).mem_nhds hx)
    have hreal := hd.hasDerivAt.comp_ofReal
    rw [iteratedDeriv_succ]
    exact hreal.deriv

/-- All complex-order derivatives on the real axis inherit an exponential bound from the strip.
The radius is `β/4`, so each Cauchy circle stays inside `|Im z| ≤ β/2`. -/
theorem exists_besselInterp_iteratedDeriv_exp_bound {β : ℝ} (hβ : 1 ≤ β) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ,
      ‖iteratedDeriv n (besselInterp β) (x : ℂ)‖ ≤
        n.factorial * (C * Real.exp (β / 4) * Real.exp (-|x|)) / (β / 4) ^ n := by
  obtain ⟨C, hC0, hC⟩ := Contour.exists_norm_besselInterp_strip_le hβ
  refine ⟨C, hC0, fun x => ?_⟩
  let r : ℝ := β / 4
  have hr : 0 < r := by dsimp [r]; linarith
  have hrhalf : r ≤ β / 2 := by dsimp [r]; linarith
  have hclosed : DifferentiableOn ℂ (besselInterp β) (closedBall (x : ℂ) r) := by
    apply (besselInterp_diffOn_strip (by linarith : 0 < β)).mono
    intro z hz
    have him : |z.im| ≤ r := by
      have hnorm := Complex.abs_im_le_norm (z - (x : ℂ))
      have hdist : ‖z - (x : ℂ)‖ ≤ r := by
        simpa [mem_closedBall, dist_eq_norm] using hz
      rw [Complex.sub_im, Complex.ofReal_im, sub_zero] at hnorm
      exact hnorm.trans hdist
    exact lt_of_le_of_lt him (by linarith)
  have hbound : ∀ z ∈ sphere (x : ℂ) r,
      ‖besselInterp β z‖ ≤ C * Real.exp r * Real.exp (-|x|) := by
    intro z hz
    have hzdist : ‖z - (x : ℂ)‖ = r := (mem_sphere_iff_norm).mp hz
    have him : |z.im| ≤ r := by
      have hnorm := Complex.abs_im_le_norm (z - (x : ℂ))
      rw [Complex.sub_im, Complex.ofReal_im, sub_zero, hzdist] at hnorm
      exact hnorm
    have hre : |z.re - x| ≤ r := by
      have hnorm := Complex.abs_re_le_norm (z - (x : ℂ))
      rw [hzdist] at hnorm
      exact hnorm
    have hrepr : z = (z.re : ℂ) + z.im * Complex.I := by
      apply Complex.ext <;> simp [mul_comm]
    rw [hrepr]
    calc
      ‖besselInterp β ((z.re : ℂ) + z.im * Complex.I)‖ ≤ C * Real.exp (-|z.re|) := by
        simpa [Complex.add_im, Complex.mul_im] using hC z.re z.im (him.trans hrhalf)
      _ ≤ C * (Real.exp r * Real.exp (-|x|)) := by
        apply mul_le_mul_of_nonneg_left _ hC0
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have hx' : |x| ≤ |z.re| + r := by
          calc |x| = |(x - z.re) + z.re| := by congr 1; ring
            _ ≤ |x - z.re| + |z.re| := abs_add_le _ _
            _ = |z.re - x| + |z.re| := by rw [abs_sub_comm]
            _ ≤ r + |z.re| := add_le_add hre le_rfl
            _ = |z.re| + r := by ring
        linarith
      _ = C * Real.exp r * Real.exp (-|x|) := by ring
  have hcauchy := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hr
    ((hclosed.mono closure_ball_subset_closedBall).diffContOnCl) hbound
  simpa [r, mul_assoc, mul_left_comm, mul_comm] using hcauchy

/-- A polynomial times an exponential tail has an explicit global bound. -/
private lemma abs_pow_mul_exp_neg_abs_le (k : ℕ) (x : ℝ) :
    |x| ^ k * Real.exp (-|x|) ≤ ((k : ℝ) + 1) ^ k := by
  let u := |x|
  let K := (k : ℝ) + 1
  have hK : 0 < K := by dsimp [K]; positivity
  have hu : 0 ≤ u := abs_nonneg x
  by_cases hsmall : u ≤ K
  · calc
      u ^ k * Real.exp (-u) ≤ K ^ k * 1 := by
        apply mul_le_mul
        · exact pow_le_pow_left₀ hu hsmall _
        · simpa using (Real.exp_le_exp.mpr (neg_nonpos.mpr hu))
        · positivity
        · positivity
      _ = K ^ k := by ring
  · have hlarge : K ≤ u := le_of_not_ge hsmall
    let y := u / K
    have hy : 1 ≤ y := (one_le_div hK).2 hlarge
    have hy0 : 0 ≤ y := le_trans zero_le_one hy
    have hyexp : y ≤ Real.exp y := by
      have h := Real.add_one_le_exp y
      linarith
    have hpow : y ^ (k + 1) ≤ Real.exp y ^ (k + 1) := by gcongr
    have huEq : u = K * y := by dsimp [y]; field_simp
    have hexpEq : Real.exp u = Real.exp y ^ (k + 1) := by
      rw [huEq, show K = ((k + 1 : ℕ) : ℝ) by simp [K]]
      exact Real.exp_nat_mul y (k + 1)
    have hyk : y ^ k ≤ Real.exp y ^ (k + 1) := by
      calc y ^ k ≤ y ^ (k + 1) := by
            rw [pow_succ]
            exact le_mul_of_one_le_right (by positivity) hy
        _ ≤ Real.exp y ^ (k + 1) := hpow
    have hbase : u ^ k ≤ K ^ k * Real.exp u := by
      calc
        u ^ k = K ^ k * y ^ k := by rw [huEq, mul_pow]
        _ ≤ K ^ k * Real.exp y ^ (k + 1) := mul_le_mul_of_nonneg_left hyk (by positivity)
        _ = K ^ k * Real.exp u := by rw [hexpEq]
    have hpositive : 0 < Real.exp u := Real.exp_pos _
    calc
      u ^ k * Real.exp (-u) = u ^ k / Real.exp u := by rw [Real.exp_neg]; simp [div_eq_mul_inv]
      _ ≤ K ^ k := (div_le_iff₀ hpositive).2 hbase

/-- The real restriction of `besselInterp β` is a Schwartz function for `β ≥ 1`. -/
def besselInterpRealSchwartz (β : ℝ) (hβ : 1 ≤ β) : 𝓢(ℝ, ℂ) where
  toFun := besselInterpReal β
  smooth' := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    have hβ0 : 0 < β := by linarith
    have hanalytic := BesselInterp.analyticAt_besselInterp hβ0
      (show |((x : ℂ)).im| ≤ β / 2 by simp; linarith)
    have hcomplex : ContDiffAt ℝ ⊤ (besselInterp β) (x : ℂ) :=
      hanalytic.contDiffAt.restrict_scalars ℝ
    have hreal := hcomplex.comp x Complex.ofRealCLM.contDiff.contDiffAt
    change ContDiffAt ℝ ∞ (besselInterp β ∘ Complex.ofReal) x
    exact hreal.of_le le_top
  decay' k n := by
    obtain ⟨C, hC0, hC⟩ := exists_besselInterp_iteratedDeriv_exp_bound hβ n
    let D : ℝ := n.factorial * (C * Real.exp (β / 4)) / (β / 4) ^ n
    have hD : 0 ≤ D := by
      dsimp [D]
      positivity
    refine ⟨D * (((k : ℝ) + 1) ^ k), fun x => ?_⟩
    have hderiv : ‖iteratedDeriv n (besselInterpReal β) x‖ ≤
        D * Real.exp (-|x|) := by
      rw [iteratedDeriv_real_eq_complex (by linarith : 0 < β) n]
      specialize hC x
      dsimp [D]
      calc
        ‖iteratedDeriv n (besselInterp β) (x : ℂ)‖ ≤
            n.factorial * (C * Real.exp (β / 4) * Real.exp (-|x|)) / (β / 4) ^ n := hC
        _ = (n.factorial * (C * Real.exp (β / 4)) / (β / 4) ^ n) * Real.exp (-|x|) := by ring
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    have hweight : ‖x‖ = |x| := Real.norm_eq_abs x
    rw [hweight]
    calc
      |x| ^ k * ‖iteratedDeriv n (besselInterpReal β) x‖ ≤
          |x| ^ k * (D * Real.exp (-|x|)) := mul_le_mul_of_nonneg_left hderiv (by positivity)
      _ = D * (|x| ^ k * Real.exp (-|x|)) := by ring
      _ ≤ D * (((k : ℝ) + 1) ^ k) :=
          mul_le_mul_of_nonneg_left (abs_pow_mul_exp_neg_abs_le k x) hD

private def schwartzSquare (f : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (f : ℝ → ℂ) f

private theorem schwartzSquare_apply (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    schwartzSquare f x = f x ^ 2 := by
  simp [schwartzSquare, SchwartzMap.smulLeftCLM_apply_apply, f.hasTemperateGrowth,
    smul_eq_mul, pow_two]

private theorem rotatorOneFacePinnedDensity_eq_fourthPower (β x : ℝ) (hβ : 0 < β) :
    rotatorOneFacePinnedDensity β x = besselInterp β x ^ 4 := by
  classical
  unfold rotatorOneFacePinnedDensity
  calc
    (∏ e : RotatorInternalBond 1,
        besselInterp β ((rotatorOneFaceRealField x ((rotatorDualGraph 1).src e) -
          rotatorOneFaceRealField x ((rotatorDualGraph 1).tgt e) : ℝ) : ℂ)) =
      ∏ _e : RotatorInternalBond 1, besselInterp β x := by
        apply Finset.prod_congr rfl
        intro e he
        fin_cases e <;> simp [rotatorOneFaceRealField, rotatorDualGraph,
          Duality.wiredBoxGraph, Duality.wiredBoxSrc, Duality.wiredBoxTgt,
          Duality.horizontalPrimalSrc, Duality.horizontalPrimalTgt,
          Duality.verticalPrimalSrc, Duality.verticalPrimalTgt,
          Duality.horizontalFaceX, Duality.verticalFaceY]
        all_goals
          first
          | rfl
          | rw [← Complex.ofReal_neg]
            exact besselInterp_neg_ofReal hβ x
    _ = besselInterp β x ^ 4 := by
      simp [RotatorInternalBond, FroehlichSpencer.BKT.Lattice2D.SquareFreeEdge,
        FroehlichSpencer.BKT.Lattice2D.SquareFreeHorizontalEdge,
        FroehlichSpencer.BKT.Lattice2D.SquareFreeVerticalEdge]

/-- The one-face pinned density has an actual Schwartz representative for `β ≥ 1`. -/
theorem exists_rotatorOneFacePinnedDensity_schwartz {β : ℝ} (hβ : 1 ≤ β) :
    ∃ f : 𝓢(ℝ, ℂ), ∀ x, f x = rotatorOneFacePinnedDensity β x := by
  let f : 𝓢(ℝ, ℂ) := besselInterpRealSchwartz β hβ
  let f₂ : 𝓢(ℝ, ℂ) := schwartzSquare f
  let f₄ : 𝓢(ℝ, ℂ) := schwartzSquare f₂
  refine ⟨f₄, fun x => ?_⟩
  calc
    f₄ x = (besselInterp β x) ^ 4 := by
      calc
        f₄ x = (f₂ x) ^ 2 := schwartzSquare_apply f₂ x
        _ = (f x) ^ 4 := by rw [schwartzSquare_apply]; ring
        _ = (besselInterp β x) ^ 4 := by change (besselInterp β x) ^ 4 = _; rfl
    _ = rotatorOneFacePinnedDensity β x :=
      (rotatorOneFacePinnedDensity_eq_fourthPower β x (by linarith)).symm

/-- The actual one-face finite-cutoff pairings converge to the zero-exterior height partition
factor. This instantiates the cutoff theorem with the Schwartz representative proved above. -/
theorem rotatorOneFaceCombCutoffPairing_tendsto_actual {β : ℝ} (hβ : 1 ≤ β) :
    Tendsto (fun N : ℕ => rotatorOneFaceCombCutoffPairing β N) atTop
      (𝓝 (rotatorHeightPartitionFactor 1 β)) := by
  obtain ⟨f, hf⟩ := exists_rotatorOneFacePinnedDensity_schwartz hβ
  exact rotatorOneFaceCombCutoffPairing_tendsto β (by linarith) f hf

end FroehlichSpencer.BKT.Rotator

end
