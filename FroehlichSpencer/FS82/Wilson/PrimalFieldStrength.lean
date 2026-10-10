/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Wilson.DualityFinite
import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# The Villain field-strength insertion

The source observable is the logarithmic derivative of the periodized
Gaussian.  This file proves its exact character-series insertion, including
the sign fixed by the `exp(-i m x)` Fourier convention.
-/

@[expose] public section

open Complex
open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Poisson
open MeasureTheory

local instance : Fact (0 < (1 : ℝ)) := ⟨one_pos⟩
noncomputable local instance : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
noncomputable local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
noncomputable local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace FroehlichSpencer.FS82.Wilson

private theorem nat_le_sq (n : ℕ) : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
  cases n with
  | zero => norm_num
  | succ n =>
      have hn : (1 : ℝ) ≤ (Nat.succ n : ℝ) := by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
      nlinarith

private theorem villainCoeff_firstMoment_summable (β : ℝ) (hβ : 0 < β) :
    Summable fun k : ℤ => |(k : ℝ)| * villainGaussianCoeff β k := by
  let c := 1 / (2 * β)
  have hc : 0 < c := by dsimp [c]; positivity
  have hcoeff (k : ℤ) : villainGaussianCoeff β k =
      Real.exp (-c * (k : ℝ) ^ 2) := by
    rw [villainGaussianCoeff]
    congr 1
    dsimp [c]
    field_simp
  have hnat : Summable fun n : ℕ =>
      (n : ℝ) * Real.exp (-c * (n : ℝ)) := by
    simpa [pow_one] using Real.summable_pow_mul_exp_neg_nat_mul 1 hc
  apply (summable_int_iff_summable_nat_and_neg).2
  constructor
  · apply Summable.of_nonneg_of_le (fun n => by
      rw [hcoeff]
      positivity) ?_ hnat
    intro n
    have hn : (n : ℝ) ≤ (n : ℝ) ^ 2 := nat_le_sq n
    have he : Real.exp (-c * (n : ℝ) ^ 2) ≤ Real.exp (-c * (n : ℝ)) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left hn hc.le]
    have hn0 : 0 ≤ (n : ℝ) := by positivity
    rw [hcoeff]
    simp only [Int.cast_natCast, abs_of_nonneg hn0]
    exact mul_le_mul_of_nonneg_left he hn0

  · apply Summable.of_nonneg_of_le (fun n => by
      rw [hcoeff]
      positivity) ?_ hnat
    intro n
    have hn : (n : ℝ) ≤ (n : ℝ) ^ 2 := nat_le_sq n
    have he : Real.exp (-c * (n : ℝ) ^ 2) ≤ Real.exp (-c * (n : ℝ)) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left hn hc.le]
    have hn0 : 0 ≤ (n : ℝ) := by positivity
    rw [hcoeff]
    simp only [Int.cast_neg, Int.cast_natCast, neg_sq, abs_neg,
      abs_of_nonneg hn0]
    exact mul_le_mul_of_nonneg_left he hn0


private def primalFinIntEquiv (n : ℕ) :
    (Fin (n + 1) → ℤ) ≃ ℤ × (Fin n → ℤ) where
  toFun f := (f 0, fun i => f i.succ)
  invFun p := Fin.cases p.1 p.2
  left_inv f := by
    funext i
    refine Fin.cases ?_ ?_ i <;> simp
  right_inv p := by
    rcases p with ⟨z, f⟩
    rfl

private theorem primalProductTsumFinBounded (n : ℕ) (g : ℤ → ℝ)
    (hg : Summable g) (hg0 : ∀ k, 0 ≤ g k)
    (phase : Fin n → ℤ → ℂ)
    (hphase : ∀ i k, ‖phase i k‖ ≤ 1) :
    (∏ i : Fin n, ∑' k : ℤ, (g k : ℂ) * phase i k) =
      ∑' f : Fin n → ℤ,
        ∏ i : Fin n, (g (f i) : ℂ) * phase i (f i) := by
  classical
  induction n with
  | zero => simp
  | succ n ih =>
      let F : (Fin (n + 1) → ℤ) → ℂ := fun f =>
        ∏ i : Fin (n + 1), (g (f i) : ℂ) * phase i (f i)
      let R : (Fin n → ℤ) → ℂ := fun f =>
        ∏ i : Fin n, (g (f i) : ℂ) * phase i.succ (f i)
      let A : ℤ → ℂ := fun k => (g k : ℂ) * phase 0 k
      have hcoeff : Summable fun f : Fin (n + 1) → ℤ => ∏ i, g (f i) :=
        FroehlichSpencer.FS82.Poisson.summable_pi_prod_of_summable g hg
      have hF : Summable F := by
        apply Summable.of_norm_bounded hcoeff
        intro f
        dsimp [F]
        rw [norm_prod]
        apply Finset.prod_le_prod₀
        · intro i hi
          exact norm_nonneg _
        · intro i hi
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (hg0 (f i))]
          calc
            (g (f i)) * ‖phase i (f i)‖ ≤ g (f i) * 1 :=
              mul_le_mul_of_nonneg_left (hphase i (f i)) (hg0 (f i))
            _ = g (f i) := mul_one _
      let e := primalFinIntEquiv n
      have hcomp : Summable (F ∘ e.symm) :=
        (Equiv.summable_iff (f := F) e.symm).2 hF
      have hrewrite (p : ℤ × (Fin n → ℤ)) : F (e.symm p) = A p.1 * R p.2 := by
        rcases p with ⟨k, f⟩
        change (∏ i : Fin (n + 1),
          (g ((e.symm (k, f)) i) : ℂ) * phase i ((e.symm (k, f)) i)) =
            ((g k : ℂ) * phase 0 k) *
              ∏ i : Fin n, (g (f i) : ℂ) * phase i.succ (f i)
        rw [show e.symm (k, f) = Fin.cases k f by rfl]
        simp only [Fin.prod_univ_succ, Fin.cases_zero, Fin.cases_succ]
      have hcomp' : Summable (fun p : ℤ × (Fin n → ℤ) => A p.1 * R p.2) :=
        hcomp.congr fun p => hrewrite p
      have hprod : (∑' f : Fin (n + 1) → ℤ, F f) =
          ∑' p : ℤ × (Fin n → ℤ), A p.1 * R p.2 := by
        calc
          _ = ∑' p : ℤ × (Fin n → ℤ), F (e.symm p) := (Equiv.tsum_eq e.symm F).symm
          _ = _ := tsum_congr hrewrite
      have hiter : (∑' p : ℤ × (Fin n → ℤ), A p.1 * R p.2) =
          ∑' k : ℤ, ∑' f : Fin n → ℤ, A k * R f := hcomp'.tsum_prod
      have hinner (k : ℤ) :
          (∑' f : Fin n → ℤ, A k * R f) =
            A k * ∏ i : Fin n, ∑' z : ℤ, (g z : ℂ) * phase i.succ z := by
        rw [tsum_mul_left]
        dsimp [A, R]
        rw [ih (fun i z => phase i.succ z) (fun i z => hphase i.succ z)]
      rw [Fin.prod_univ_succ]
      calc
        (∑' k : ℤ, (g k : ℂ) * phase 0 k) *
            ∏ i : Fin n, ∑' k : ℤ, (g k : ℂ) * phase i.succ k =
          ∑' k : ℤ, A k * ∏ i : Fin n, ∑' z : ℤ, (g z : ℂ) * phase i.succ z := by
            rw [← tsum_mul_right]
        _ = ∑' k : ℤ, ∑' f : Fin n → ℤ, A k * R f := by
            apply tsum_congr
            intro k
            exact (hinner k).symm
        _ = ∑' p : ℤ × (Fin n → ℤ), A p.1 * R p.2 := hiter.symm
        _ = ∑' f : Fin (n + 1) → ℤ, F f := hprod.symm

private theorem primalProductTsumFintypeBounded {ι : Type*} [Fintype ι]
    (g : ℤ → ℝ) (hg : Summable g) (hg0 : ∀ k, 0 ≤ g k)
    (phase : ι → ℤ → ℂ) (hphase : ∀ i k, ‖phase i k‖ ≤ 1) :
    (∏ i : ι, ∑' k : ℤ, (g k : ℂ) * phase i k) =
      ∑' f : ι → ℤ,
        ∏ i : ι, (g (f i) : ℂ) * phase i (f i) := by
  classical
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let eπ : (ι → ℤ) ≃ (Fin (Fintype.card ι) → ℤ) :=
    Equiv.piCongrLeft (fun _ : Fin (Fintype.card ι) => ℤ) e
  have hfin := primalProductTsumFinBounded (Fintype.card ι) g hg hg0
    (fun i k => phase (e.symm i) k) (fun i k => hphase (e.symm i) k)
  calc
    (∏ i : ι, ∑' k : ℤ, (g k : ℂ) * phase i k) =
        ∏ i : Fin (Fintype.card ι), ∑' k : ℤ, (g k : ℂ) * phase (e.symm i) k := by
          symm
          exact Equiv.prod_comp e.symm (fun i => ∑' k : ℤ, (g k : ℂ) * phase i k)
    _ = ∑' f : Fin (Fintype.card ι) → ℤ,
          ∏ i : Fin (Fintype.card ι), (g (f i) : ℂ) * phase (e.symm i) (f i) := hfin
    _ = ∑' f : ι → ℤ, ∏ i : ι, (g (f i) : ℂ) * phase i (f i) := by
          let H : (ι → ℤ) → ℂ := fun f =>
            ∏ i : ι, (g (f i) : ℂ) * phase i (f i)
          have hsum := Equiv.tsum_eq eπ.symm H
          rw [← hsum]
          apply tsum_congr
          intro f
          dsimp [H, eπ]
          rw [← Equiv.prod_comp e (fun j : Fin (Fintype.card ι) =>
            (g (f j) : ℂ) * phase (e.symm j) (f j))]
          apply Finset.prod_congr rfl
          intro i hi
          simp [Equiv.piCongrLeft]

private noncomputable def villainCosineTerm (β : ℝ)
    (k : ℤ) (x : ℝ) : ℝ :=
  villainGaussianCoeff β k * Real.cos ((k : ℝ) * x)

noncomputable def villainCosineTermDeriv (β : ℝ)
    (k : ℤ) (x : ℝ) : ℝ :=
  villainGaussianCoeff β k * (-(k : ℝ) * Real.sin ((k : ℝ) * x))

private theorem villainCosineTerm_hasDerivAt (β : ℝ)
    (k : ℤ) (x : ℝ) :
    HasDerivAt (villainCosineTerm β k)
      (villainCosineTermDeriv β k x) x := by
  have harg : HasDerivAt (fun y : ℝ => (k : ℝ) * y) (k : ℝ) x := by
    simpa [mul_comm] using (hasDerivAt_id x).const_mul (k : ℝ)
  have hcos := (Real.hasDerivAt_cos ((k : ℝ) * x)).comp x harg
  convert hcos.const_mul (villainGaussianCoeff β k) using 1
  · funext y
    simp [villainCosineTerm, mul_comm]
  · simp [villainCosineTermDeriv, mul_comm, mul_assoc]

private theorem villainCosineTermDeriv_norm_bound (β : ℝ)
    (k : ℤ) (x : ℝ) :
    ‖villainCosineTermDeriv β k x‖ ≤
      |(k : ℝ)| * villainGaussianCoeff β k := by
  rw [villainCosineTermDeriv, Real.norm_eq_abs]
  have hcoeff : 0 ≤ villainGaussianCoeff β k := by
    rw [villainGaussianCoeff]
    positivity
  calc
    |villainGaussianCoeff β k * (-(k : ℝ) * Real.sin ((k : ℝ) * x))| =
        villainGaussianCoeff β k * (|(k : ℝ)| * |Real.sin ((k : ℝ) * x)|) := by
          rw [abs_mul, abs_of_nonneg hcoeff, abs_mul, abs_neg]
    _ ≤ villainGaussianCoeff β k * (|(k : ℝ)| * 1) := by
          gcongr
          exact Real.abs_sin_le_one _
    _ = |(k : ℝ)| * villainGaussianCoeff β k := by ring

/-- The real derivative of the periodized Villain density in the physical
angle variable. -/
theorem villainWeight_hasDerivAt_fourier (β x : ℝ) (hβ : 0 < β) :
    HasDerivAt (villainWeight β)
      ((1 / Real.sqrt (2 * Real.pi * β)) *
        ∑' k : ℤ, villainCosineTermDeriv β k x) x := by
  let u : ℤ → ℝ := fun k => |(k : ℝ)| * villainGaussianCoeff β k
  have hu : Summable u := villainCoeff_firstMoment_summable β hβ
  have htermSummable : Summable fun k : ℤ => villainCosineTerm β k 0 := by
    refine (villainCharacterCoeff_summable β hβ).congr ?_
    intro k
    simp [villainCosineTerm, villainGaussianCoeff, Real.cos_zero]
  have hsumDeriv := hasDerivAt_tsum hu
    (fun k y => villainCosineTerm_hasDerivAt β k y)
    (fun k y => villainCosineTermDeriv_norm_bound β k y)
    htermSummable x
  have hscale := HasDerivAt.const_mul
    (1 / Real.sqrt (2 * Real.pi * β)) hsumDeriv
  have hEq : villainWeight β =ᶠ[nhds x]
      fun y => (1 / Real.sqrt (2 * Real.pi * β)) *
        ∑' k : ℤ, villainCosineTerm β k y := by
    filter_upwards [] with y
    rw [villainWeight_eq_fourierCosineSum β y hβ]
    simp [villainCosineTerm, villainGaussianCoeff]
  exact hscale.congr_of_eventuallyEq hEq

public noncomputable def villainComplexCharacterTerm (β : ℝ)
    (k : ℤ) (x : ℝ) : ℂ :=
  (villainGaussianCoeff β k : ℂ) *
    Complex.exp (-Complex.I * (k : ℝ) * (x : ℂ))

public noncomputable def villainComplexCharacterTermDeriv (β : ℝ)
    (k : ℤ) (x : ℝ) : ℂ :=
  villainComplexCharacterTerm β k x * (-Complex.I * (k : ℝ))

private theorem villainComplexCharacterTerm_hasDerivAt (β : ℝ)
    (k : ℤ) (x : ℝ) :
    HasDerivAt (villainComplexCharacterTerm β k)
      (villainComplexCharacterTermDeriv β k x) x := by
  have harg : HasDerivAt
      (fun y : ℝ => (-Complex.I * (k : ℝ)) * (y : ℂ))
      (-Complex.I * (k : ℝ)) x := by
    simpa only [Complex.ofRealCLM_apply, ofReal_one, mul_one] using
      (Complex.ofRealCLM.hasDerivAt).const_mul
        (-Complex.I * (k : ℝ))
  have hexp := (Complex.hasDerivAt_exp
      (-Complex.I * (k : ℝ) * (x : ℂ))).comp x harg
  convert HasDerivAt.const_mul
      (villainGaussianCoeff β k : ℂ) hexp using 1
  · funext y
    simp only [villainComplexCharacterTerm]
    congr 2
  · simp only [villainComplexCharacterTermDeriv, villainComplexCharacterTerm]
    ring

private theorem villainComplexCharacterTermDeriv_norm_bound
    (β : ℝ) (k : ℤ) (x : ℝ) :
    ‖villainComplexCharacterTermDeriv β k x‖ ≤
      |(k : ℝ)| * villainGaussianCoeff β k := by
  have hc : 0 ≤ villainGaussianCoeff β k := by
    rw [villainGaussianCoeff]
    positivity
  rw [villainComplexCharacterTermDeriv, villainComplexCharacterTerm,
    norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hc, Complex.norm_exp]
  have hreal : ( -Complex.I * (k : ℝ) * (x : ℂ)).re = 0 := by
    simp
  rw [hreal, Real.exp_zero]
  simp [Complex.norm_I, mul_comm]


/-- The source field-strength numerator `-i φ′`, with its exact character
series.  Division by the positive Villain weight gives the observable in
(2.89).  The coefficient is `-m` for the convention `exp(-i m x)`. -/
noncomputable def villainFieldStrengthNumerator (β x : ℝ) : ℂ :=
  (-Complex.I) * ((deriv (villainWeight β) x : ℝ) : ℂ)

theorem villainFieldStrengthNumerator_eq_fourier (β x : ℝ)
    (hβ : 0 < β) :
    villainFieldStrengthNumerator β x =
      (villainFourierScale β : ℂ) *
        ∑' k : ℤ,
          ((-(k : ℝ) : ℂ) * (villainGaussianCoeff β k : ℂ)) *
            Complex.exp (-Complex.I * (k : ℝ) * (x : ℂ)) := by
  let u : ℤ → ℝ := fun k => |(k : ℝ)| * villainGaussianCoeff β k
  have hu : Summable u := villainCoeff_firstMoment_summable β hβ
  have htermSummable : Summable fun k : ℤ => villainComplexCharacterTerm β k 0 := by
    apply Summable.of_norm_bounded (villainCharacterCoeff_summable β hβ)
    intro k
    have hc : 0 ≤ villainGaussianCoeff β k := by
      rw [villainGaussianCoeff]
      positivity
    have hnorm : ‖villainComplexCharacterTerm β k 0‖ =
        villainGaussianCoeff β k := by
      rw [villainComplexCharacterTerm, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg hc, Complex.norm_exp]
      simp
    rw [hnorm]
    exact le_rfl
  have hseries := hasDerivAt_tsum hu
    (fun k y => villainComplexCharacterTerm_hasDerivAt β k y)
    (fun k y => villainComplexCharacterTermDeriv_norm_bound β k y)
    htermSummable x
  have hscale := HasDerivAt.const_mul (villainFourierScale β) hseries
  have hEq : (fun y : ℝ => (villainWeight β y : ℂ)) =ᶠ[nhds x]
      fun y => (villainFourierScale β : ℂ) *
        ∑' k : ℤ, villainComplexCharacterTerm β k y := by
    filter_upwards [] with y
    rw [villainWeight_eq_complexCharacterSum β y hβ]
    simp [villainFourierScale, villainComplexCharacterTerm,
      villainGaussianCoeff]
  have hderiv := hscale.congr_of_eventuallyEq hEq
  have hrealCast := (villainWeight_hasDerivAt_fourier β x hβ).ofReal_comp
  have hderivValue := hrealCast.unique hderiv
  have hrealDeriv := (villainWeight_hasDerivAt_fourier β x hβ).deriv
  have hmul : (-Complex.I) *
      ((deriv (villainWeight β) x : ℝ) : ℂ) =
        (villainFourierScale β : ℂ) *
          ∑' k : ℤ,
            (-Complex.I) * villainComplexCharacterTermDeriv β k x := by
    calc
      _ = (-Complex.I) *
          ((deriv (villainWeight β) x : ℝ) : ℂ) := by rfl
      _ = (-Complex.I) *
          (((1 / Real.sqrt (2 * Real.pi * β)) *
            ∑' k : ℤ, villainCosineTermDeriv β k x : ℝ) : ℂ) := by
              exact congrArg (fun z : ℝ =>
                (-Complex.I) * (z : ℂ)) hrealDeriv
      _ = (-Complex.I) *
          ((villainFourierScale β : ℂ) *
            ∑' k : ℤ, villainComplexCharacterTermDeriv β k x) := by
              exact congrArg (fun z : ℂ => (-Complex.I) * z) hderivValue
      _ = (villainFourierScale β : ℂ) *
          ((-Complex.I) *
            ∑' k : ℤ, villainComplexCharacterTermDeriv β k x) := by ring
      _ = _ := by rw [← tsum_mul_left]
  rw [villainFieldStrengthNumerator, hmul]
  apply congrArg (fun z : ℂ => (villainFourierScale β : ℂ) * z)
  apply tsum_congr
  intro k
  simp only [villainComplexCharacterTermDeriv, villainComplexCharacterTerm]
  push_cast
  have hfreq : (-Complex.I) * (-Complex.I * ((k : ℝ) : ℂ)) =
      -((k : ℝ) : ℂ) := by
    calc
      (-Complex.I) * (-Complex.I * ((k : ℝ) : ℂ)) =
          (Complex.I ^ 2) * ((k : ℝ) : ℂ) := by ring
      _ = -((k : ℝ) : ℂ) := by rw [Complex.I_sq]; ring
  calc
    -Complex.I *
        ((villainGaussianCoeff β k : ℂ) *
          Complex.exp (-Complex.I * (k : ℝ) * (x : ℂ)) *
          (-Complex.I * (k : ℝ))) =
      ((-(k : ℝ) : ℂ) * (villainGaussianCoeff β k : ℂ)) *
        Complex.exp (-Complex.I * (k : ℝ) * (x : ℂ)) := by
          calc
            _ = (villainGaussianCoeff β k : ℂ) *
                Complex.exp (-Complex.I * (k : ℝ) * (x : ℂ)) *
                ((-Complex.I) * (-Complex.I * ((k : ℝ) : ℂ))) := by ring
            _ = (villainGaussianCoeff β k : ℂ) *
                Complex.exp (-Complex.I * (k : ℝ) * (x : ℂ)) *
                (-((k : ℝ) : ℂ)) := by rw [hfreq]
            _ = _ := by ring


/-- The field strength on the real representative line. -/
noncomputable def villainFieldStrengthRepresentative (β x : ℝ) : ℂ :=
  villainFieldStrengthNumerator β x / (villainWeight β x : ℂ)


/-- The differentiated Fourier terms converge in the continuous-map norm. -/
private theorem villainCircleFieldStrengthMapTerms_summable
    (β : ℝ) (hβ : 0 < β) :
    Summable fun k : ℤ =>
      ((-(k : ℝ) : ℂ) * (villainGaussianCoeff β k : ℂ)) •
        fourier (T := (1 : ℝ)) (-k) := by
  apply Summable.of_norm_bounded (villainCoeff_firstMoment_summable β hβ)
  intro k
  have hc : 0 ≤ villainGaussianCoeff β k := by
    rw [villainGaussianCoeff]
    positivity
  rw [norm_smul, Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hc, fourier_norm]
  simp

/-- The field-strength numerator as a continuous-circle Fourier series. -/
noncomputable def villainCircleFieldStrengthNumeratorMap
    (β : ℝ) : C(UnitAddCircle, ℂ) :=
  (villainFourierScale β : ℂ) •
    ∑' k : ℤ,
      ((-(k : ℝ) : ℂ) * (villainGaussianCoeff β k : ℂ)) •
        fourier (T := (1 : ℝ)) (-k)


noncomputable def villainCircleFieldStrengthNumerator
    (β : ℝ) (z : UnitAddCircle) : ℂ :=
  villainCircleFieldStrengthNumeratorMap β z

theorem villainCircleFieldStrengthNumerator_apply (β : ℝ)
    (z : UnitAddCircle) (hβ : 0 < β) :
    villainCircleFieldStrengthNumerator β z =
      (villainFourierScale β : ℂ) *
        ∑' k : ℤ,
          ((-(k : ℝ) : ℂ) * (villainGaussianCoeff β k : ℂ)) *
            fourier (T := (1 : ℝ)) (-k) z := by
  have hsum := ContinuousMap.tsum_apply
    (villainCircleFieldStrengthMapTerms_summable β hβ) z
  change (villainFourierScale β : ℂ) *
      (∑' k : ℤ,
        ((-(k : ℝ) : ℂ) * (villainGaussianCoeff β k : ℂ)) •
          fourier (T := (1 : ℝ)) (-k)) z = _
  rw [← hsum]
  apply congrArg (fun w : ℂ => (villainFourierScale β : ℂ) * w)
  apply tsum_congr
  intro k
  simp only [ContinuousMap.smul_apply, smul_eq_mul]


theorem villainCircleWeight_characterSeries (β : ℝ)
    (z : UnitAddCircle) (hβ : 0 < β) :
    (villainCircleWeight β z : ℂ) =
      (villainFourierScale β : ℂ) *
        ∑' k : ℤ, (villainGaussianCoeff β k : ℂ) *
          fourier (T := (1 : ℝ)) (-k) z := by
  have hterms : Summable fun k : ℤ =>
      (villainGaussianCoeff β k : ℂ) • fourier (T := (1 : ℝ)) (-k) := by
    apply Summable.of_norm_bounded (villainCharacterCoeff_summable β hβ)
    intro k
    have hc : 0 ≤ villainGaussianCoeff β k := by
      rw [villainGaussianCoeff]
      positivity
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hc, fourier_norm]
    simp [villainGaussianCoeff]
  have hsum := ContinuousMap.tsum_apply hterms z
  have hmap : villainCircleFourierMap β z =
      (villainFourierScale β : ℂ) *
        ∑' k : ℤ, (villainGaussianCoeff β k : ℂ) *
          fourier (T := (1 : ℝ)) (-k) z := by
    have hpois := villainWeight_eq_complexCharacterSum β
      (2 * Real.pi * circleRepresentative z) hβ
    have hchar (k : ℤ) :
        Complex.exp (-Complex.I * (k : ℝ) *
            ((2 * Real.pi * circleRepresentative z : ℝ) : ℂ)) =
          fourier (T := (1 : ℝ)) (-k) z := by
      have hrep : fourier (T := (1 : ℝ)) (-k) z =
          fourier (T := (1 : ℝ)) (-k) (circleRepresentative z : UnitAddCircle) :=
        congrArg (fun w : UnitAddCircle => fourier (T := (1 : ℝ)) (-k) w)
          (circleRepresentative_coe z).symm
      rw [hrep, fourier_coe_apply]
      apply congrArg Complex.exp
      push_cast
      ring
    calc
      villainCircleFourierMap β z =
          (villainWeight β (2 * Real.pi * circleRepresentative z) : ℂ) :=
            villainCircleFourierMap_apply β z hβ
      _ = (villainFourierScale β : ℂ) *
          ∑' k : ℤ, (villainGaussianCoeff β k : ℂ) *
            fourier (T := (1 : ℝ)) (-k) z := by
              rw [hpois]
              rw [show (1 / (Real.sqrt (2 * Real.pi * β) : ℝ) : ℂ) =
                villainFourierScale β by
                  unfold villainFourierScale
                  rw [Complex.ofReal_div]
                  simp]
              apply congrArg (fun w : ℂ => (villainFourierScale β : ℂ) * w)
              apply tsum_congr
              intro k
              simp only [villainGaussianCoeff]
              rw [hchar k]
  have hreal : (villainCircleWeight β z : ℂ) = villainCircleFourierMap β z := by
    rw [villainCircleWeight, villainCircleFourierMap_apply β z hβ]
    simp
  rw [hreal, hmap]

private noncomputable def villainInflatedGaussianCoeff
    (β : ℝ) (k : ℤ) : ℝ :=
  (1 + |(k : ℝ)|) * villainGaussianCoeff β k

private theorem villainInflatedGaussianCoeff_summable
    (β : ℝ) (hβ : 0 < β) :
    Summable (villainInflatedGaussianCoeff β) := by
  have hbase := villainCharacterCoeff_summable β hβ
  have hfirst := villainCoeff_firstMoment_summable β hβ
  have hEq : villainInflatedGaussianCoeff β =
      fun k => villainGaussianCoeff β k + |(k : ℝ)| * villainGaussianCoeff β k := by
    funext k
    dsimp [villainInflatedGaussianCoeff]
    ring
  rw [hEq]
  exact hbase.add hfirst

private theorem villainInflatedGaussianCoeff_nonneg
    (β : ℝ) (k : ℤ) : 0 ≤ villainInflatedGaussianCoeff β k := by
  rw [villainInflatedGaussianCoeff, villainGaussianCoeff]
  positivity


private noncomputable def villainInsertionMultiplier
    (insert : Bool) (k : ℤ) : ℝ :=
  if insert then -(k : ℝ) / (1 + |(k : ℝ)|)
    else 1 / (1 + |(k : ℝ)|)

private noncomputable def villainInsertionPhase (insert : Bool)
    (k : ℤ) (z : UnitAddCircle) : ℂ :=
  (villainInsertionMultiplier insert k : ℂ) *
    fourier (T := (1 : ℝ)) (-k) z

private theorem villainInsertionPhase_norm_le_one (insert : Bool)
    (k : ℤ) (z : UnitAddCircle) :
    ‖villainInsertionPhase insert k z‖ ≤ 1 := by
  have hd : 0 < 1 + |(k : ℝ)| := by positivity
  have hfourier : ‖fourier (T := (1 : ℝ)) (-k) z‖ = 1 := by
    simp [fourier_apply]
  rw [villainInsertionPhase, villainInsertionMultiplier]
  split_ifs
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_div, abs_neg, abs_of_pos hd, hfourier]
    have hle : |(k : ℝ)| ≤ 1 + |(k : ℝ)| := by
      nlinarith [abs_nonneg (k : ℝ)]
    simpa using (div_le_one_of_le₀ hle hd.le)
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 1),
      abs_of_pos hd, hfourier]
    have hle : (1 : ℝ) ≤ 1 + |(k : ℝ)| := by
      linarith [abs_nonneg (k : ℝ)]
    simpa using (div_le_one_of_le₀ hle hd.le)

private theorem villainInflatedCoeff_mul_insertionPhase
    (β : ℝ) (insert : Bool) (k : ℤ) (z : UnitAddCircle) :
    (villainInflatedGaussianCoeff β k : ℂ) * villainInsertionPhase insert k z =
      if insert then
        ((-(k : ℝ) : ℂ) * (villainGaussianCoeff β k : ℂ)) *
          fourier (T := (1 : ℝ)) (-k) z
      else
        (villainGaussianCoeff β k : ℂ) * fourier (T := (1 : ℝ)) (-k) z := by
  have hreal : villainInflatedGaussianCoeff β k *
      villainInsertionMultiplier insert k =
        if insert then -(k : ℝ) * villainGaussianCoeff β k
          else villainGaussianCoeff β k := by
    rw [villainInflatedGaussianCoeff, villainInsertionMultiplier]
    split_ifs <;> field_simp
  rw [villainInsertionPhase]
  calc
    (villainInflatedGaussianCoeff β k : ℂ) *
        ((villainInsertionMultiplier insert k : ℂ) *
          fourier (T := (1 : ℝ)) (-k) z) =
      ((villainInflatedGaussianCoeff β k *
        villainInsertionMultiplier insert k : ℝ) : ℂ) *
          fourier (T := (1 : ℝ)) (-k) z := by
            rw [Complex.ofReal_mul]
            ring
    _ = _ := by rw [hreal]; split_ifs <;> norm_cast

private theorem villainCircleInsertionExpansion
    (β : ℝ) (z : UnitAddCircle) (hβ : 0 < β) (insert : Bool) :
    (if insert then villainCircleFieldStrengthNumerator β z
      else (villainCircleWeight β z : ℂ)) =
      (villainFourierScale β : ℂ) *
        ∑' k : ℤ, (villainInflatedGaussianCoeff β k : ℂ) *
          villainInsertionPhase insert k z := by
  have hbase :
      (if insert then villainCircleFieldStrengthNumerator β z
        else (villainCircleWeight β z : ℂ)) =
        (villainFourierScale β : ℂ) *
          ∑' k : ℤ,
            (if insert then
              ((-(k : ℝ) : ℂ) * (villainGaussianCoeff β k : ℂ)) *
                fourier (T := (1 : ℝ)) (-k) z
            else
              (villainGaussianCoeff β k : ℂ) * fourier (T := (1 : ℝ)) (-k) z) := by
    by_cases hi : insert
    · simp [hi, villainCircleFieldStrengthNumerator_apply β z hβ]
    · simp [hi, villainCircleWeight_characterSeries β z hβ]
  rw [hbase]
  congr 1
  apply tsum_congr
  intro k
  rw [villainInflatedCoeff_mul_insertionPhase]


private theorem primal_prod_le_nonneg {ι : Type*} (s : Finset ι)
    (f g : ι → ℝ) (hf : ∀ i ∈ s, 0 ≤ f i) (hg : ∀ i ∈ s, 0 ≤ g i)
    (hle : ∀ i ∈ s, f i ≤ g i) : ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha]
      apply mul_le_mul
      · exact hle a (Finset.mem_insert_self _ _)
      · apply ih
        · intro i hi
          exact hf i (Finset.mem_insert_of_mem hi)
        · intro i hi
          exact hg i (Finset.mem_insert_of_mem hi)
        · intro i hi
          exact hle i (Finset.mem_insert_of_mem hi)
      · exact Finset.prod_nonneg fun i hi =>
          hf i (Finset.mem_insert_of_mem hi)
      · exact hg a (Finset.mem_insert_self _ _)

noncomputable def primalFieldStrengthInsertionFactor {B : Box 4}
    (β : ℝ) (θ : PrimalAngleConfig B)
    (p q r : PrimalPlaquettes B) : ℂ :=
  if r = p ∨ r = q then
    villainCircleFieldStrengthNumerator β (primalPlaquetteFlux θ r)
  else
    (villainCircleWeight β (primalPlaquetteFlux θ r) : ℂ)

noncomputable def primalFieldStrengthInsertionDensity {B : Box 4}
    (β : ℝ) (θ : PrimalAngleConfig B)
    (p q : PrimalPlaquettes B) : ℂ :=
  ∏ r : PrimalPlaquettes B, primalFieldStrengthInsertionFactor β θ p q r


/-- Character expansion with two distinct field-strength insertions. Each
insertion contributes `-m`; the two C4 orientation signs consequently cancel
in the two-point product. -/
theorem primalFieldStrengthInsertionDensity_eq_dualSeries {B : Box 4}
    (β : ℝ) (hβ : 0 < β) (θ : PrimalAngleConfig B)
    (p q : PrimalPlaquettes B) (hpq : p ≠ q) :
    primalFieldStrengthInsertionDensity β θ p q =
      villainFourierScale β ^ Fintype.card (PrimalPlaquettes B) *
        ∑' m : PrimalPlaquettes B → ℤ,
          ((m p : ℝ) * (m q : ℝ) : ℂ) * dualCharacterTerm β 0 m θ := by
  classical
  let gB : ℤ → ℝ := villainInflatedGaussianCoeff β
  let phase : PrimalPlaquettes B → ℤ → ℂ := fun r k =>
    villainInsertionPhase (r = p ∨ r = q) k (primalPlaquetteFlux θ r)
  have hgB : Summable gB := villainInflatedGaussianCoeff_summable β hβ
  have hgB0 : ∀ k, 0 ≤ gB k := villainInflatedGaussianCoeff_nonneg β
  have hphase : ∀ r k, ‖phase r k‖ ≤ 1 := by
    intro r k
    exact villainInsertionPhase_norm_le_one (r = p ∨ r = q) k
      (primalPlaquetteFlux θ r)
  have hlocal (r : PrimalPlaquettes B) :
      primalFieldStrengthInsertionFactor β θ p q r =
        (villainFourierScale β : ℂ) *
          ∑' k : ℤ, (gB k : ℂ) * phase r k := by
    dsimp [primalFieldStrengthInsertionFactor, phase, gB]
    by_cases hr : r = p ∨ r = q
    · simpa [hr] using villainCircleInsertionExpansion β
        (primalPlaquetteFlux θ r) hβ true
    · simpa [hr] using villainCircleInsertionExpansion β
        (primalPlaquetteFlux θ r) hβ false
  have hprod := primalProductTsumFintypeBounded
    (ι := PrimalPlaquettes B) gB hgB hgB0 phase hphase
  have hmode (m : PrimalPlaquettes B → ℤ) :
      (∏ r : PrimalPlaquettes B, (gB (m r) : ℂ) * phase r (m r)) =
        ((m p : ℝ) * (m q : ℝ) : ℂ) * dualCharacterTerm β 0 m θ := by
    let c : PrimalPlaquettes B → ℂ := fun r =>
      if r = p ∨ r = q then (-(m r : ℝ) : ℂ) else 1
    have hcoeff (r : PrimalPlaquettes B) :
        (gB (m r) : ℂ) * phase r (m r) =
          c r * ((villainGaussianCoeff β (m r) : ℂ) *
            fourier (T := (1 : ℝ)) (-m r) (primalPlaquetteFlux θ r)) := by
      change (villainInflatedGaussianCoeff β (m r) : ℂ) *
          villainInsertionPhase (decide (r = p ∨ r = q)) (m r)
            (primalPlaquetteFlux θ r) =
        (if r = p ∨ r = q then (-(m r : ℝ) : ℂ) else 1) * _
      have h := villainInflatedCoeff_mul_insertionPhase β
        (decide (r = p ∨ r = q)) (m r) (primalPlaquetteFlux θ r)
      by_cases hr : r = p ∨ r = q
      · simpa [hr, villainInsertionPhase, villainInsertionMultiplier,
          villainInflatedGaussianCoeff, villainGaussianCoeff, ← mul_assoc] using h
      · simpa [hr, villainInsertionPhase, villainInsertionMultiplier,
          villainInflatedGaussianCoeff, villainGaussianCoeff, ← mul_assoc] using h
    have hcprod : (∏ r : PrimalPlaquettes B, c r) =
        ((m p : ℝ) * (m q : ℝ) : ℂ) := by
      have hqmem : q ∈ (Finset.univ : Finset (PrimalPlaquettes B)).erase p := by
        exact Finset.mem_erase.mpr ⟨Ne.symm hpq, Finset.mem_univ q⟩
      have hcp : c p = (-(m p : ℝ) : ℂ) := by simp [c]
      have hcq : c q = (-(m q : ℝ) : ℂ) := by simp [c]
      have hrest : ∏ r ∈ (Finset.univ.erase p).erase q, c r = 1 := by
        apply Finset.prod_eq_one
        intro r hr
        rcases Finset.mem_erase.mp hr with ⟨hrq, hrpMem⟩
        rcases Finset.mem_erase.mp hrpMem with ⟨hrp, _⟩
        simp [c, hrp, hrq]
      calc
        ∏ r : PrimalPlaquettes B, c r =
            (∏ r ∈ (Finset.univ.erase p).erase q, c r) * c q * c p := by
          rw [← Finset.prod_erase_mul (Finset.univ : Finset (PrimalPlaquettes B))
            c (Finset.mem_univ p)]
          rw [← Finset.prod_erase_mul (Finset.univ.erase p) c hqmem]
        _ = ((m p : ℝ) * (m q : ℝ) : ℂ) := by
          rw [hrest, hcp, hcq]
          push_cast
          ring
    calc
      _ = (∏ r : PrimalPlaquettes B, c r) *
          ∏ r : PrimalPlaquettes B,
            (villainGaussianCoeff β (m r) : ℂ) *
              fourier (T := (1 : ℝ)) (-m r) (primalPlaquetteFlux θ r) := by
            rw [← Finset.prod_mul_distrib]
            apply Finset.prod_congr rfl
            intro r hr
            exact hcoeff r
      _ = ((m p : ℝ) * (m q : ℝ) : ℂ) * dualCharacterTerm β 0 m θ := by
            rw [hcprod]
            unfold dualCharacterTerm
            rw [Finset.prod_mul_distrib]
            have hgauss :
                (∏ r : PrimalPlaquettes B,
                  (villainGaussianCoeff β (m r) : ℂ)) =
                  (dualGaussianProduct β m : ℂ) := by
              rw [dualGaussianProduct, Complex.ofReal_prod]
              congr 1
            rw [hgauss, plaquetteMode_fourierProduct]
            simp [primalSheetLoopFrequency]
  calc
    primalFieldStrengthInsertionDensity β θ p q =
        ∏ r : PrimalPlaquettes B,
          ((villainFourierScale β : ℂ) *
            ∑' k : ℤ, (gB k : ℂ) * phase r k) := by
              unfold primalFieldStrengthInsertionDensity
              apply Finset.prod_congr rfl
              intro r hr
              exact hlocal r
    _ = (villainFourierScale β : ℂ) ^ Finset.univ.card *
          ∏ r : PrimalPlaquettes B,
            ∑' k : ℤ, (gB k : ℂ) * phase r k := by
              rw [Finset.prod_mul_distrib, Finset.prod_const]
    _ = _ := by
          rw [hprod]
          apply congrArg (fun z : ℂ =>
            (villainFourierScale β : ℂ) ^ Fintype.card (PrimalPlaquettes B) * z)
          apply tsum_congr
          intro m
          exact hmode m

private theorem primalFieldStrengthModeTerm_eq_dualCharacter {B : Box 4}
    (β : ℝ) (θ : PrimalAngleConfig B) (p q : PrimalPlaquettes B)
    (hpq : p ≠ q) (m : PrimalPlaquettes B → ℤ) :
    (∏ r : PrimalPlaquettes B,
      (villainInflatedGaussianCoeff β (m r) : ℂ) *
        villainInsertionPhase (decide (r = p ∨ r = q)) (m r)
          (primalPlaquetteFlux θ r)) =
      ((m p : ℝ) * (m q : ℝ) : ℂ) * dualCharacterTerm β 0 m θ := by
  classical
  let c : PrimalPlaquettes B → ℂ := fun r =>
    if r = p ∨ r = q then (-(m r : ℝ) : ℂ) else 1
  have hcoeff (r : PrimalPlaquettes B) :
      (villainInflatedGaussianCoeff β (m r) : ℂ) *
        villainInsertionPhase (decide (r = p ∨ r = q)) (m r)
          (primalPlaquetteFlux θ r) =
        c r * ((villainGaussianCoeff β (m r) : ℂ) *
          fourier (T := (1 : ℝ)) (-m r) (primalPlaquetteFlux θ r)) := by
    change (villainInflatedGaussianCoeff β (m r) : ℂ) *
        villainInsertionPhase (decide (r = p ∨ r = q)) (m r)
          (primalPlaquetteFlux θ r) =
      (if r = p ∨ r = q then (-(m r : ℝ) : ℂ) else 1) * _
    have h := villainInflatedCoeff_mul_insertionPhase β
      (decide (r = p ∨ r = q)) (m r) (primalPlaquetteFlux θ r)
    by_cases hr : r = p ∨ r = q
    · simpa [hr, villainInsertionPhase, villainInsertionMultiplier,
        villainInflatedGaussianCoeff, villainGaussianCoeff, ← mul_assoc] using h
    · simpa [hr, villainInsertionPhase, villainInsertionMultiplier,
        villainInflatedGaussianCoeff, villainGaussianCoeff, ← mul_assoc] using h
  have hqmem : q ∈ (Finset.univ : Finset (PrimalPlaquettes B)).erase p :=
    Finset.mem_erase.mpr ⟨Ne.symm hpq, Finset.mem_univ q⟩
  have hcp : c p = (-(m p : ℝ) : ℂ) := by simp [c]
  have hcq : c q = (-(m q : ℝ) : ℂ) := by simp [c]
  have hrest : ∏ r ∈ (Finset.univ.erase p).erase q, c r = 1 := by
    apply Finset.prod_eq_one
    intro r hr
    rcases Finset.mem_erase.mp hr with ⟨hrq, hrpMem⟩
    rcases Finset.mem_erase.mp hrpMem with ⟨hrp, _⟩
    simp [c, hrp, hrq]
  have hcprod : (∏ r : PrimalPlaquettes B, c r) =
      ((m p : ℝ) * (m q : ℝ) : ℂ) := by
    calc
      ∏ r : PrimalPlaquettes B, c r =
          (∏ r ∈ (Finset.univ.erase p).erase q, c r) * c q * c p := by
        rw [← Finset.prod_erase_mul (Finset.univ : Finset (PrimalPlaquettes B))
          c (Finset.mem_univ p)]
        rw [← Finset.prod_erase_mul (Finset.univ.erase p) c hqmem]
      _ = ((m p : ℝ) * (m q : ℝ) : ℂ) := by
        rw [hrest, hcp, hcq]
        push_cast
        ring
  calc
    _ = (∏ r : PrimalPlaquettes B, c r) *
        ∏ r : PrimalPlaquettes B,
          (villainGaussianCoeff β (m r) : ℂ) *
            fourier (T := (1 : ℝ)) (-m r) (primalPlaquetteFlux θ r) := by
          rw [← Finset.prod_mul_distrib]
          apply Finset.prod_congr rfl
          intro r hr
          exact hcoeff r
    _ = ((m p : ℝ) * (m q : ℝ) : ℂ) *
        dualCharacterTerm β 0 m θ := by
          rw [hcprod]
          unfold dualCharacterTerm
          rw [Finset.prod_mul_distrib]
          have hgauss :
              (∏ r : PrimalPlaquettes B,
                (villainGaussianCoeff β (m r) : ℂ)) =
                (dualGaussianProduct β m : ℂ) := by
            rw [dualGaussianProduct, Complex.ofReal_prod]
            congr 1
          rw [hgauss, plaquetteMode_fourierProduct]
          simp [primalSheetLoopFrequency]

/-- The integrable finite-volume dual identity for distinct plaquettes. Under
C4 these are the primal `{2,3}` observables and the mode coordinates are the
dual `{0,1}` curvatures. Their two orientation signs cancel. -/
theorem primalFieldStrengthInsertionCorrelation_eq_dual {B : Box 4}
    (β : ℝ) (hβ : 0 < β) (p q : PrimalPlaquettes B) (hpq : p ≠ q) :
    (∫ θ : PrimalAngleConfig B,
      primalFieldStrengthInsertionDensity β θ p q) =
      (villainFourierScale β : ℂ) ^ Fintype.card (PrimalPlaquettes B) *
        ∑' m : PrimalPlaquettes B → ℤ,
          ((m p : ℝ) * (m q : ℝ) : ℂ) *
            (dualWilsonTerm β 0 m : ℂ) := by
  classical
  let g : ℤ → ℝ := villainInflatedGaussianCoeff β
  have hg : Summable g := villainInflatedGaussianCoeff_summable β hβ
  have hg0 : ∀ k, 0 ≤ g k := villainInflatedGaussianCoeff_nonneg β
  have hmajor : Summable fun m : PrimalPlaquettes B → ℤ =>
      ∏ r : PrimalPlaquettes B, g (m r) :=
    summable_pi_prod_of_summable g hg
  have hnormBound (m : PrimalPlaquettes B → ℤ) (θ : PrimalAngleConfig B) :
      ‖((m p : ℝ) * (m q : ℝ) : ℂ) *
        dualCharacterTerm β 0 m θ‖ ≤
        ∏ r : PrimalPlaquettes B, g (m r) := by
    rw [← primalFieldStrengthModeTerm_eq_dualCharacter β θ p q hpq m,
      norm_prod]
    apply primal_prod_le_nonneg Finset.univ
    · intro r hr
      exact norm_nonneg _
    · intro r hr
      exact hg0 (m r)
    · intro r hr
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hg0 (m r))]
      calc
        g (m r) * ‖villainInsertionPhase (decide (r = p ∨ r = q))
            (m r) (primalPlaquetteFlux θ r)‖ ≤ g (m r) * 1 :=
          mul_le_mul_of_nonneg_left
            (villainInsertionPhase_norm_le_one (decide (r = p ∨ r = q))
              (m r) (primalPlaquetteFlux θ r)) (hg0 (m r))
        _ = g (m r) := mul_one _
  have htermIntegrable (m : PrimalPlaquettes B → ℤ) :
      Integrable (fun θ : PrimalAngleConfig B =>
        ((m p : ℝ) * (m q : ℝ) : ℂ) * dualCharacterTerm β 0 m θ) := by
    apply MeasureTheory.integrableOn_univ.mp
    have hc : Continuous (fun θ : PrimalAngleConfig B =>
        ((m p : ℝ) * (m q : ℝ) : ℂ) * dualCharacterTerm β 0 m θ) :=
      continuous_const.mul (dualCharacterTerm_continuous β 0 m)
    exact hc.continuousOn.integrableOn_compact isCompact_univ
  have hnormIntegrable (m : PrimalPlaquettes B → ℤ) :
      Integrable (fun θ : PrimalAngleConfig B =>
        ‖((m p : ℝ) * (m q : ℝ) : ℂ) * dualCharacterTerm β 0 m θ‖) :=
    (htermIntegrable m).norm
  have hnormSum : Summable fun m : PrimalPlaquettes B → ℤ =>
      ∫ θ : PrimalAngleConfig B,
        ‖((m p : ℝ) * (m q : ℝ) : ℂ) * dualCharacterTerm β 0 m θ‖ := by
    apply Summable.of_nonneg_of_le
      (fun m => integral_nonneg (fun θ => norm_nonneg _))
      (fun m => ?_) hmajor
    calc
      ∫ θ : PrimalAngleConfig B,
          ‖((m p : ℝ) * (m q : ℝ) : ℂ) * dualCharacterTerm β 0 m θ‖ ≤
        ∫ _θ : PrimalAngleConfig B, ∏ r : PrimalPlaquettes B, g (m r) := by
          apply integral_mono (hnormIntegrable m) (integrable_const _)
          exact hnormBound m
      _ = ∏ r : PrimalPlaquettes B, g (m r) := by simp
  have hswap := MeasureTheory.integral_tsum_of_summable_integral_norm
    (fun m => htermIntegrable m) hnormSum
  calc
    _ = ∫ θ : PrimalAngleConfig B,
        (villainFourierScale β : ℂ) ^ Fintype.card (PrimalPlaquettes B) *
          ∑' m : PrimalPlaquettes B → ℤ,
            ((m p : ℝ) * (m q : ℝ) : ℂ) * dualCharacterTerm β 0 m θ := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun θ =>
            primalFieldStrengthInsertionDensity_eq_dualSeries β hβ θ p q hpq
    _ = (villainFourierScale β : ℂ) ^ Fintype.card (PrimalPlaquettes B) *
        ∫ θ : PrimalAngleConfig B,
          ∑' m : PrimalPlaquettes B → ℤ,
            ((m p : ℝ) * (m q : ℝ) : ℂ) * dualCharacterTerm β 0 m θ := by
          rw [MeasureTheory.integral_const_mul]
    _ = (villainFourierScale β : ℂ) ^ Fintype.card (PrimalPlaquettes B) *
        ∑' m : PrimalPlaquettes B → ℤ,
          ∫ θ : PrimalAngleConfig B,
            ((m p : ℝ) * (m q : ℝ) : ℂ) * dualCharacterTerm β 0 m θ := by
          rw [hswap]
    _ = _ := by
          congr 1
          apply tsum_congr
          intro m
          rw [MeasureTheory.integral_const_mul, dualCharacterTerm_integral]

/--
C4-compatible circle version of the differentiated Villain character
series.
-/
theorem villainCircleFieldStrengthNumerator_eq_representative
    (β : ℝ) (z : UnitAddCircle) (hβ : 0 < β) :
    villainCircleFieldStrengthNumerator β z =
      villainFieldStrengthNumerator β
        (2 * Real.pi * circleRepresentative z) := by
  rw [villainFieldStrengthNumerator_eq_fourier β _ hβ]
  rw [villainCircleFieldStrengthNumerator_apply β z hβ]
  congr 1
  apply tsum_congr
  intro k
  have hchar : fourier (T := (1 : ℝ)) (-k) z =
      fourier (T := (1 : ℝ)) (-k) (circleRepresentative z : UnitAddCircle) :=
    congrArg (fun w : UnitAddCircle => fourier (T := (1 : ℝ)) (-k) w)
      (circleRepresentative_coe z).symm
  rw [hchar, fourier_coe_apply]
  congr 3
  push_cast
  ring

/-- The Villain field-strength observable on a circle-valued plaquette flux. -/
noncomputable def villainCircleFieldStrength
    (β : ℝ) (z : UnitAddCircle) : ℂ :=
  villainCircleFieldStrengthNumerator β z / (villainCircleWeight β z : ℂ)

theorem villainCircleFieldStrength_continuous
    (β : ℝ) (hβ : 0 < β) :
    Continuous (villainCircleFieldStrength β) := by
  apply (villainCircleFieldStrengthNumeratorMap β).continuous.div
    (Complex.continuous_ofReal.comp (villainCircleWeight_continuous β))
  intro z
  change (villainCircleWeight β z : ℂ) ≠ 0
  exact_mod_cast (villainCircleWeight_pos β z hβ).ne'


/-- The primal field-strength variable (2.89) at a finite plaquette. -/
noncomputable def primalFieldStrength {B : Box 4}
    (β : ℝ) (θ : PrimalAngleConfig B) (p : PrimalPlaquettes B) : ℂ :=
  villainCircleFieldStrength β (primalPlaquetteFlux θ p)


theorem continuous_primalFieldStrength {B : Box 4}
    (β : ℝ) (hβ : 0 < β) (p : PrimalPlaquettes B) :
    Continuous (fun θ : PrimalAngleConfig B => primalFieldStrength β θ p) :=
  (villainCircleFieldStrength_continuous β hβ).comp
    (continuous_primalPlaquetteFlux p)


/-- The normalized finite-volume Villain two-plaquette field-strength
correlation. The product is complex-valued because each field-strength
insertion contains `-i`. -/
noncomputable def primalFieldStrengthCorrelation {B : Box 4}
    (β : ℝ) (p q : PrimalPlaquettes B) : ℂ :=
  (∫ θ : PrimalAngleConfig B,
      (primalVillainDensity (B := B) β θ : ℂ) *
        primalFieldStrength β θ p * primalFieldStrength β θ q) /
    (primalVillainPartition (B := B) β : ℂ)


private theorem primalFieldStrengthInsertionDensity_eq_observableNumerator
    {B : Box 4} (β : ℝ) (hβ : 0 < β) (θ : PrimalAngleConfig B)
    (p q : PrimalPlaquettes B) (hpq : p ≠ q) :
    primalFieldStrengthInsertionDensity β θ p q =
      (primalVillainDensity β θ : ℂ) *
        primalFieldStrength β θ p * primalFieldStrength β θ q := by
  classical
  let f : PrimalPlaquettes B → ℂ := fun r =>
    if r = p then primalFieldStrength β θ p
    else if r = q then primalFieldStrength β θ q else 1
  have hratio (z : UnitAddCircle) :
      villainCircleFieldStrengthNumerator β z =
        (villainCircleWeight β z : ℂ) * villainCircleFieldStrength β z := by
    have hw : (villainCircleWeight β z : ℂ) ≠ 0 := by
      exact_mod_cast (villainCircleWeight_pos β z hβ).ne'
    unfold villainCircleFieldStrength
    field_simp
  have hfactor (r : PrimalPlaquettes B) :
      primalFieldStrengthInsertionFactor β θ p q r =
        (villainCircleWeight β (primalPlaquetteFlux θ r) : ℂ) * f r := by
    by_cases hrp : r = p
    · subst r
      simp [primalFieldStrengthInsertionFactor, f, primalFieldStrength, hratio]
    · by_cases hrq : r = q
      · subst r
        simp [primalFieldStrengthInsertionFactor, f, primalFieldStrength,
          hrp, hratio]
      · simp [primalFieldStrengthInsertionFactor, f, hrp, hrq]
  have hrest : ∏ r ∈ (Finset.univ.erase p).erase q, f r = 1 := by
    apply Finset.prod_eq_one
    intro r hr
    rcases Finset.mem_erase.mp hr with ⟨hrq, hrpMem⟩
    rcases Finset.mem_erase.mp hrpMem with ⟨hrp, _⟩
    simp [f, hrp, hrq]
  have hfprod : (∏ r : PrimalPlaquettes B, f r) =
      primalFieldStrength β θ p * primalFieldStrength β θ q := by
    have hqmem : q ∈ (Finset.univ : Finset (PrimalPlaquettes B)).erase p :=
      Finset.mem_erase.mpr ⟨Ne.symm hpq, Finset.mem_univ q⟩
    calc
      ∏ r : PrimalPlaquettes B, f r =
          (∏ r ∈ (Finset.univ.erase p).erase q, f r) * f q * f p := by
        rw [← Finset.prod_erase_mul (Finset.univ : Finset (PrimalPlaquettes B))
          f (Finset.mem_univ p)]
        rw [← Finset.prod_erase_mul (Finset.univ.erase p) f hqmem]
      _ = primalFieldStrength β θ p * primalFieldStrength β θ q := by
        rw [hrest]
        simp [f, Ne.symm hpq]
        ring
  calc
    primalFieldStrengthInsertionDensity β θ p q =
        ∏ r : PrimalPlaquettes B,
          (villainCircleWeight β (primalPlaquetteFlux θ r) : ℂ) * f r := by
            unfold primalFieldStrengthInsertionDensity
            apply Finset.prod_congr rfl
            intro r hr
            exact hfactor r
    _ = (∏ r : PrimalPlaquettes B,
          (villainCircleWeight β (primalPlaquetteFlux θ r) : ℂ)) *
          ∏ r : PrimalPlaquettes B, f r := Finset.prod_mul_distrib
    _ = (primalVillainDensity β θ : ℂ) *
          primalFieldStrength β θ p * primalFieldStrength β θ q := by
            rw [hfprod, primalVillainDensity, Complex.ofReal_prod]
            ring

/-- The partition function equals the zero-current dual partition times the
common Poisson factor. -/
theorem primalVillainPartition_eq_dual {B : Box 4}
    (β : ℝ) (hβ : 0 < β) :
    (primalVillainPartition (B := B) β : ℂ) =
      (villainFourierScale β : ℂ) ^ Fintype.card (PrimalPlaquettes B) *
        (dualWilsonPartition β (0 : Chain 4 B) : ℂ) := by
  calc
    (primalVillainPartition (B := B) β : ℂ) =
        ∫ θ : PrimalAngleConfig B, (primalVillainDensity β θ : ℂ) := by
          rw [primalVillainPartition, integral_complex_ofReal]
    _ = ∫ θ : PrimalAngleConfig B,
        (villainFourierScale β : ℂ) ^ Fintype.card (PrimalPlaquettes B) *
          ∑' m : PrimalPlaquettes B → ℤ, dualCharacterTerm β 0 m θ := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun θ =>
            by simpa [dualCharacterTerm, primalSheetLoopFrequency] using
              primalVillainDensity_characterExpansion β hβ θ
    _ = (villainFourierScale β : ℂ) ^ Fintype.card (PrimalPlaquettes B) *
        ∫ θ : PrimalAngleConfig B,
          ∑' m : PrimalPlaquettes B → ℤ, dualCharacterTerm β 0 m θ := by
          rw [integral_const_mul]
    _ = (villainFourierScale β : ℂ) ^ Fintype.card (PrimalPlaquettes B) *
        (dualWilsonPartition β (0 : Chain 4 B) : ℂ) := by
          rw [dualCharacterSeries_integral_eq β hβ 0]

/-- The normalized finite dual two-curvature correlation, with each integer
mode weighted by the zero-current Villain dual law. -/
noncomputable def finiteDualCurvatureCorrelation {B : Box 4}
    (β : ℝ) (p q : PrimalPlaquettes B) : ℂ :=
  (∑' m : PrimalPlaquettes B → ℤ,
    ((m p : ℝ) * (m q : ℝ) : ℂ) * (dualWilsonTerm β 0 m : ℂ)) /
      (dualWilsonPartition β (0 : Chain 4 B) : ℂ)

/-- Exact finite-volume dual-observable bridge for distinct faces. The
coordinate-oriented C4 signs are both `-1` for the primal `{2,3}` to dual
`{0,1}` map, so their product is `+1`. -/
theorem primalFieldStrengthCorrelation_eq_dual {B : Box 4}
    (β : ℝ) (hβ : 0 < β) (p q : PrimalPlaquettes B) (hpq : p ≠ q) :
    primalFieldStrengthCorrelation β p q =
      finiteDualCurvatureCorrelation β p q := by
  have hnum :
      (∫ θ : PrimalAngleConfig B,
        (primalVillainDensity β θ : ℂ) *
          primalFieldStrength β θ p * primalFieldStrength β θ q) =
        (villainFourierScale β : ℂ) ^ Fintype.card (PrimalPlaquettes B) *
          ∑' m : PrimalPlaquettes B → ℤ,
            ((m p : ℝ) * (m q : ℝ) : ℂ) *
              (dualWilsonTerm β 0 m : ℂ) := by
    calc
      _ = ∫ θ : PrimalAngleConfig B,
          primalFieldStrengthInsertionDensity β θ p q := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall fun θ =>
              (primalFieldStrengthInsertionDensity_eq_observableNumerator
                β hβ θ p q hpq).symm
      _ = _ := primalFieldStrengthInsertionCorrelation_eq_dual β hβ p q hpq
  have hden := primalVillainPartition_eq_dual (B := B) β hβ
  have hscale : villainFourierScale β ≠ 0 := by
    unfold villainFourierScale
    exact_mod_cast (show
      (1 / Real.sqrt (2 * Real.pi * β) : ℝ) ≠ 0 by positivity)
  have hden0 :
      (dualWilsonPartition β (0 : Chain 4 B) : ℂ) ≠ 0 := by
    exact_mod_cast (dualWilsonPartition_zero_pos (B := B) β hβ).ne'
  unfold primalFieldStrengthCorrelation finiteDualCurvatureCorrelation
  rw [hnum, hden]
  have hscalePow :
      (villainFourierScale β : ℂ) ^ Fintype.card (PrimalPlaquettes B) ≠ 0 :=
    pow_ne_zero _ (by exact_mod_cast hscale)
  field_simp


end FroehlichSpencer.FS82.Wilson
