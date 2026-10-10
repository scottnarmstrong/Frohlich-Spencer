/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import FroehlichSpencer.FS82.Wilson.PrimalMeasure
public import FroehlichSpencer.FS82.Poisson.PiSummable
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Constrained integer plaquette sums

Finite-volume Fourier modes are integer plaquette fields. Their cubical
boundary is the link divergence appearing in the Wilson-loop duality formula.
-/

public section

namespace FroehlichSpencer.FS82.Wilson

open FroehlichSpencer.FS82.Cubical
open FroehlichSpencer.FS82.Poisson
open MeasureTheory

local instance : Fact (0 < (1 : ℝ)) := ⟨one_pos⟩
noncomputable local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
noncomputable local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
noncomputable local instance instIsProbabilityMeasureUnitAddCircleVolume_froehlichSpencer_1 : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem primalTorus_character_integral {B : Box 4}
    (q : PrimalLinks B → ℤ) :
    ∫ θ : PrimalAngleConfig B, UnitAddTorus.mFourier q θ =
      if q = 0 then 1 else 0 := by
  have h := (orthonormal_iff_ite.mp
    (UnitAddTorus.orthonormal_mFourier (d := PrimalLinks B)))
      (0 : PrimalLinks B → ℤ) q
  rw [MeasureTheory.ContinuousMap.inner_toLp] at h
  simpa [UnitAddTorus.mFourier_zero, eq_comm] using h

/-- The integer 2-chain whose plaquette coefficients are the Fourier modes. -/
@[expose] noncomputable def plaquetteModeChain {B : Box 4}
    (m : PrimalPlaquettes B → ℤ) : Chain 4 B :=
  ∑ p : PrimalPlaquettes B, Finsupp.single p.1 (m p)

/-- Link divergence of an integer plaquette field. -/
@[expose] noncomputable def plaquetteModeDivergence {B : Box 4}
    (m : PrimalPlaquettes B → ℤ) : PrimalLinks B → ℤ :=
  fun l => (boundary (plaquetteModeChain m)) l.1

/-- The frequency of the boundary loop of a plaquette sheet, restricted to
primal links. -/
@[expose] noncomputable def primalSheetLoopFrequency {B : Box 4}
    (S : Chain 4 B) : PrimalLinks B → ℤ :=
  fun l => (boundary S) l.1

/-- Product of the Gaussian character coefficients in (2.19). -/
@[expose] noncomputable def dualGaussianProduct {B : Box 4} (β : ℝ)
    (m : PrimalPlaquettes B → ℤ) : ℝ :=
  ∏ p : PrimalPlaquettes B,
    Real.exp (-(m p : ℝ) ^ 2 / (2 * β))

/-- A dual configuration contributes to the Wilson numerator precisely when
its link divergence equals the oriented loop current. -/
@[expose] noncomputable def dualWilsonTerm {B : Box 4} (β : ℝ)
    (S : Chain 4 B) (m : PrimalPlaquettes B → ℤ) : ℝ :=
  if plaquetteModeDivergence m = primalSheetLoopFrequency S then dualGaussianProduct β m else 0

/-- The constrained integer plaquette partition sum `Z_B(j)` from (2.27). -/
@[expose] noncomputable def dualWilsonPartition {B : Box 4} (β : ℝ)
    (S : Chain 4 B) : ℝ :=
  ∑' m : PrimalPlaquettes B → ℤ, dualWilsonTerm (B := B) β S m

theorem dualGaussianProduct_nonneg {B : Box 4} (β : ℝ)
    (m : PrimalPlaquettes B → ℤ) : 0 ≤ dualGaussianProduct β m := by
  unfold dualGaussianProduct
  exact Finset.prod_nonneg fun p hp => (Real.exp_pos _).le

theorem dualGaussianProduct_pos {B : Box 4} (β : ℝ)
    (m : PrimalPlaquettes B → ℤ) : 0 < dualGaussianProduct β m := by
  unfold dualGaussianProduct
  exact Finset.prod_pos fun p hp => Real.exp_pos _

theorem dualWilsonTerm_nonneg {B : Box 4} (β : ℝ) (S : Chain 4 B)
    (m : PrimalPlaquettes B → ℤ) : 0 ≤ dualWilsonTerm (B := B) β S m := by
  unfold dualWilsonTerm
  split_ifs <;> [exact dualGaussianProduct_nonneg (B := B) β m; exact le_rfl]

theorem dualGaussianProduct_summable {B : Box 4} (β : ℝ) (hβ : 0 < β) :
    Summable (dualGaussianProduct (B := B) β) := by
  classical
  unfold dualGaussianProduct
  exact summable_pi_prod_of_summable
    (fun n : ℤ => Real.exp (-(n : ℝ) ^ 2 / (2 * β)))
    (villainCharacterCoeff_summable β hβ)

theorem dualWilsonTerm_summable {B : Box 4} (β : ℝ) (hβ : 0 < β)
    (S : Chain 4 B) : Summable (dualWilsonTerm (B := B) β S) := by
  apply Summable.of_nonneg_of_le (fun m => dualWilsonTerm_nonneg β S m)
    (fun m => ?_) (dualGaussianProduct_summable (B := B) β hβ)
  unfold dualWilsonTerm
  split_ifs <;> simp [dualGaussianProduct_nonneg]


theorem dualWilsonPartition_pos_of_solution {B : Box 4} (β : ℝ) (hβ : 0 < β)
    (S : Chain 4 B) (m₀ : PrimalPlaquettes B → ℤ)
    (hm₀ : plaquetteModeDivergence m₀ = primalSheetLoopFrequency S) :
    0 < dualWilsonPartition β S := by
  unfold dualWilsonPartition
  apply (dualWilsonTerm_summable (B := B) β hβ S).tsum_pos
    (fun m => dualWilsonTerm_nonneg (B := B) β S m) m₀
  simpa [dualWilsonTerm, hm₀] using dualGaussianProduct_pos (B := B) β m₀

theorem dualWilsonPartition_zero_pos {B : Box 4} (β : ℝ) (hβ : 0 < β) :
    0 < dualWilsonPartition β (0 : Chain 4 B) := by
  apply dualWilsonPartition_pos_of_solution (B := B) β hβ 0 0
  funext l
  simp [plaquetteModeDivergence, primalSheetLoopFrequency, plaquetteModeChain]

/-- One Fourier mode of the expanded primal density, including the Wilson
boundary character. -/
@[expose] noncomputable def dualCharacterTerm {B : Box 4} (β : ℝ)
    (S : Chain 4 B) (m : PrimalPlaquettes B → ℤ)
    (θ : PrimalAngleConfig B) : ℂ :=
  (dualGaussianProduct β m : ℂ) *
    UnitAddTorus.mFourier
      (fun l => -plaquetteModeDivergence m l + primalSheetLoopFrequency S l) θ

theorem dualCharacterTerm_integral {B : Box 4} (β : ℝ) (S : Chain 4 B)
    (m : PrimalPlaquettes B → ℤ) :
    ∫ θ : PrimalAngleConfig B, dualCharacterTerm β S m θ =
      (dualWilsonTerm β S m : ℂ) := by
  let q : PrimalLinks B → ℤ := fun l =>
    -plaquetteModeDivergence m l + primalSheetLoopFrequency S l
  have horth := primalTorus_character_integral (B := B) q
  have hzero : q = 0 ↔
      plaquetteModeDivergence m = primalSheetLoopFrequency S := by
    constructor
    · intro h
      funext l
      have hl := congrFun h l
      dsimp [q] at hl
      omega
    · intro h
      funext l
      dsimp [q]
      rw [h]
      abel
  unfold dualCharacterTerm
  rw [MeasureTheory.integral_const_mul]
  rw [horth]
  by_cases h : plaquetteModeDivergence m = primalSheetLoopFrequency S
  · have hq : q = 0 := hzero.mpr h
    simp [dualWilsonTerm, h, hq]
  · have hq : q ≠ 0 := fun hq => h (hzero.mp hq)
    simp [dualWilsonTerm, h, hq]

theorem dualCharacterTerm_continuous {B : Box 4} (β : ℝ) (S : Chain 4 B)
    (m : PrimalPlaquettes B → ℤ) :
    Continuous (fun θ : PrimalAngleConfig B => dualCharacterTerm β S m θ) := by
  exact continuous_const.mul
    (UnitAddTorus.mFourier
      (fun l => -plaquetteModeDivergence m l + primalSheetLoopFrequency S l)).continuous

theorem dualCharacterTerm_integrable {B : Box 4} (β : ℝ) (S : Chain 4 B)
    (m : PrimalPlaquettes B → ℤ) :
    Integrable (dualCharacterTerm β S m) := by
  apply MeasureTheory.integrableOn_univ.mp
  exact (dualCharacterTerm_continuous β S m).continuousOn.integrableOn_compact isCompact_univ

theorem dualCharacterTerm_norm {B : Box 4} (β : ℝ) (S : Chain 4 B)
    (m : PrimalPlaquettes B → ℤ) (θ : PrimalAngleConfig B) :
    ‖dualCharacterTerm β S m θ‖ = dualGaussianProduct β m := by
  unfold dualCharacterTerm
  rw [norm_mul, Complex.norm_real]
  rw [Real.norm_eq_abs, abs_of_nonneg (dualGaussianProduct_nonneg β m)]
  simp [UnitAddTorus.mFourier]

theorem dualCharacterTerm_integral_norm {B : Box 4} (β : ℝ) (S : Chain 4 B)
    (m : PrimalPlaquettes B → ℤ) :
    ∫ θ : PrimalAngleConfig B, ‖dualCharacterTerm β S m θ‖ =
      dualGaussianProduct β m := by
  simp_rw [dualCharacterTerm_norm]
  simp

/-- Absolute termwise integration of the character expansion gives the
constrained plaquette partition sum. -/
theorem dualCharacterSeries_integral_eq {B : Box 4} (β : ℝ) (hβ : 0 < β)
    (S : Chain 4 B) :
    ∫ θ : PrimalAngleConfig B,
      ∑' m : PrimalPlaquettes B → ℤ, dualCharacterTerm β S m θ =
        (dualWilsonPartition β S : ℂ) := by
  have hnormsum : Summable fun m : PrimalPlaquettes B → ℤ =>
    ∫ θ : PrimalAngleConfig B, ‖dualCharacterTerm β S m θ‖ := by
    apply (dualGaussianProduct_summable (B := B) β hβ).congr
    intro m
    exact (dualCharacterTerm_integral_norm β S m).symm
  have hswap := MeasureTheory.integral_tsum_of_summable_integral_norm
    (fun m => dualCharacterTerm_integrable β S m) hnormsum
  rw [← hswap]
  calc
    _ = ∑' m : PrimalPlaquettes B → ℤ, (dualWilsonTerm β S m : ℂ) :=
      tsum_congr fun m => dualCharacterTerm_integral β S m
    _ = (dualWilsonPartition β S : ℂ) := by
      unfold dualWilsonPartition
      exact (Complex.ofReal_tsum (f := dualWilsonTerm (B := B) β S)).symm

private def finSuccIntEquiv (n : ℕ) :
    (Fin (n + 1) → ℤ) ≃ ℤ × (Fin n → ℤ) where
  toFun f := (f 0, fun i => f i.succ)
  invFun p := Fin.cases p.1 p.2
  left_inv f := by
    funext i
    refine Fin.cases ?_ ?_ i <;> simp
  right_inv p := by
    rcases p with ⟨z, f⟩
    rfl

private theorem product_tsum_fin (n : ℕ) (g : ℤ → ℝ) (hg : Summable g)
    (hg0 : ∀ k, 0 ≤ g k) (phase : Fin n → ℤ → ℂ)
    (hphase : ∀ i k, ‖phase i k‖ = 1) :
    (∏ i : Fin n, ∑' k : ℤ, (g k : ℂ) * phase i k) =
      ∑' f : Fin n → ℤ, ∏ i : Fin n, (g (f i) : ℂ) * phase i (f i) := by
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
        summable_pi_prod_of_summable g hg
      have hF : Summable F := by
        apply Summable.of_norm_bounded hcoeff
        intro f
        dsimp [F]
        rw [norm_prod]
        apply le_of_eq
        apply Finset.prod_congr rfl
        intro i hi
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (hg0 (f i)), hphase i (f i)]
        simp
      let e := finSuccIntEquiv n
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

private theorem product_tsum_fintype {ι : Type*} [Fintype ι]
    (g : ℤ → ℝ) (hg : Summable g) (hg0 : ∀ k, 0 ≤ g k)
    (phase : ι → ℤ → ℂ) (hphase : ∀ i k, ‖phase i k‖ = 1) :
    (∏ i : ι, ∑' k : ℤ, (g k : ℂ) * phase i k) =
      ∑' f : ι → ℤ, ∏ i : ι, (g (f i) : ℂ) * phase i (f i) := by
  classical
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let eπ : (ι → ℤ) ≃ (Fin (Fintype.card ι) → ℤ) :=
    Equiv.piCongrLeft (fun _ : Fin (Fintype.card ι) => ℤ) e
  have hfin := product_tsum_fin (Fintype.card ι) g hg hg0
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

private theorem fourier_zsmul_argument {k n : ℤ} (x : UnitAddCircle) :
    fourier (T := (1 : ℝ)) n (k • x) = fourier (T := (1 : ℝ)) (n * k) x := by
  rw [fourier_apply, fourier_apply, smul_smul]

private theorem fourier_argument_add {n : ℤ} (x y : UnitAddCircle) :
    fourier (T := (1 : ℝ)) n (x + y) =
      fourier (T := (1 : ℝ)) n x * fourier (T := (1 : ℝ)) n y := by
  rw [fourier_apply, zsmul_add, AddCircle.toCircle_add, Circle.coe_mul,
    ← fourier_apply, ← fourier_apply]

private theorem circleChainPairing_eq_link_sum {B : Box 4}
    (q : Chain 4 B) (θ : PrimalAngleConfig B) :
    circleChainPairing q (primalCircleCochain θ) =
      ∑ l : PrimalLinks B, q l.1 • θ l := by
  classical
  induction q using Finsupp.induction_linear with
  | zero => simp [circleChainPairing]
  | add q r hq hr =>
      rw [circleChainPairing_add, hq, hr]
      simp [Finsupp.add_apply, add_zsmul, Finset.sum_add_distrib]
  | single c z =>
      have hsingle :
          circleChainPairing (Finsupp.single c z) (primalCircleCochain θ) =
            z • primalCircleCochain θ c := by
        simp [circleChainPairing]
      by_cases hc : cellDegree c = 1
      · let l₀ : PrimalLinks B := ⟨c, hc⟩
        have hangle : primalCircleCochain θ c = θ l₀ := by
          simp [primalCircleCochain, hc, l₀]
        have hsum :
            (∑ l : PrimalLinks B, (Finsupp.single c z : Chain 4 B) l.1 • θ l) =
              (Finsupp.single c z : Chain 4 B) l₀.1 • θ l₀ :=
          Fintype.sum_eq_single l₀ (by
            intro l hl
            have hne : l.1 ≠ c := by
              intro heq
              exact hl (Subtype.ext heq)
            rw [Finsupp.single_eq_of_ne hne]
            simp)
        calc
          circleChainPairing (Finsupp.single c z) (primalCircleCochain θ) =
              z • primalCircleCochain θ c := hsingle
          _ = z • θ l₀ := by rw [hangle]
          _ = ∑ l : PrimalLinks B, (Finsupp.single c z : Chain 4 B) l.1 • θ l := by
                rw [hsum]
                simp [l₀, Finsupp.single_eq_same]
      · have hangle : primalCircleCochain θ c = 0 := by
          simp [primalCircleCochain, hc]
        have hsum :
            (∑ l : PrimalLinks B, (Finsupp.single c z : Chain 4 B) l.1 • θ l) = 0 := by
          apply Fintype.sum_eq_zero
          intro l
          have hne : l.1 ≠ c := by
            intro heq
            exact hc (heq ▸ l.property)
          rw [Finsupp.single_eq_of_ne hne]
          simp
        calc
          circleChainPairing (Finsupp.single c z) (primalCircleCochain θ) =
              z • primalCircleCochain θ c := hsingle
          _ = 0 := by rw [hangle]; simp
          _ = ∑ l : PrimalLinks B, (Finsupp.single c z : Chain 4 B) l.1 • θ l := by
                rw [hsum]

private theorem fourier_finset_zsmul_sum {ι : Type*} (s : Finset ι) (n : ℤ)
    (a : ι → ℤ) (x : ι → UnitAddCircle) :
    fourier (T := (1 : ℝ)) n (∑ i ∈ s, a i • x i) =
      ∏ i ∈ s, fourier (T := (1 : ℝ)) (n * a i) (x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.prod_insert hi,
        fourier_argument_add, fourier_zsmul_argument, ih]

private theorem fourier_sum_zsmul {ι : Type*} [Fintype ι] (n : ℤ)
    (a : ι → ℤ) (x : ι → UnitAddCircle) :
    fourier (T := (1 : ℝ)) n (∑ i, a i • x i) =
      ∏ i, fourier (T := (1 : ℝ)) (n * a i) (x i) := by
  simpa using fourier_finset_zsmul_sum (Finset.univ : Finset ι) n a x

/-- Stokes transports the product of plaquette characters to the character
of the oriented link divergence. -/
theorem plaquetteMode_fourierProduct {B : Box 4} (m : PrimalPlaquettes B → ℤ)
    (θ : PrimalAngleConfig B) :
    (∏ p : PrimalPlaquettes B,
      fourier (T := (1 : ℝ)) (-m p) (primalPlaquetteFlux θ p)) =
      UnitAddTorus.mFourier (fun l => -plaquetteModeDivergence m l) θ := by
  classical
  let q : Chain 4 B := plaquetteModeChain m
  let f : Cell 4 B → UnitAddCircle := circleCochainCoboundary (primalCircleCochain θ)
  have hplaq (p : PrimalPlaquettes B) : primalPlaquetteFlux θ p = f p.1 := rfl
  have hpair : circleChainPairing q f = ∑ p : PrimalPlaquettes B, m p • f p.1 := by
    dsimp [q, plaquetteModeChain, circleChainPairing]
    simp [Finsupp.linearCombination_single]
  have hprod := fourier_sum_zsmul (ι := PrimalPlaquettes B) (-1) m
    (fun p => f p.1)
  have hstokes := circleChainPairing_boundary_eq_coboundary q
    (primalCircleCochain θ)
  have hlinks := circleChainPairing_eq_link_sum (boundary q) θ
  have hlinkprod := fourier_sum_zsmul (ι := PrimalLinks B) (-1)
    (fun l => (boundary q) l.1) θ
  calc
    (∏ p : PrimalPlaquettes B,
        fourier (T := (1 : ℝ)) (-m p) (primalPlaquetteFlux θ p)) =
        ∏ p : PrimalPlaquettes B,
          fourier (T := (1 : ℝ)) ((-1) * m p) (f p.1) := by
            apply Finset.prod_congr rfl
            intro p hp
            rw [hplaq]
            simp only [neg_one_mul]
    _ = fourier (T := (1 : ℝ)) (-1)
          (∑ p : PrimalPlaquettes B, m p • f p.1) := by
            simpa only [neg_one_mul] using hprod.symm
    _ = fourier (T := (1 : ℝ)) (-1) (circleChainPairing q f) := by
          exact congrArg (fourier (T := (1 : ℝ)) (-1)) hpair.symm
    _ = fourier (T := (1 : ℝ)) (-1)
          (circleChainPairing (boundary q) (primalCircleCochain θ)) := by
            exact congrArg (fourier (T := (1 : ℝ)) (-1)) hstokes.symm
    _ = fourier (T := (1 : ℝ)) (-1)
          (∑ l : PrimalLinks B, (boundary q) l.1 • θ l) :=
            congrArg (fourier (T := (1 : ℝ)) (-1)) hlinks
    _ = ∏ l : PrimalLinks B,
          fourier (T := (1 : ℝ)) ((-1) * (boundary q) l.1) (θ l) :=
            hlinkprod
    _ = UnitAddTorus.mFourier
          (fun l => -plaquetteModeDivergence m l) θ := by
            simp [UnitAddTorus.mFourier, plaquetteModeDivergence, q]

@[expose] noncomputable def villainFourierScale (β : ℝ) : ℂ :=
  (1 / Real.sqrt (2 * Real.pi * β) : ℝ)

@[expose] noncomputable def villainGaussianCoeff (β : ℝ) (k : ℤ) : ℝ :=
  Real.exp (-(k : ℝ) ^ 2 / (2 * β))

@[expose] noncomputable def villainCircleCharacterSeries (β : ℝ) (z : UnitAddCircle) : ℂ :=
  ∑' k : ℤ, (villainGaussianCoeff β k : ℂ) * fourier (T := (1 : ℝ)) (-k) z

private theorem villainCircleFourierMap_eq_characterSeries (β : ℝ) (hβ : 0 < β)
    (z : UnitAddCircle) :
    villainCircleFourierMap β z =
      villainFourierScale β * villainCircleCharacterSeries β z := by
  have hterms : Summable fun k : ℤ =>
      (Real.exp (-(k : ℝ) ^ 2 / (2 * β)) : ℂ) •
        fourier (T := (1 : ℝ)) (-k) := by
    apply Summable.of_norm_bounded (villainCharacterCoeff_summable β hβ)
    intro k
    simp only [norm_smul, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg (Real.exp_nonneg _), fourier_norm]
    simp
  have hsum := ContinuousMap.tsum_apply hterms z
  rw [villainCircleFourierMap, ContinuousMap.smul_apply, hsum.symm]
  simp only [smul_eq_mul, villainFourierScale]
  congr 1
  · norm_cast

private theorem villainCircleWeight_complex (β : ℝ) (z : UnitAddCircle)
    (hβ : 0 < β) :
    (villainCircleWeight β z : ℂ) = villainCircleFourierMap β z := by
  rw [villainCircleWeight_eq_periodized β z hβ,
    villainCircleFourierMap_apply β z hβ]

/-- Finite-volume product expansion in plaquette characters. The common
Poisson prefactor is kept explicit so it cancels from normalized expectations. -/
theorem primalVillainDensity_characterExpansion {B : Box 4} (β : ℝ)
    (hβ : 0 < β) (θ : PrimalAngleConfig B) :
    (primalVillainDensity β θ : ℂ) =
      villainFourierScale β ^ Fintype.card (PrimalPlaquettes B) *
        ∑' m : PrimalPlaquettes B → ℤ,
          (dualGaussianProduct β m : ℂ) *
            UnitAddTorus.mFourier (fun l => -plaquetteModeDivergence m l) θ := by
  classical
  let g : ℤ → ℝ := villainGaussianCoeff β
  let phase : PrimalPlaquettes B → ℤ → ℂ := fun p k =>
    fourier (T := (1 : ℝ)) (-k) (primalPlaquetteFlux θ p)
  have hg : Summable g := by
    change Summable (fun k : ℤ => Real.exp (-(k : ℝ) ^ 2 / (2 * β)))
    exact villainCharacterCoeff_summable β hβ
  have hg0 : ∀ k, 0 ≤ g k := fun k => by
    change 0 ≤ Real.exp (-(k : ℝ) ^ 2 / (2 * β))
    exact Real.exp_nonneg _
  have hphase : ∀ p k, ‖phase p k‖ = 1 := by
    intro p k
    simp [phase, fourier_apply]
  have hproduct := product_tsum_fintype (ι := PrimalPlaquettes B)
    g hg hg0 phase hphase
  have hcoeff (m : PrimalPlaquettes B → ℤ) :
      (dualGaussianProduct β m : ℂ) = ∏ p : PrimalPlaquettes B, (g (m p) : ℂ) := by
    simp [dualGaussianProduct, g, villainGaussianCoeff]
  have hterm (m : PrimalPlaquettes B → ℤ) :
      (∏ p : PrimalPlaquettes B, (g (m p) : ℂ) * phase p (m p)) =
        (dualGaussianProduct β m : ℂ) *
          UnitAddTorus.mFourier (fun l => -plaquetteModeDivergence m l) θ := by
    calc
      _ = (∏ p : PrimalPlaquettes B, (g (m p) : ℂ)) *
            (∏ p : PrimalPlaquettes B, phase p (m p)) := Finset.prod_mul_distrib
      _ = _ := by rw [← hcoeff, ← plaquetteMode_fourierProduct]
  have hweights :
      (primalVillainDensity β θ : ℂ) =
        ∏ p : PrimalPlaquettes B,
          villainFourierScale β * villainCircleCharacterSeries β
            (primalPlaquetteFlux θ p) := by
    unfold primalVillainDensity
    rw [Complex.ofReal_prod]
    apply Finset.prod_congr rfl
    intro p hp
    rw [villainCircleWeight_complex β (primalPlaquetteFlux θ p) hβ,
      villainCircleFourierMap_eq_characterSeries β hβ]
  calc
    (primalVillainDensity β θ : ℂ) =
        villainFourierScale β ^ Fintype.card (PrimalPlaquettes B) *
          ∏ p : PrimalPlaquettes B, villainCircleCharacterSeries β
            (primalPlaquetteFlux θ p) := by
          rw [hweights, Finset.prod_mul_distrib, Finset.prod_const]
          rfl
    _ = villainFourierScale β ^ Fintype.card (PrimalPlaquettes B) *
          ∑' m : PrimalPlaquettes B → ℤ,
            ∏ p : PrimalPlaquettes B, (g (m p) : ℂ) * phase p (m p) := by
          apply congrArg (fun z : ℂ =>
            villainFourierScale β ^ Fintype.card (PrimalPlaquettes B) * z)
          simpa [villainCircleCharacterSeries, phase, g, villainGaussianCoeff] using hproduct
    _ = villainFourierScale β ^ Fintype.card (PrimalPlaquettes B) *
          ∑' m : PrimalPlaquettes B → ℤ,
            (dualGaussianProduct β m : ℂ) *
              UnitAddTorus.mFourier (fun l => -plaquetteModeDivergence m l) θ := by
          apply congrArg (fun z : ℂ =>
            villainFourierScale β ^ Fintype.card (PrimalPlaquettes B) * z)
          apply tsum_congr
          exact hterm

theorem primalWilsonObservable_eq_mFourier {B : Box 4}
    (θ : PrimalAngleConfig B) (S : Chain 4 B) :
    primalWilsonObservable θ S =
      UnitAddTorus.mFourier (primalSheetLoopFrequency S) θ := by
  have hlinks := circleChainPairing_eq_link_sum (boundary S) θ
  have hfourier := fourier_sum_zsmul (ι := PrimalLinks B) 1
    (fun l => (boundary S) l.1) θ
  unfold primalWilsonObservable
  rw [hlinks]
  simpa [UnitAddTorus.mFourier, primalSheetLoopFrequency] using hfourier

theorem primalVillainWilsonIntegrand_characterExpansion {B : Box 4} (β : ℝ)
    (hβ : 0 < β) (S : Chain 4 B) (θ : PrimalAngleConfig B) :
    (primalVillainDensity β θ : ℂ) * primalWilsonObservable θ S =
      villainFourierScale β ^ Fintype.card (PrimalPlaquettes B) *
        ∑' m : PrimalPlaquettes B → ℤ, dualCharacterTerm β S m θ := by
  rw [primalVillainDensity_characterExpansion β hβ θ,
    primalWilsonObservable_eq_mFourier θ S]
  calc
    _ = villainFourierScale β ^ Fintype.card (PrimalPlaquettes B) *
          ((∑' m : PrimalPlaquettes B → ℤ,
            (dualGaussianProduct β m : ℂ) *
              UnitAddTorus.mFourier (fun l => -plaquetteModeDivergence m l) θ) *
            UnitAddTorus.mFourier (primalSheetLoopFrequency S) θ) := by ring
    _ = villainFourierScale β ^ Fintype.card (PrimalPlaquettes B) *
          ∑' m : PrimalPlaquettes B → ℤ,
            ((dualGaussianProduct β m : ℂ) *
              UnitAddTorus.mFourier (fun l => -plaquetteModeDivergence m l) θ) *
              UnitAddTorus.mFourier (primalSheetLoopFrequency S) θ := by
          congr 1
          rw [← tsum_mul_right]
    _ = villainFourierScale β ^ Fintype.card (PrimalPlaquettes B) *
          ∑' m : PrimalPlaquettes B → ℤ, dualCharacterTerm β S m θ := by
          congr 1
          apply tsum_congr
          intro m
          unfold dualCharacterTerm
          have hm := UnitAddTorus.mFourier_add
            (m := fun l => -plaquetteModeDivergence m l)
            (n := primalSheetLoopFrequency S) (x := θ)
          have hfreq :
              (fun l => -plaquetteModeDivergence m l + primalSheetLoopFrequency S l) =
                (fun l => -plaquetteModeDivergence m l) + primalSheetLoopFrequency S := by
            funext l
            rfl
          calc
            _ = (dualGaussianProduct β m : ℂ) *
                  (UnitAddTorus.mFourier (fun l => -plaquetteModeDivergence m l) θ *
                    UnitAddTorus.mFourier (primalSheetLoopFrequency S) θ) := by ring
            _ = _ := by rw [← hm, hfreq]

theorem primalWilsonNumerator_eq_scale_mul_dualPartition {B : Box 4}
    (β : ℝ) (hβ : 0 < β) (S : Chain 4 B) :
    primalWilsonNumerator β S =
      villainFourierScale β ^ Fintype.card (PrimalPlaquettes B) *
        (dualWilsonPartition β S : ℂ) := by
  calc
    primalWilsonNumerator β S =
        ∫ θ : PrimalAngleConfig B,
          villainFourierScale β ^ Fintype.card (PrimalPlaquettes B) *
            ∑' m : PrimalPlaquettes B → ℤ, dualCharacterTerm β S m θ := by
          unfold primalWilsonNumerator
          apply integral_congr_ae
          filter_upwards with θ
          exact primalVillainWilsonIntegrand_characterExpansion β hβ S θ
    _ = villainFourierScale β ^ Fintype.card (PrimalPlaquettes B) *
          (dualWilsonPartition β S : ℂ) := by
          rw [MeasureTheory.integral_const_mul, dualCharacterSeries_integral_eq β hβ S]

theorem primalVillainPartition_eq_zeroWilsonNumerator {B : Box 4} (β : ℝ) :
    (primalVillainPartition (B := B) β : ℂ) =
      primalWilsonNumerator β (0 : Chain 4 B) := by
  unfold primalVillainPartition primalWilsonNumerator
  rw [← integral_complex_ofReal]
  congr 1
  funext θ
  simp [primalWilsonObservable, circleChainPairing]

theorem primalWilsonExpectation_eq_dualPartition_ratio {B : Box 4}
    (β : ℝ) (hβ : 0 < β) (S : Chain 4 B) :
    primalWilsonExpectation β S =
      ((dualWilsonPartition (B := B) β S : ℂ) /
        (dualWilsonPartition (B := B) β (0 : Chain 4 B) : ℂ)) := by
  have hnum := primalWilsonNumerator_eq_scale_mul_dualPartition β hβ S
  have hden : (primalVillainPartition (B := B) β : ℂ) =
      villainFourierScale β ^ Fintype.card (PrimalPlaquettes B) *
        (dualWilsonPartition (B := B) β (0 : Chain 4 B) : ℂ) := by
    rw [primalVillainPartition_eq_zeroWilsonNumerator (B := B),
      primalWilsonNumerator_eq_scale_mul_dualPartition β hβ]
  have hscale : villainFourierScale β ^ Fintype.card (PrimalPlaquettes B) ≠ 0 := by
    apply pow_ne_zero
    simp [villainFourierScale]
    positivity
  have hdual : (dualWilsonPartition (B := B) β (0 : Chain 4 B) : ℂ) ≠ 0 := by
    exact_mod_cast (dualWilsonPartition_zero_pos (B := B) β hβ).ne'
  unfold primalWilsonExpectation
  rw [hnum, hden]
  have hcancel :
      villainFourierScale β ^ Fintype.card (PrimalPlaquettes B) *
        (dualWilsonPartition β S : ℂ) /
        (villainFourierScale β ^ Fintype.card (PrimalPlaquettes B) *
          (dualWilsonPartition (B := B) β (0 : Chain 4 B) : ℂ)) =
        (dualWilsonPartition β S : ℂ) /
          (dualWilsonPartition (B := B) β (0 : Chain 4 B) : ℂ) := by
    field_simp [hscale, hdual]
  exact hcancel

theorem dualWilsonPartition_nonneg {B : Box 4} (β : ℝ) (_hβ : 0 < β)
    (S : Chain 4 B) : 0 ≤ dualWilsonPartition β S := by
  unfold dualWilsonPartition
  exact tsum_nonneg (fun m => dualWilsonTerm_nonneg (B := B) β S m)

theorem primalWilsonExpectation_im_eq_zero {B : Box 4}
    (β : ℝ) (hβ : 0 < β) (S : Chain 4 B) :
    (primalWilsonExpectation β S).im = 0 := by
  rw [primalWilsonExpectation_eq_dualPartition_ratio β hβ S]
  simp

theorem primalWilsonExpectation_re_nonneg {B : Box 4}
    (β : ℝ) (hβ : 0 < β) (S : Chain 4 B) :
    0 ≤ (primalWilsonExpectation β S).re := by
  rw [primalWilsonExpectation_eq_dualPartition_ratio β hβ S]
  rw [← Complex.ofReal_div]
  simp only [Complex.ofReal_re]
  exact div_nonneg (dualWilsonPartition_nonneg β hβ S)
    (dualWilsonPartition_zero_pos (B := B) β hβ).le


end FroehlichSpencer.FS82.Wilson

end
